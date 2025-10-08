;; server.cl
;;
;;  
;;  An example of using the acl socket code to create a framework
;; for building lisp server applications.
;;
;;
;; Modified 12/98 by Howard Goldberg as simple replacement for ipc package 
;; functions not present in sockets package.  Modified make-socket-server
;; to return process instead of socket. Accepts a user-defined 
;; server-startup-announce-function.  Adds listening socket to property list
;; of process to facilitate cleanup



(defpackage "SERVER"
  (:use "COMMON-LISP" "EXCL")
    (:export "MAKE-SOCKET-SERVER" "KILL-SOCKET-SERVER")) 

(in-package server)

(defvar *server-count* 0)	; used to name servers

(defun make-socket-server (&key (name (format nil "socket server ~d "
					      (incf *server-count*)))
				port 
				function 
				wait 
				(format :text)
				server-startup-announce-function)
  ;;
  ;; create a server process with the given name, listening on the
  ;; given port, running the given function on each connection that
  ;; comes in, and possibly waiting for that function's completion before
  ;; accepting a new connection.
  ;;
  ;; name - a string naming the server process -- if nil, then this 
  ;;	function will create a name.
  ;; port - if nil then an internet domain port number will be chosen
  ;;	    by the operating system.   If a number is given then that
  ;;	    port will be used (or an error will be signalled if it
  ;;	    is already in use).    If port is a string then a unix
  ;;	    domain port will be used.  (this will not work on Windows).
  ;; function - the function to run when a connection is made.  This
  ;;	    function must take one argument which is the stream used
  ;;	    used for reading from and writing to the process that connected
  ;;	    to this socket. 
  ;; wait - if true, then the function will be run in the server process
  ;;	    and thus the server won't accept a new connection until
  ;;	    the function finishes.
  ;; format  - :text (the default) or :binary.   This determes what kind
  ;;	    of data can sent to and read from the socket stream.
  ;;	    
  ;;
  ;;
  ;; The return value is the port number on which the server is
  ;;	listening.
  ;;
  (let ((passive-socket (socket:make-socket
			 :connect :passive
			 :local-port port
			 :address-family 
			 (if* (stringp port)
			    then :file
			  elseif (or (null port)
				     (integerp port))
			    then :internet
			    else (error "illegal value for port: ~s"
					port))
			 :format format
			 )))
    (mp::process-run-function name 
			      #'(lambda ()
				  (start-socket-server passive-socket
						       :function function
						       :wait wait
						       :startup-function server-startup-announce-function)))
    ))

(defun start-socket-server (passive-socket &key function wait startup-function)
  ;; internal function run in the server lightweight process 
  ;; that continually processes the connection.
  ;; This code is careful to ensure that the sockets are 
  ;; properly closed something abnormal happens.
  ;; Additions 1/98 Howard Goldberg
  ;; Associate socket with process to facilitate process and socket cleanup
  ;; Execute user-supplied startup function given a valid socket and new process
  (unwind-protect
      (setf (getf (mp:process-property-list sys:*current-process*) 'socket) passive-socket)
      (funcall startup-function (socket:local-port passive-socket))
      (loop (let ((connection (socket:accept-connection passive-socket)))
	      (if* wait
		 then (unwind-protect
			  (funcall function connection)
			(errorset (close connection) nil))
		 else (mp:process-run-function
		       (format nil "server run ~d" (incf *server-count*))
		       #'(lambda (con)
			   (unwind-protect
			       (funcall function con)
			     (errorset (close con) nil)))
		       connection))))
      (errorset (close passive-socket) nil)))

(defun kill-socket-server (process)
  ;; given a process, kill the process and close the socket associated with the process
  ;; needs error-checking
  (progn
    (close (getf (mp:process-property-list process) 'socket))
    (mp:process-kill process)))




