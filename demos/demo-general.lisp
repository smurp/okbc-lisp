(in-package :demos)

(defun get-demo-connection (host port user-id password ksl-p)
  #-ksl-okbc (declare (ignore user-id password))
  (if ksl-p
      #+ksl-okbc
      (let ((password (or password "")))
	(let ((sessions
	       (if user-id
		   (ksl-okbc:active-sessions
		    host port user-id password)
		   ;; Connect anonymously
		   nil)))
	  (multiple-value-bind (key session-id)
	    (if user-id
		(if sessions
		    (ksl-okbc:login-user-and-connect-to-session
		     host port user-id password
		     (first (first sessions)))
		    (ksl-okbc:login-user-and-create-session
		     host port user-id password
		     :just-me "Demo2" 100))
		(ksl-okbc:login-user-and-connect-to-session
		 host port :alien "" :anonymous))
	    (establish-connection
	     'ksl-okbc:ksl-network-connection
	     :initargs (list :host host
			     :port port
			     :user-id
			     (string (or user-id :alien))
			     :password password
			     :session-id (string session-id)
			     :key key
			     :kb-library :a)))))
      #-ksl-okbc
      (error "Should never get here!")
      (establish-connection
       'ok-back:simple-network-connection
       :initargs (list :host host :port port))))

(defun prompt-and-read-frame-name (prompt default)
  (format *query-io* "~&~A" prompt)
  (when default (format *query-io* " [default ~A]" default))
  (format *query-io* ": ")
  (let ((line (read-line *query-io*)))
    (if (equal "" line)
	default
	(string-upcase line))))

