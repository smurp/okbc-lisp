(in-package :ok-kernel)

(defconstant *string-char-element-type*
  #+(and Lucid (not dbcs)) 'string-char
  #+(and Lucid dbcs) 'base-character
  #+MCL 'base-character
  #+EXCL 'character
  #+Harlequin-Common-Lisp 'base-char
  #-(or Lucid MCL EXCL Harlequin-Common-Lisp)
  (unimplemented "String char type"))

(eval-when (compile load eval)
(defconstant *list-type-code* 0)
(defconstant *symbol-type-code* 1)
(defconstant *string-type-code* 2)
(defconstant *integer-type-code* 3)
(defconstant *float-type-code* 4)
(defconstant *true-type-code* 5)
(defconstant *false-type-code* 6)
(defconstant *other-type-code* 7)
(defconstant *kb-type-code* 8)
(defconstant *procedure-type-code* 9)
(defconstant *frame-handle-type-code* 10)
(defconstant *remote-value-type-code* 11)
(defconstant *enumerator-type-code* 12)
);;; eval-when

(defvar *quasi-package-table* (make-hash-table :test #'equal))
(defvar *frame-handle-table-hash-table-initial-size* 10000)
(defvar *frame-handle-key-to-frame-handle-table*
  (tries:new-root-hybrid-trie :frame-handle-key-to-frame-handle-table nil))
(defvar *frame-object-to-frame-handle-table*
  (tries:new-root-hybrid-trie :frame-object-to-frame-handle-table nil))
(defvar *frame-handle-to-frame-handle-key-table*
  (make-hash-table :test #'eql
		   :size *frame-handle-table-hash-table-initial-size*))

(defmacro ok-utils:fast-terpri (stream)
  "Like <code>terpri</code>, but in some implementations will use faster,
   lower-level IO primitives."
  `(fast-write-char #\newline ,stream))

(defmacro ok-utils:fast-write-fixnum
    #+Lucid (number &optional (stream nil))
    #-Lucid (number stream)
    "Writes a fixnum to the stream.  In some implementations will use fast,
     lower-level IO primitives."
  #+Lucid
  (if stream
      `(let ((system::*print-output* stream))
	(lucid::output-integer ,number))
      `(lucid::output-integer ,number))
  #-Lucid `(prin1 ,number ,stream))

(defun reset-frame-handle-tables ()
  (setq *frame-handle-key-to-frame-handle-table*
    (tries:new-root-hybrid-trie :frame-handle-key-to-frame-handle-table nil))
  (setq *frame-object-to-frame-handle-table*
    (tries:new-root-hybrid-trie :frame-object-to-frame-handle-table nil))
  (setq *frame-handle-to-frame-handle-key-table*
    (make-hash-table :test #'eql
		     :size *frame-handle-table-hash-table-initial-size*)))

(defvar *frame-handle-id-counter* 0)

(defvar *remote-value-key-to-remote-value-table*
  (make-hash-table :test #'equal))
(defvar *remote-value-to-remote-value-key-table*
  (make-hash-table :test #'eql))
(defvar *remote-value-id-counter* 0)

(defun reset-remote-value-tables ()
  (setq *remote-value-key-to-remote-value-table*
    (make-hash-table :test #'equal))
  (setq *remote-value-to-remote-value-key-table*
    (make-hash-table :test #'eql))
  (setq *remote-value-id-counter* 0))

(defun reset-handle-tables ()
  (reset-frame-handle-tables)
  (reset-remote-value-tables))

(defvar *enumerator-id-to-enumerator-table*
  (make-hash-table :test #'eql))
(defvar *enumerator-id-counter* nil)

(defparameter *default-network-okbc-query-format* :portable)
(defparameter *default-network-okbc-reply-format* :portable)
;; Note that transport versions :c and :b are the same, it's just that
;; the version number got bumped for OKBC 2.0.
(defparameter *default-network-okbc-transport-version* :c)
(defparameter *default-network-okbc-kb-library* :a)

(defokbcclass ok-back:abstract-network-connection (connection)
  ((host :accessor host :initarg :host)
   (port :accessor port :initarg :port)
   (kb-library :accessor kb-library :initform *default-network-okbc-kb-library*
	       :initarg :kb-library)
   (net-stream :accessor net-stream :initarg :net-stream :initform :ephemeral)
   (socket :accessor socket :initform nil :initarg :socket)
   (request-tag :accessor request-tag :initform 0))
  (:documentation "The abstract superclass of all OKBC network connections.
   If you plan to define your own class of network connection, you <i>must</i>
   make it a subclass of this class."))

(defdoc ok-back:host (function)
  "An accessor on network connections that returns the host for the
   connection.")

(defdoc ok-back:port (function)
  "An accessor on network connections that returns the port for the
   connection.")

(defokbcclass ok-back:simple-network-connection
    (ok-back:abstract-network-connection)
  ()
  (:documentation "The class of connection used to implement simple OKBC
   network connections.  Communication with a server using this connection
   class is single-threaded and unauthenticated.  <p>

   A server that will accept connections of this connection type is started
   using <code>ok-utils:nokbc-server</code>"))


(defmethod key-for-frame-handle-uniquification ((thing t) (kb t)) thing)

(defun allocate-frame-handle-id ()
  (ok-utils:without-scheduling
   (incf *frame-handle-id-counter*)
   *frame-handle-id-counter*))

(defun make-handle-key (id kb-id)
  (cons id kb-id))

(defun safely-make-frame-handle (id kb-id thing)
  (assert (or (integerp id) (and (keywordp id) (equal -1 kb-id))))
  (assert (integerp kb-id))
  (make-frame-handle 
   :id id
   :kb-id kb-id
   :thing thing))

(defun ok-back:create-frame-handle (for-thing kb &optional (unique-key nil)
					      (object-trie-node nil))
  "Internal protocol used to create FRS-independent frame handles.
   <code>For-thing</code> is the object being represented by the frame
   handle in <code>kb</code>.  <code>Unique-key</code> is a key used to
   identify the thing, usually itself.  <code>Object-trie-node</code>, if
   supplied, is a node in a trie in an object to frame handle mapping table
   for the thing.<P>

   This is deep internal protocol.  Back end implementors should almost
   certainly <i>not</i> call this function, but should call
   <code>okbc:frs-independent-frame-handle</code> instead."
  (declare (special *okbc-standard-names*))
  (if (and (keywordp for-thing)
	   (member for-thing *okbc-standard-names*))
      (let ((id for-thing))
	(let ((key (make-handle-key id -1)))
	  ;; This is actually a find-or-create for canonical frames
	  ;; which are all mapped into the same (non-existent) KB with ID -1
	  (multiple-value-bind (result found-p trie-node)
	      (tries:get-hybrid-trie-returning-node
	       key *frame-handle-key-to-frame-handle-table*)
	    (if found-p
		result
		(let ((new (safely-make-frame-handle 
			    id -1 (or for-thing *undefined-value*))))
		  (initialize-fast-hash-key new)
		  (multiple-value-bind (result found-p object-trie-node)
		      (if object-trie-node
			  (values nil nil object-trie-node)
			  (tries:get-hybrid-trie-returning-node
			   (or unique-key new)
			   *frame-object-to-frame-handle-table*))
		    (declare (ignore result found-p))
		    (set-hybrid-trie-value object-trie-node new))
		  (set-hybrid-trie-value trie-node new)
		  (setf (gethash new *frame-handle-to-frame-handle-key-table*)
			key)
		  new)))))
      (let ((id (allocate-frame-handle-id)))
	(let ((key (make-handle-key id (unique-id kb))))
	  (let ((new (safely-make-frame-handle 
		      id (unique-id kb)
		      (or for-thing *undefined-value*))))
	    (initialize-fast-hash-key new)
	    (setf (tries:get-hybrid-trie
		   key *frame-handle-key-to-frame-handle-table*)
		  new)
	    (multiple-value-bind (result found-p object-trie-node)
		(if object-trie-node
		    (values nil nil object-trie-node)
		    (tries:get-hybrid-trie-returning-node
		     (or unique-key new)
		     *frame-object-to-frame-handle-table*))
	      (declare (ignore result found-p))
	      (set-hybrid-trie-value object-trie-node new))
	    (setf (gethash new *frame-handle-to-frame-handle-key-table*) key)
	    new)))))

(defun ok-back:print-frame-handle (frame-handle kb stream macro-character)
  "Writes a reader macro call to the <code>stream</code> representing the
   <code>frame-handle</code> with respect to the <code>kb</code>.
   <code>macro-character</code> is the macro character to use.  The final
   result will be something like <code>#$(42 7)</code>."
  (flet ((print-fact (fact stream)
	   (if (#-Allegro fixnump #+allegro excl:fixnump fact)
	       (fast-write-fixnum fact stream)
	       (prin1 fact stream))))
    (fast-write-string "#" stream)
    (fast-write-char macro-character stream)
    (fast-write-string "(" stream)
    (print-fact (ok-back:frame-handle-id frame-handle) stream)
    (fast-write-string " " stream)
    (if (eq (unique-id kb) (ok-back:frame-handle-kb-id frame-handle))
	(fast-write-string "!" stream)
	(print-fact (ok-back:frame-handle-kb-id frame-handle) stream))
    (fast-write-string ")" stream)))

(defvar ok-back:*default-kb*)

(setf (documentation 'ok-back:*default-kb* 'variable)
      "If bound, this is the default KB into which to intern frame handles when
       using the <code>ok-back:frame-handle-reader</code>")

(defun ok-back:frame-handle-reader (stream char arg)
  "A reader function that can be put into a reatable to read simple
   <code>frame-handle</code> references from a stream.  The
   <code>frame-handle</code> references should have been printed using
   <code>print-frame-handle</code>."
  ;; Used in reader macros to read frame handles of the form #$(id kb-id).
  (declare (ignore char arg))
  (let ((spec (read stream t nil t)))
    (assert (and (consp spec) (= (length spec) 2)) ()
	    "Illegal frame handle spec.")
    (destructuring-bind (id kb-id) spec
      (if (and (symbolp kb-id) (string= (symbol-name kb-id) "!"))
	  (if (boundp '*default-kb*)
	      (setq kb-id (unique-id (symbol-value '*default-kb*)))
	      (error "No default kb found!")))
      (assert (integerp kb-id)) ;; should ideally be a fixnum
      (let ((key (make-handle-key id kb-id)))
	(multiple-value-bind (result found-p trie-node)
	    (tries:get-hybrid-trie-returning-node
	     key *frame-handle-key-to-frame-handle-table*)
	  (if found-p
	      result
	      (let ((new (safely-make-frame-handle
			  id kb-id *undefined-value*)))
		(initialize-fast-hash-key new)
		(tries:set-hybrid-trie-value trie-node new)
		(multiple-value-bind (result found-p object-trie-node)
		    (tries:get-hybrid-trie-returning-node
		     new *frame-object-to-frame-handle-table*)
		  (declare (ignore result found-p))
		  (tries:set-hybrid-trie-value object-trie-node new))
		(setf (gethash new *frame-handle-to-frame-handle-key-table*)
		      key)
		new)))))))

(defun ok-back:find-or-create-frame-handle
    (for-thing frame kb transmit-handles-p)
  "Finds or creates an FRS-independent frame handle for <code>for-thing</code>.
   This is deep internal protocol.  Back end implementors should almost
   certainly <i>not</i> call this function, but should call
   <code>okbc:frs-independent-frame-handle</code> instead."
  (if (eq for-thing frame)
      (let ((unique-key
	     (key-for-frame-handle-uniquification for-thing kb)))
	(if (typep unique-key 'frame-handle)
	    unique-key
	    (multiple-value-bind (existing found-p object-trie-node)
		(tries:get-hybrid-trie-returning-node
		 unique-key *frame-object-to-frame-handle-table*)
	      (or (and found-p existing)
		  (create-frame-handle
		   for-thing kb unique-key object-trie-node)))))
      (deframify frame kb transmit-handles-p)))

(defmethod deframify ((thing cons) kb transmit-handles-p)
  (let ((result nil)
	(tail nil))
    (loop with remainder = thing
	  for x = (pop remainder)
	  for this = (cons (deframify x kb transmit-handles-p) nil)
	  do (if result
		 (progn (setf (rest (the cons tail)) this)
			(setq tail (rest tail)))
		 (progn (setq result this)
			(setq tail result)))
	  when (not remainder) return nil
	  when (not (consp remainder))
	  do (setf (rest (the cons tail))
		   (deframify remainder kb transmit-handles-p))
	     (return nil))
    result))

(defmethod deframify ((thing kb) (kb t) (transmit-handles-p t))
  thing)

(defmethod deframify ((thing structure-kb) (kb t) (transmit-handles-p t))
  thing)

(defmethod deframify (thing kb transmit-handles-p)
  (cond ((ok-back:coercible-to-frame-p-internal thing kb nil)
	 (let ((name (ok-back:get-frame-name-internal thing kb nil)))
	   (if (eq name thing)
	       name
	       (deframify name kb transmit-handles-p))))
	(t thing)))

(defmethod deframify ((thing (eql nil)) (kb t) (transmit-handles-p t))
  nil)

;==============================================================================

;;; Socket connection stuff....

#+Lucid
(let ((connect.o-path
       (if (boundp 'user::*os-native-binary-file-type*)
	   #-KSL
	   (make-pathname :defaults (current-source-file)
			  :name "connect"
			  :type user::*os-native-binary-file-type*)
	   #+KSL
	   (user::cms-pathname '("okbc" "lisp") "okbc-connect"
			       user::*os-native-binary-file-type*)
	   (make-pathname :defaults (current-source-file)
			  :name "connect"
			  :type "o"))))
  (load-foreign-files (list connect.o-path)))

#+Lucid
(def-foreign-function (connect-socket
		       (:name #-No-Underscore-In-Foreign-Functions
			      "_ConnectSocket"
			      #+No-Underscore-In-Foreign-Functions
			      "ConnectSocket")
		       (:language :c)
		       (:return-type :fixnum))
    (host :simple-string)
  (port :fixnum))

#+Lucid
(def-foreign-function (disconnect-socket
		       (:name #-No-Underscore-In-Foreign-Functions "_close"
			      #+No-Underscore-In-Foreign-Functions  "close")
		       (:language :c))
    (socket :fixnum))


(defvar *max-connection-retry-attempts* 5)
(defvar *connection-retry-sleep-period-in-seconds* 2)


#+Lucid
(defmacro ok-utils:with-connection-to-socket ((stream host port) &body body)
  `(let ((socket nil))
    (unwind-protect
	 (progn
	   ;;; This is a bit of a hack sometimes for no reason that I can
	   ;;; figure out we sometimes don't get a connection, but if
	   ;;; we try again we do.  I've put in this loop to retry (by default)
	   ;;; five times over a period of 10 seconds and barf out after that.
	   (loop for count from 1 to *max-connection-retry-attempts*
		 do (setq socket (connect-socket ,host ,port))
		 (when (not (equal -1 socket)) (return socket))
		 #+Lucid
		 (format lcl:*initial-io*
			 "~&;;; Connection to ~A:~D failed on try ~D"
			 ,host ,port count)
		 (sleep *connection-retry-sleep-period-in-seconds*))
	   (when (equal -1 socket)
	     (error 'okbc:network-connection-error :host ,host :port ,port))
	   (with-open-stream
	       (,stream (make-lisp-stream :input-handle socket
					  :output-handle socket
					  :auto-force NIL))
	     ,@body))
      (when (and socket (not (equal -1 socket))) (disconnect-socket socket)))))

#+MCL
(defvar *mcl-command-timeout* 255)

#+MCL
(defmacro ok-utils:with-connection-to-socket ((stream host port) &body body)
  `(with-open-stream (,stream (ccl::open-tcp-stream ,host ,port
			       :commandtimeout *mcl-command-timeout*))
     ,@body))

#+(and Allegro (not (and allegro-version>= (version>= 5))))
(defmacro ok-utils:with-connection-to-socket ((stream host port) &body body)
  `(with-open-stream (,stream (ipc:open-network-stream
			       :host ,host :port ,port))
     ,@body))

#+(and Allegro allegro-version>= (version>= 5))
(defmacro ok-utils:with-connection-to-socket ((stream host port) &body body)
  `(with-open-stream (,stream (socket:make-socket 
			       :remote-host ,host :remote-port ,port))
     ,@body))

#+Harlequin-Common-Lisp
(defmacro ok-utils:with-connection-to-socket ((stream host port) &body body)
  `(with-open-stream (,stream (comm:open-tcp-stream ,host ,port :direction :io
			       :element-type 'base-char))
     ,@body))

#-(or Lucid MCL Allegro Harlequin-Common-Lisp)
(progn (cerror "Go ahead, anyway" "Please define with-connection-to-socket")
       (defmacro ok-utils:with-connection-to-socket
	   ((stream host port) &body body)
	 `(let ((,stream nil)
		(,host nil)
		(,port nil))
	   ,@body)))

(defdoc ok-utils:with-connection-to-socket (function)
  "Executes <code>body</code> with <code>stream</code> bound to a TCP
   stream connected to a socket identified by <code>host</code> and
   <code>port</code>.")

(defun make-quote-mask (args)
  (loop for arg in args collect (if (consp arg) (list t t) t)))

