(in-package :ok-kernel)

#+Lucid
(def-foreign-function
    (ok-utils:getpid (:return-type :signed-32bit)
		     (:name #-No-Underscore-In-Foreign-Functions
			    "_getpid"
			    #+No-Underscore-In-Foreign-Functions
			    "getpid")))

#+Lucid
(load-foreign-files nil)


;;;for acl5.0, use getpid from excl for cross-platform compatibility
#+(and Allegro (not (and allegro-version>= (version>= 5))))
(ignore-errors (load "" :unreferenced-lib-names '("_getpid")))
#+(and Allegro (not (and allegro-version>= (version>= 5))))
(ff:defforeign 'ok-utils:getpid :return-type :fixnum :arguments nil)
#+(and Allegro allegro-version>= (version>= 5))
(defun ok-utils:getpid () (excl::getpid))

#+Harlequin-Common-Lisp
(fli:define-foreign-function (ok-utils:getpid "getpid")
    ()
  :result-type :long
  :language :ansi-c)

#-(or Lucid Allegro Harlequin-Common-Lisp)
(progn (cerror "Go ahead, anyway" "Need to implement ok-utils:getpid")
       (defun ok-utils:getpid () 0))

(defdoc ok-utils:getpid (function)
  "Returns the UNIX process ID of the process in which the current Lisp
   is running.")

(defvar *image-unique-tag* nil)

(defun image-unique-tag (&optional (force-p nil))
  (or (and (not force-p) *image-unique-tag*)
      (setq *image-unique-tag*
	    (sxhash (format nil "~A-~A"
			    (get-universal-time) ;; maybe get something better
			    (ok-utils:getpid))))))

(defun start-point-for-kb-ids ()
  ;; Compute a fixnum that's a good start point for KB IDs.  This should
  ;; give us a full year before wraparound, and a few extra bits that are
  ;; unlikely to clash.
  (flet ((bits-in (n) (ceiling (log n 2))))
    (let ((pid (sxhash (ok-utils:getpid)));; jumble bits
	  (fixnum-length (bits-in most-positive-fixnum))
	  (year-length (bits-in (* 365 24 3600)))
	  (time (get-universal-time)))
      (let ((mask (ash pid (- fixnum-length year-length))))
	;; Make sure it's still a fixnum
	(let ((masked (coerce (logand (logxor mask time) most-positive-fixnum)
			      'fixnum)))
	  masked)))))

(defun make-server-kb-id-start-point ()
  ;; Computes an offset to add to KB IDs when passed over the net.  A bunch
  ;; of random bits that are masked off at the top end so that adding it
  ;; to the KB ID start point shouldn't push us into the land of bignums.
  (let ((start (start-point-for-kb-ids)))
    (flet ((bits-in (n) (ceiling (log n 2))))
      (logand (logxor (random start) start)
	      (- (expt 2 (- (bits-in most-positive-fixnum) 2)) 1)))))

(defvar *server-unique-kb-id-offset* (make-server-kb-id-start-point))

(defvar *network-okbc-kbs* nil)
(pushnew 'network-kb *abstract-kb-class-names*)

(defvar ok-back:*print-pretty-frame-handles* nil
  "A flag used to tell implementors of ok-back:print-abstract-handle-for-kb
   to print frame handles as prettily as possible.")

(defvar *inside-handle-printer-p* nil)

(defmethod print-object ((thing abstract-handle) (stream t))
  (if (and (okbc:current-kb)
	   (not *inside-handle-printer-p*)
	   (not (typep (okbc:current-kb) 'ok-back:network-kb))
	   (not (typep (okbc:current-kb) 'ok-back:network-structure-kb))
	   (ok-back:coercible-to-frame-p-internal thing (okbc:current-kb)
						  nil))
      (let ((*inside-handle-printer-p* t)
	    (ok-cache:*allow-okbc-caching-p* nil)
	    #+lucid (liquid::*trace-suppress* t))
	(ok-back:print-abstract-handle-for-kb thing (okbc:current-kb) stream))
      (print-unreadable-object
       (thing stream :type t :identity t)
       (let (#+lucid (liquid::*trace-suppress* t))
	 (cond ((or (eq (abstract-handle-thing thing) *undefined-value*)
		    (eq (abstract-handle-thing thing) thing))
		(format stream "~S:~S" (abstract-handle-kb-id thing)
			(abstract-handle-id thing)))
	       (t (format stream "Representing ~S"
		    (abstract-handle-thing thing))))))))

(defokbcgeneric ok-back:print-abstract-handle-for-kb (thing kb stream)
  (:documentation
   "A print-method extension hook that causes FRS-independent frame handles
    to be printed out in a manner appropriate to the KB in question.  This is
    only called if the frame handle is coercible-to-frame-p in the KB."))

(defvar *frames-being-printed* nil)

(defmethod ok-back:print-abstract-handle-for-kb
 ((thing abstract-handle) (kb t) (stream t))
 (if (member thing *frames-being-printed*)
     (format stream "[.... recursive ....]")
     (let ((*frames-being-printed* (cons thing *frames-being-printed*)))
       (cond ((or (eq (abstract-handle-thing thing) *undefined-value*)
		  (eq (abstract-handle-thing thing) thing))
	      (print-unreadable-object
	       (thing stream :type t :identity t)
	       (let ((pretty-name
		      (ignore-errors
			(ok-back:get-frame-pretty-name-internal
			 thing (okbc:current-kb) nil))))
		 (if (or (search "-HANDLE " pretty-name
				 :test #'char=)
			 (search " Representing " pretty-name
				 :test #'char=))
		     (format stream "~S:~S" (abstract-handle-kb-id thing)
		      (abstract-handle-id thing))
		     (format stream "Representing ~S in ~A"
		       pretty-name (name (okbc:current-kb)))))))
	     ((not (abstract-handle-thing thing))
	      (print-unreadable-object
	       (thing stream :type t :identity t)
	       (format stream "Representing ~S in ~A"
		 (ok-back:get-frame-pretty-name-internal
		  thing (okbc:current-kb) nil)
		 (name (okbc:current-kb)))))
	     (t (print-unreadable-object
		 (thing stream :type t :identity t)
		 (format stream "Representing ~S"
		   (abstract-handle-thing thing))))))))

(defmethod ok-back:print-abstract-handle-for-kb
 ((thing frame-handle) (kb t) (stream t))
 (if (member thing *frames-being-printed*)
     (format stream "[.... recursive ....]")
     (let ((*frames-being-printed* (cons thing *frames-being-printed*)))
       (cond ((or (eq (abstract-handle-thing thing) *undefined-value*)
		  (eq (abstract-handle-thing thing) thing))
	      (print-unreadable-object
	       (thing stream :type t :identity t)
	       (let ((pretty-name
		      (ignore-errors
			(ok-back:get-frame-pretty-name-internal
			 thing (okbc:current-kb) nil))))
		 (if (or (search "-HANDLE " pretty-name
				 :test #'char=)
			 (search " Representing " pretty-name
				 :test #'char=))
		     (let ((name? (getf (frame-handle-plist thing)
					:allocated-name)))
		       (if name?
			   (let ((type? (getf (frame-handle-plist thing)
					      :allocated-type)))
			     (if type?
				 (format stream "Representing ~S, allocated ~
                                                 as a ~A in ~A"
				   name? type? (name (okbc:current-kb)))
				 (format stream "Representing ~S in ~A"
				   name? (name (okbc:current-kb)))))
			   (format stream "~S:~S" (abstract-handle-kb-id thing)
				   (abstract-handle-id thing))))
		     (format stream "Representing ~S in ~A"
		       pretty-name (name (okbc:current-kb)))))))
	     ((not (abstract-handle-thing thing))
	      (print-unreadable-object
	       (thing stream :type t :identity t)
	       (format stream "Representing ~S in ~A"
		 (ok-back:get-frame-pretty-name-internal
		  thing (okbc:current-kb) nil)
		 (name (okbc:current-kb)))))
	     (t (print-unreadable-object
		 (thing stream :type t :identity t)
		 (format stream "Representing ~S"
		   (abstract-handle-thing thing))))))))

#-(or Lucid MCL Allegro Harlequin-Common-Lisp)
(cerror "Go ahead, anyway" "Implement fast-write-char")

#+(or Allegro MCL Harlequin-Common-Lisp)
(defun ok-utils:fast-write-char (char stream)
  (write-char char stream))

(defdoc fast-write-char (function)
  "Like <code>write-char</code>, but in some implementations will use
   faster, lower-level IO primitives.")

#+(or Allegro MCL Harlequin-Common-Lisp)
(defun ok-utils:fast-write-string (string stream &key (start 0) (end nil))
  (write-string string stream :start start :end end))

(defdoc fast-write-string (function)
  "Like <code>write-string</code>, but in some implementations will
   use faster,lower-level IO primitives.")

#-(or MCL Lucid Allegro Harlequin-Common-Lisp)
(error "Define fast-write-string")
			  
#-(or Lucid MCL Allegro Harlequin-Common-Lisp)
(cerror "Go ahead, anyway" "Implement fast-read-char")

#+(or Allegro MCL Harlequin-Common-Lisp)
(defun fast-read-char (stream &optional (eof-error-p t) eof-value recursive-p)
  (read-char stream eof-error-p eof-value recursive-p))

(defdoc fast-read-char (function)
  "Like <code>read-char</code>, but in some implementations will use
   faster, lower-level IO primitives.")


#-Lucid
(defun ok-utils:underlying-stream (s type)
  (declare (ignore type))
  s)

(defdoc underlying-stream (function)
  "Given a <code>stream</code>and a <code>type</code>, which is either
   <code>:input</code>, or <code>:output</code>, returns the most
   primitive underlying stream that can be found.  This is used,
   for example, to extract the underlying output stream from a
   bidirectional TCP stream.  It is useful because in some implementations
   the optimized IO primitives work much faster on primitive streams.")

(defun ok-utils:fast-read-line
    (stream &optional (eof-error-p t) (eof-value nil))
  "Like <code>read-line</code>, but in some implementations will use faster,
   lower-level IO primitives."
  (let ((str (underlying-stream stream :input))
	(count 0)
	(eof-p nil))
    (let ((chars (loop for char = (fast-read-char str eof-error-p eof-value)
		       when (eq char eof-value)
		       do (setq eof-p t)
		       until (or (char= char #\newline)
				 (eq eof-value char))
		       collect char
		       do (incf (the fixnum count)))))
      (if (and eof-p (zerop count))
	  eof-value
	  (let ((string
		 (make-array (the fixnum count) :element-type
			     *string-char-element-type*)))
	    (loop for char in chars
		  for index fixnum from 0
		  do (setf (schar string index) char))
	    string)))))

;;; The coding substrate.

(defparameter *current-transport-version* :c)

(defokbcgeneric ok-back:handles-in-tree-p (form kb)
  (:documentation "Is true if there are any frame handles in the form with
   respect to the KB."))

(defmethod handles-in-tree-p ((tree t) (kb t))
  nil)

(defmethod handles-in-tree-p ((tree cons) (kb t))
  (or (handles-in-tree-p (first tree) kb) (handles-in-tree-p (rest tree) kb)))

(defmethod handles-in-tree-p ((tree abstract-handle) (kb t))
  (not (eq tree (abstract-handle-thing tree))))

(defun allocate-remote-value-id ()
  (incf *remote-value-id-counter*)
  *remote-value-id-counter*)

(defun allocate-enumerator-id ()
  (when (not *enumerator-id-counter*)
    (setq *enumerator-id-counter* (image-unique-tag)))
  (without-scheduling (incf *enumerator-id-counter*))
  *enumerator-id-counter*)

(defvar *trace-data-encoding* nil)

(defokbcgeneric encode-data-structure-to-stream (thing stream key)
  (:documentation "Given a stream along which an OKBC client or server is to
   serialise data, encodes <code>thing</code>, some random sexpression into
   a serialised representation.  This function is used by the transport layer
   of the network model to transmit data.  It takes care of any necessary
   interning of remote values, substitution of frame objects for remote frame
   handles, and mapping of KBs into abstract KB representations.<p>

  This function can also be used (in conjunction with
  <code>decode-data-structure-from-stream</code>) as a means of saving
  (and loading) KB content to files and streams.<P>

  At present, the only supported value for <code>key</code> is
  <code>:portable</code>."))

(defmethod encode-data-structure-to-stream (thing stream (key (eql :portable)))
  (let ((stream (if *trace-data-encoding*
		    (make-broadcast-stream stream *trace-output*)
		    stream)))
    (when *trace-data-encoding*
      (format *trace-output* "~%;;; Encoding ~S~%" thing))
    (with-standard-io-syntax
	(let ((*print-readably* nil))
	  (encode-data-structure-to-stream-internal thing stream)))
    thing))

(defmethod encode-data-structure-to-stream (thing stream (key (eql :lisp)))
  (with-standard-io-syntax
      (let ((#-(or Allegro Harlequin-Common-Lisp) *print-structure*
	       #+Allegro excl:*print-structure*
	       #+Harlequin-Common-Lisp hcl:*print-structure*
	       t));; handle procedures
	(prin1 thing stream))
    (fast-terpri stream))
  thing)

(defmethod encode-data-structure-to-stream-internal ((thing cons) stream)
  (let (#+Lucid (system::*print-output* stream))
    (fast-write-fixnum *list-type-code* #-Lucid stream)
    (fast-terpri stream)
    (fast-write-fixnum (length (the cons thing)) #-Lucid stream)
    (fast-terpri stream)
    (loop with rest = thing
	  when (not rest) return nil
	  do (if (consp rest)
		 (progn (encode-data-structure-to-stream-internal
			 (first rest) stream)
			(pop rest))
		 (generic-error "Cannot encode dotted lists like ~S"
				    thing)))))

(defmethod encode-data-structure-to-stream-internal ((thing kb) stream)
  (let (#+Lucid (system::*print-output* stream))
    (fast-write-fixnum *kb-type-code* #-Lucid stream)
    (fast-terpri stream)
    (encode-data-structure-to-stream-internal
     (if (and (slot-boundp thing 'name) (name thing))
	 (name thing)
	 :prototype)
     stream)
    (let ((abstract-name (abstract-kb-class-name-from-kb thing)))
      (if abstract-name
	  (encode-data-structure-to-stream-internal abstract-name stream)
	  (progn (cerror "Go ahead anyway" "No abstract class found for ~S"
			 thing)
		 (encode-data-structure-to-stream-internal
		  'ok-back:abstract-kb-kb stream))))))

(defmethod encode-data-structure-to-stream-internal
    ((thing structure-kb) stream)
  (let (#+Lucid (system::*print-output* stream))
    (fast-write-fixnum *kb-type-code* #-Lucid stream)
    (fast-terpri stream)
    (encode-data-structure-to-stream-internal
     (or (and (name thing) (not (equal 0 (name thing)))) :prototype)
     stream)
    (let ((abstract-name (abstract-kb-class-name-from-kb thing)))
      (if abstract-name
	  (encode-data-structure-to-stream-internal abstract-name stream)
	  (progn (cerror "Go ahead anyway" "No abstract class found for ~S"
			 thing)
		 (encode-data-structure-to-stream-internal
		  'ok-back:abstract-kb-kb stream))))))

(defmethod encode-data-structure-to-stream-internal ((thing integer) stream)
  (let ((*print-escape* nil)
	(*print-readably* nil)
	#+Lucid (system::*print-output* stream))
    (let ((string (princ-to-string thing)))
      (fast-write-fixnum *integer-type-code* #-Lucid stream)
      (fast-terpri stream)
      (fast-write-fixnum (length string) #-Lucid stream)
      (fast-terpri stream)
      (fast-write-string string stream)
      (fast-terpri stream))))

(defmethod encode-data-structure-to-stream-internal ((thing float) stream)
  (let ((*print-escape* nil)
	(*print-readably* nil)
	#+Lucid (system::*print-output* stream))
    (let ((string (princ-to-string thing)))
      (fast-write-fixnum *float-type-code* #-Lucid stream)
      (fast-terpri stream)
      (fast-write-fixnum (length string) #-Lucid stream)
      (fast-terpri stream)
      (fast-write-string string stream)
      (fast-terpri stream))))

(defmethod encode-data-structure-to-stream-internal ((thing symbol) stream)
  (let ((*print-escape* nil)
	(*print-readably* nil)
	#+Lucid (system::*print-output* stream))
    (fast-write-fixnum *symbol-type-code* #-Lucid stream)
    (fast-terpri stream)
    (let ((pack (symbol-package thing)))
      (cond (pack (fast-write-fixnum (length (package-name pack))
				     #-Lucid stream)
		  (fast-terpri stream)
		  (fast-write-string (package-name pack) stream)
		  (fast-terpri stream))
	    (t (fast-write-fixnum 3 #-Lucid stream)
	       (fast-terpri stream)
	       (fast-write-string "NIL" stream)
	       (fast-terpri stream))))
    (fast-write-fixnum (length (the simple-string (symbol-name thing)))
		       #-Lucid stream)
    (fast-terpri stream)
    (fast-write-string (symbol-name thing) stream)
    (fast-terpri stream)))

;; Make quasi-symbols look just like symbols to the transport layer!
(defmethod encode-data-structure-to-stream-internal
      ((thing quasi-symbol) stream)
  (let ((*print-escape* nil)
	(*print-readably* nil)
	#+Lucid (system::*print-output* stream))
    (fast-write-fixnum *symbol-type-code* #-Lucid stream)
    (fast-terpri stream)
    (let ((pack (quasi-symbol-package thing)))
      ;; Note:  Quasi-symbols are always interned.
      (fast-write-fixnum (length (name pack)) #-Lucid stream)
      (fast-terpri stream)
      (fast-write-string (name pack) stream)
      (fast-terpri stream))
    (fast-write-fixnum (length (the simple-string (name thing)))
		       #-Lucid stream)
    (fast-terpri stream)
    (fast-write-string (name thing) stream)
    (fast-terpri stream)))

(defmethod encode-data-structure-to-stream-internal ((string string) stream)
  (let ((*print-escape* nil)
	(*print-readably* nil)
	#+Lucid (system::*print-output* stream))
    (fast-write-fixnum *string-type-code* #-Lucid stream)
    (fast-terpri stream)
    (fast-write-fixnum (length string) #-Lucid stream)
    (fast-terpri stream)
    (fast-write-string string stream)
    (fast-terpri stream)))

(defmethod encode-data-structure-to-stream-internal ((thing (eql nil)) stream)
  (let ((*print-escape* nil)
	(*print-readably* nil)
	#+Lucid (system::*print-output* stream))
    (fast-write-fixnum *false-type-code* #-Lucid stream)
    (fast-terpri stream)))

(defmethod encode-data-structure-to-stream-internal ((thing (eql t)) stream)
  (let ((*print-escape* nil)
	(*print-readably* nil)
	#+Lucid (system::*print-output* stream))
    (fast-write-fixnum *true-type-code* #-Lucid stream)
    (fast-terpri stream)))

(defmethod encode-data-structure-to-stream-internal
    ((thing procedure) stream)
  (let ((*print-escape* nil)
	(*print-readably* nil)
	#+Lucid (system::*print-output* stream))
    (fast-write-fixnum *procedure-type-code* #-Lucid stream)
    (fast-terpri stream)
    (when (string>= *current-transport-version* :b)
      (encode-data-structure-to-stream-internal
       (procedure-name thing) stream))
    (cond ((procedure-as-sexpressions-p thing)
	   (encode-data-structure-to-stream-internal
	    (procedure-arguments thing) stream)
	   (encode-data-structure-to-stream-internal
	    (procedure-expression thing) stream)
	   (encode-data-structure-to-stream-internal
	    (procedure-environment thing) stream))
	  (t
	   (encode-data-structure-to-stream-internal
	    (or (procedure-arguments thing)
		(procedure-arguments-string thing))
	    stream)
	   (encode-data-structure-to-stream-internal
	    (or (procedure-expression thing)
		(procedure-expression-string thing))
	    stream)
	   (encode-data-structure-to-stream-internal
	    (or (procedure-environment thing)
		(procedure-environment-string thing))
	    stream)))))

(defun encode-kb-id (thing stream)
  (let ((id (abstract-handle-kb-id thing)))
    (if (= -1 id)
	(encode-data-structure-to-stream-internal id stream)
	(encode-data-structure-to-stream-internal
	 (+ *server-unique-kb-id-offset* id) stream))))

(defmethod encode-data-structure-to-stream-internal
    ((thing frame-handle) stream)
  (let (#+Lucid (system::*print-output* stream))
    (fast-write-fixnum *frame-handle-type-code* #-Lucid stream)
    (fast-terpri stream)
    (encode-data-structure-to-stream-internal
     (frame-handle-id thing) stream)
    (encode-kb-id thing stream)))

(defmethod encode-data-structure-to-stream-internal
    ((thing remote-value) stream)
  (let (#+Lucid (system::*print-output* stream))
    (fast-write-fixnum *remote-value-type-code* #-Lucid stream)
    (fast-terpri stream)
    (encode-data-structure-to-stream-internal
     (remote-value-id thing) stream)
    (encode-kb-id thing stream)))

(defmethod encode-data-structure-to-stream-internal ((thing enumerator) stream)
  (let (#+Lucid (system::*print-output* stream))
    (fast-write-fixnum *enumerator-type-code* #-Lucid stream)
    (fast-terpri stream)
    (let ((id (without-scheduling
	       (when (not (enumerator-id thing))
		 (setf (enumerator-id thing) (allocate-enumerator-id)))
	       (enumerator-id thing))))
      ;; Only intern the enumerator when we actually transmit it somewhere!!
      (when (not (gethash id *enumerator-id-to-enumerator-table*))
	(setf (gethash id *enumerator-id-to-enumerator-table*) thing))
      (encode-data-structure-to-stream-internal id stream))))

(defun default-encode-other-data-structure (thing stream)
  (let ((*print-escape* nil)
	(*print-readably* nil)
	#+Lucid (system::*print-output* stream)
	(string (princ-to-string thing)))
    (fast-write-fixnum *other-type-code* #-Lucid stream)
    (fast-terpri stream)
    (fast-write-fixnum (length string) #-Lucid stream)
    (fast-terpri stream)
    (fast-write-string string stream)
    (fast-terpri stream)))

(defvar *encode-other-data-structure-function*
  'default-encode-other-data-structure)

(defmethod encode-data-structure-to-stream-internal ((thing t) stream)
  (funcall *encode-other-data-structure-function* thing stream))

;------------------------------------------------------------------------------

(defokbcgeneric decode-data-structure-from-stream (stream key)
  (:documentation "Given a stream along which an OKBC client or server has
   serialised data, decodes that serialised representation into real data
   structures.  This function is used by the transport layer of the network
   model to receive data.  It takes care of any necessary interning of
   symbols, decoding remote values, substitution of remote frame handles, and
   mapping of abstract KB representations.<p>

  This function can also be used (in conjunction with
  <code>encode-data-structure-to-stream</code>) as a means of loading
  (and saving) KB content to files and streams.<P>

  At present, the only supported value for <code>key</code> is
  <code>:portable</code>."))

(defmethod decode-data-structure-from-stream (stream (key (eql :portable)))
  (with-standard-io-syntax
      (let ((*print-readably* nil))
	(decode-data-structure-from-stream-internal stream))))

(defmethod decode-data-structure-from-stream (stream (key (eql :lisp)))
  (with-standard-io-syntax (read stream)))

(defun decode-data-structure-from-stream-internal (stream)
  (let ((code (fast-read-line stream)))
    (when (let ((cookie "GET /"))
	    (and (> (length code) (length cookie))
		 (string-equal cookie code :end2 (length cookie))))
      (error "PROTOCOL ERROR.  You are probably trying to connect to this ~
              server using the wrong type of connection ~
              (KSL-Network-Connection?).  What should have been an integer ~
              type code was really: ~S" code))
    (decode-data-structure-from-stream-given-key stream (parse-integer code))))

(defmethod decode-data-structure-from-stream-given-key
    (stream (code (eql *list-type-code*)))
  (let ((length (parse-integer (fast-read-line stream))))
    (loop for index from 0 below length
	  collect (decode-data-structure-from-stream-internal stream))))

(defvar #+Lucid user::*package-to-use-for-non-existent-packages*
        #-Lucid cl-user::*package-to-use-for-non-existent-packages*
  (or (find-package :common-lisp-user)
      (find-package :user)))

(defun find-or-create-quasi-package (name)
  (etypecase name
    (quasi-package name)
    ((or string symbol)
     (let ((name (string name)))
       (or (gethash name *quasi-package-table*)
	   (let ((new (make-quasi-package :name name)))
	     (setf (gethash name *quasi-package-table*) new)
	     new))))))

(defun intern-quasi-symbol (pname package-name)
  "The <code>quasi-symbol</code> counterpart to <code>intern</code>.  This
   function should be used by back ends when loading KBs to make sure that
   any <code>quasi-symbol</code>s are interned correctly.  See also
   <code>quasi-symbol-reader</code>."
  (let ((real-package (find-package
		       (etypecase package-name
			(quasi-package (name package-name))
			((or symbol string) (string package-name))
			(package (package-name package-name))))))
    (if real-package
	(intern pname real-package)
	(let ((package (find-or-create-quasi-package package-name)))
	  (or (gethash pname (quasi-package-symbol-table package))
	      (let ((new (make-quasi-symbol :name pname :package package)))
		(setf (gethash pname (quasi-package-symbol-table package)) new)
		new))))))
    
(defmethod decode-data-structure-from-stream-given-key
    (stream (code (eql *symbol-type-code*)))
  (fast-read-line stream) ;;; Ignore length
  (let ((package-name (fast-read-line stream)))
    (fast-read-line stream) ;;; Ignore length
    (let ((pname (fast-read-line stream)))
      (if (string= nil package-name)
	  (make-symbol pname)
	  (let ((package (find-package package-name)))
	    (if package
		(let ((sym (intern pname package-name)))
		  (if (eq sym :__establish-local-connection)
		      (okbc:local-connection)
		      sym))
		;; This is the old way we did it!
;		(let ((package
;                       #+Lucid user::*package-to-use-for-non-existent-packages*
;                       #-Lucid
;                       cl-user::*package-to-use-for-non-existent-packages*))
;                  (format *standard-output*
;                          "~%;;; !! Package ~A does not exist.  ~
;                                    Interning \"~A\" into ~A"
;                          (the string package-name)
;                          (the string pname)
;                          package)
;                  (intern pname package))
		(intern-quasi-symbol pname package-name)))))))

(defmethod decode-data-structure-from-stream-given-key
    (stream (code (eql *integer-type-code*)))
  (fast-read-line stream) ;;; Ignore length
  (parse-integer (fast-read-line stream)))

(defmethod decode-data-structure-from-stream-given-key
    (stream (code (eql *float-type-code*)))
  (fast-read-line stream) ;;; Ignore length
  (safely-read-from-string (fast-read-line stream)))

(defmethod decode-data-structure-from-stream-given-key
    (stream (code (eql *string-type-code*)))
  (let ((length (parse-integer (fast-read-line stream))))
    (let ((string (make-array length :element-type
			      *string-char-element-type*)))
      (loop for index from 0 below length
	    for char = (fast-read-char stream)
	    do (setf (schar string index) char))
      (fast-read-char stream) ;; newline
      string)))

(defmethod decode-data-structure-from-stream-given-key
    ((stream t) (code (eql *false-type-code*)))
  nil)

(defmethod decode-data-structure-from-stream-given-key
    ((stream t) (code (eql *true-type-code*)))
  t)

(defmethod decode-data-structure-from-stream-given-key
    (stream (code (eql *procedure-type-code*)))
  (let ((name        (if (string< *current-transport-version* :b)
			 nil
			 (decode-data-structure-from-stream stream :portable)))
	(arguments   (decode-data-structure-from-stream stream :portable))
	(expression  (decode-data-structure-from-stream stream :portable))
	(environment (decode-data-structure-from-stream stream :portable)))
    (intern-procedure
     :name        name
     :arguments   arguments
     :expression  expression
     :environment environment)))

(defun decode-frame-handle-given-id-and-kb-id (id kb-id)
  (okbc-assert
   (and (integerp kb-id) (or (integerp id) (and (= -1 kb-id) (keywordp id)))) ()
   "Illegal frame handle.  Maybe you are using obsolete transport.  ~
      Both the ID and KB id must be integers, or a keyword ID in KB -1.")
  (let ((key (make-handle-key id kb-id)))
    (multiple-value-bind (existing found-p trie-node)
      (tries:get-hybrid-trie-returning-node
       key *frame-handle-key-to-frame-handle-table*)
      (if found-p
	  (if (eq (frame-handle-thing existing) *undefined-value*)
	      existing
	      (frame-handle-thing existing))
	  (let ((new (make-frame-handle :id id :kb-id kb-id)))
	    (initialize-fast-hash-key new)
	    (set-hybrid-trie-value trie-node new)
	    new)))))

(defmethod decode-data-structure-from-stream-given-key
    (stream (code (eql *frame-handle-type-code*)))
  (let ((id    (decode-data-structure-from-stream stream :portable))
	(kb-id (decode-data-structure-from-stream stream :portable)))
    (decode-frame-handle-given-id-and-kb-id
     id (if (equal kb-id -1) kb-id (- kb-id *server-unique-kb-id-offset*)))))

(defun decode-remote-value-given-id-and-kb-id (id kb-id)
  (okbc-assert
   (and (integerp id) (integerp kb-id)) ()
   "Illegal remote value.  Maybe you are using obsolete transport.  ~
      Both the ID and KB id must be integers.")
  (let ((key (make-handle-key id kb-id)))
    (let ((existing (gethash key *remote-value-key-to-remote-value-table*)))
      (if existing
	  (if (eq (remote-value-thing existing) *undefined-value*)
	      existing
	      (remote-value-thing existing))
	  (let ((new (make-remote-value :id id :kb-id kb-id)))
	    (initialize-fast-hash-key new)
	    (setf (gethash key *remote-value-key-to-remote-value-table*) new)
	    new)))))

(defmethod decode-data-structure-from-stream-given-key
    (stream (code (eql *remote-value-type-code*)))
  (let ((id    (decode-data-structure-from-stream stream :portable))
	(kb-id (decode-data-structure-from-stream stream :portable)))
    (decode-remote-value-given-id-and-kb-id
     id (- kb-id *server-unique-kb-id-offset*))))

(defun decode-enumerator-given-id (id)
 (declare (special *connection*))
 (okbc-assert
  (integerp id) ()
  "Illegal enumerator value.  Maybe you are using obsolete transport.  ~
      The ID must be an integer.")
 (let ((existing (gethash id *enumerator-id-to-enumerator-table*)))
   (if existing
       existing
	  ;;; This has been passed to us from the other side, so make a
	  ;;; remote enumerator object for it.
	  ;;; Note that clients are not allowed to pass enumerators to servers,
	  ;;; but servers can pass enumerators back to clients.
       (if (boundp '*connection*)
	   (let ((new-enumerator (make-network-enumerator
				  :id id
				  :connection *connection*)))
	     (setf (gethash id *enumerator-id-to-enumerator-table*)
		   new-enumerator)
	     new-enumerator)
	   (progn (warn "Tried to intern an enumerator on a server for ID ~D"
			id)
		  nil)))))

(defmethod decode-data-structure-from-stream-given-key
    (stream (code (eql *enumerator-type-code*)))
  (declare (special *connection*))
  (let ((id (decode-data-structure-from-stream stream :portable)))
    (decode-enumerator-given-id id)))

(defun ok-utils:inside-okbc-server-p ()
  "Is true when one is inside a thread that is running an OKBC server."
  *inside-okbc-server-p*)

(defmethod get-kb-types-internal :around ((connection local-connection))
  (if *network-okbc-client-p*
      (call-next-method)
      (if (inside-okbc-server-p)
	  (let ((results (call-next-method)))
	    (sort
	     (loop for p in results
		   for abstract = (abstract-kb-class-name-from-kb p)
		   for concrete =
		   (and abstract (concrete-kb-class-from-abstract-kb-class-name
				  abstract))
		   for accept-p =
		   (and concrete (not (typep p 'ok-back:network-kb)))
		   when accept-p
		   collect p
		   when (and (not concrete) (not (typep p 'ok-back:network-kb)))
		   do (warn "Compliant KB class ~S does not have enough~%~
                             protocol to make it network visible!"
			    (type-of-name p)))
	     #'string< :key 'type-of-name))
	  (let ((results (call-next-method)))
	    (loop for p in results
		  for abstract = (abstract-kb-class-name-from-kb p)
		  for concrete =
		  (and abstract (concrete-kb-class-from-abstract-kb-class-name
				 abstract))
		  for accept-p =
		   (and concrete (not (typep p 'ok-back:network-kb)))
		  when accept-p
		  collect p)))))

#-(and Lucid (not lcl5.0)) ;; Compiler bug in old version.  You lose.
(defmethod get-kb-type-internal :around
  (thing (connection local-connection))
  (if *network-okbc-client-p*
      (call-next-method)
      (let ((real-thing
	     (or (concrete-kb-class-from-abstract-kb-class-name thing)
		 thing)))
	(call-next-method real-thing connection))))

(defun find-okbc-kb-of-type
    (type name &key (error-p t) (connection (okbc:local-connection)))
  (typecase name
    ((or symbol quasi-symbol)
     (let ((actual-type
	    (concrete-kb-class-from-abstract-kb-class-name type)))
       (or (and actual-type
		(find-kb-of-type-internal name (get-kb-type-internal
						actual-type connection)
					  connection))
	   (if error-p
	       (error 'kb-not-found :kb name)
	       nil))))
    (otherwise (if error-p
		   (error 'kb-not-found :kb name)
		   nil))))

(defun find-or-create-local-network-okbc-kb (name kb-type)
  (when (not (typep name '(or symbol quasi-symbol)))
    (warn "Remote KB name ~S is not a symbol or quasi-symbol" name)
    (error "Remote KB name ~S is not a symbol or quasi-symbol" name))
  (let ((local-connection (okbc:local-connection)))
    (let ((existing (or (find-okbc-kb-of-type 'network-kb name :error-p nil
					      :connection local-connection)
			(find-kb-of-type-internal
			 name (okbc:get-kb-type 'network-kb)
			 local-connection)
			(find-okbc-kb-of-type kb-type name :error-p nil))))
      (if existing
	  existing
	  (let ((new (make-instance
		      (class-of kb-type)
		      :name name
		      :connection
		      (or *current-connection*
			  (and (current-kb) (connection (current-kb)))))))
	    (values new :created))))))

(defmethod network-kb-class-from-abstract-kb-class-name (name)
  (let ((name-root (subseq (symbol-name name)
			   (length "ABSTRACT-")
			   (- (length (symbol-name name))
			      (length "-KB")))))
    (eval `(defnetwork-okbc-kb ,name-root ()))))

(defmethod frs-name-internal
    ((kb-type network-kb) (connection local-connection))
  (let ((abstract-name (abstract-name kb-type)))
    (let ((name-root (subseq (symbol-name abstract-name)
			     (length "ABSTRACT-")
			     (- (length (symbol-name abstract-name))
				(length "-KB")))))
      name-root)))

(defun decode-kb-given-name-and-type (name type)
  (let ((localcon (okbc:local-connection)))
    (let ((concrete-class
	   (and (not *network-okbc-client-p*)
		(concrete-kb-class-from-abstract-kb-class-name type))))
      (if concrete-class
	  (if (eq :prototype name)
	      (get-kb-type-internal concrete-class localcon)
	      (let ((kb (find-kb-of-type-internal
			 name (get-kb-type-internal concrete-class localcon)
			 localcon)))
		(if kb
		    kb
		    (progn (warn "Tried to get non-existent KB ~S" name)
			   (format *trace-output*
			    "Tried to get non-existent KB ~S" name)
			   nil))))
	  (if (eq :prototype name)
	      (get-kb-type-internal
	       (network-kb-class-from-abstract-kb-class-name type)
	       localcon)
	      (find-or-create-local-network-okbc-kb
	       name (class-prototype-safe
		     (network-kb-class-from-abstract-kb-class-name type))))))))

(defmethod decode-data-structure-from-stream-given-key
    ((stream t) (code (eql *kb-type-code*)))
 (let ((name (decode-data-structure-from-stream-internal stream))
       (type (decode-data-structure-from-stream-internal stream)))
   (decode-kb-given-name-and-type name type)))

(defmethod decode-data-structure-from-stream-given-key
    ((stream t) (code (eql *other-type-code*)))
  ;; If you don't know what it is, pretend it's a string.
  (decode-data-structure-from-stream-given-key stream *string-type-code*))

;==============================================================================

;;; The server top level for the generic, simple, single-threaded server.

(defparameter *nokbc-port* 6502)
(defvar *saved-sockets-alist* nil)
(defvar *socket*)
(defvar *socaddr*)
(defparameter *catch-errors-in-persistent-connections-p* t)

#-(or Lucid Allegro Harlequin-Common-Lisp)
(cerror "Go ahead, anyway"
	"You must implement the \"NOKBC-SERVER\" function for this Lisp!")

;; This is a rewriting of the ipc:start-lisp-listener-daemon provided by
;; Franz so that we can run our listener daemon at the same time as the
;; Allegro emacs-lisp interface.

#+(or Allegro Harlequin-Common-Lisp)
(defparameter *server-startup-timout* 30
  "Seconds to wait before barfing out when we fail to start up a server.")

#+(and Allegro (not (and allegro-version>= (version>= 5))))
(defun ok-utils:nokbc-server (&key (port *nokbc-port*) (catch-errors-p t)
                                   (server-type :okbc) (max-port port))
  (declare (special *nokbc-port* *saved-sockets-alist*))
  (assert (>= max-port port))
  (let ((port-used (gensym)))
    (cond ((not (assoc port *saved-sockets-alist* :test #'equal))
           (let ((process
                  (mp:process-run-function "NOKBC Listener Socket Daemon"
                                           'run-listener-socket-daemon port
                                           port-used catch-errors-p server-type
                                           max-port)))
             ;; wait for port-used to be bound, that is, set by
             ;; run-listener-socket-daemon
             (mp:process-wait-with-timeout
              "Waiting for server" *server-startup-timout*
              #'boundp port-used)
	     (when (boundp port-used)
	       (setf *saved-sockets-alist*
		     (acons (symbol-value port-used) process
			    *saved-sockets-alist*))
	       (setf (mp::process-interruptable-p process) nil)
	       (setf (getf (mp:process-property-list process)
			   ':survive-dumplisp)
		     'mp:process-kill))
             (values process (symbol-value port-used))))
          (t (warn "The Network OKBC listener daemon is already ~
                    running on port ~S.~%"
                   port)
             (values nil nil)))))

#+Allegro
(defparameter *last-server-condition* nil)

#+(and Allegro (not (and allegro-version>= (version>= 5))))
(defun run-listener-socket-daemon
    (port port-used-symbol catch-errors-p server-type
	  &optional (max-port port))
  (handler-case
   (ipc::lisp-server-socket-daemon 
    :startup-stream-process
    #'(lambda (stream &rest args)
	(apply 'fork-nokbc-request catch-errors-p server-type stream args))
    :inet-port-min port
    :inet-port-max max-port
    :server-startup-announce-function 
    #'(lambda ()
	(format t "~&;Network OKBC server started on port ~a~%"
	  ipc:*inet-port-used*)
	(set port-used-symbol ipc:*inet-port-used*)))
   (error (condition)
	  (setq *last-server-condition* condition)
	  (let ((*print-escape* nil))
	    (warn "!! Failed to start up server:  Condition ~S is now:~
                   ~A" '*last-server-condition*
		   (princ-to-string condition)))
	  nil)))


;=============================================================================

#+(and Allegro allegro-version>= (version>= 5))
(defun ok-utils:nokbc-server (&key (port *nokbc-port*) (catch-errors-p t)
                                   (server-type :okbc))
  (declare (special *nokbc-port* *saved-sockets-alist*))
  (let ((port-used (gensym)))
    (cond ((not (assoc port *saved-sockets-alist* :test #'equal))
           (let ((process
		  (server:make-socket-server
		   :name "NOKBC Listener Socket Daemon"
		   :port port
		   ;;:function #' (lambda (port)
		   ;; (run-listener-socket-daemon
		   ;; port port-used server-type catch-errors-p)))))
		   :function
		   #' (lambda (port)
			(fork-nokbc-request catch-errors-p server-type port))
		   :server-startup-announce-function
		   #' (lambda (port)
			(setf (symbol-value port-used) port)))))
					     
             ;; wait for port-used to be bound, that is, set by
             ;; run-listener-socket-daemon
             (mp:process-wait-with-timeout
              "Waiting for server" *server-startup-timout*
              #'boundp port-used)
	     (when (boundp port-used)
	       (setf *saved-sockets-alist*
		     (acons (symbol-value port-used) process
			    *saved-sockets-alist*))
	       (setf (mp::process-interruptible-p process) nil)
	       (setf (getf (mp:process-property-list process)
			   ':survive-dumplisp)
		     'mp:process-kill))
             (values process (symbol-value port-used))))
          (t (warn "The Network OKBC listener daemon is already ~
                    running on port ~S.~%"
                   port)
             (values nil nil)))))


;;;no longer used
#+(and Allegro allegro-version>= (version>= 5))
(defun run-listener-socket-daemon
    (port port-used-symbol server-type catch-errors-p)
  (progn
    (setf (symbol-value port-used-symbol) port)
    (handler-case
      (fork-nokbc-request catch-errors-p server-type port)
   (error (condition)
	  (setq *last-server-condition* condition)
	  (let ((*print-escape* nil))
	    (warn "!! Failed to start up server:  Condition ~S is now:~
                   ~A" '*last-server-condition*
		   (princ-to-string condition)))
	  nil))))

;=============================================================================

#+Harlequin-Common-Lisp
(defun ok-utils:nokbc-server (&key (port *nokbc-port*) (catch-errors-p t)
                                   (server-type :okbc))
  (declare (special *nokbc-port* *saved-sockets-alist*))
  (let ((port-used (gensym)))
    (cond ((not (assoc port *saved-sockets-alist* :test #'equal))
	   (let ((process (comm:start-up-server-and-mp
			   :process-name "NOKBC Listener Socket Daemon"
			   :function
			   #'(lambda (handle)
			       (run-listener-socket-daemon
				handle port-used server-type catch-errors-p))
			   :service port
			   :announce *trace-output*)))
	     ;; wait for port-used to be bound, that is, set by
	     ;; run-listener-socket-daemon
	     (mp:process-wait-with-timeout
	      "Waiting for server" *server-startup-timout*
	      #'boundp port-used)
	     (when (boundp port-used)
	       (setf *saved-sockets-alist*
		     (acons (symbol-value port-used) process
			    *saved-sockets-alist*)))
             (values process (symbol-value port-used))))
          (t (warn "The Network OKBC listener daemon is already ~
                    running on port ~S.~%"
                   port)
             (values nil nil)))))

#+Harlequin-Common-Lisp
(defun run-listener-socket-daemon (handle port-used server-type catch-errors-p)
  (let ((stream (make-instance 'comm:socket-stream
			       :socket handle
			       :direction :io
			       :element-type 'base-char)))
    (setf (symbol-value port-used) t)
    (fork-nokbc-request catch-errors-p server-type stream)))

;=============================================================================

;; This is a rewriting of the ipc:kill-lisp-listener-daemon function from
;; Franz, and can be called to shut down the NOKBC server.
(defun ok-utils:kill-nokbc-server (&optional port)
  "In some implementations, a daemon process may be spun off to handle
   a network OKBC server.  Such daemon servers
   can be killed using <code>kill-nokbc-server</code>, which kills the
   server for the specified <code>port</code>."
  #-Allegro (declare (ignore port))
  #-Allegro
  (warn "In this Lisp implementation, OKBC servers run in the foreground.  ~
         Kill-nokbc-server is not implemented.")
  #+Allegro
  (let ((socket (when port 
                  (cdr (assoc port *saved-sockets-alist*)))))
    (if (or (null socket)
            (progn
	      ;; for acl5.0 version, socket is really the daemon process
	      #+(and allegro-version>= (version>= 5))
	      (server:kill-socket-server socket)
	      #-(and allegro-version>= (version>= 5))
	      (mp:process-kill socket)
              ;; this makes sure the kill is allowed to complete:
              #-(and allegro-version>= (version>= 5))
	      (mp:process-allow-schedule)
              (setq *saved-sockets-alist*
                    (remove (if port 
                                (assoc port *saved-sockets-alist*
                                       :test #'equal)
                                (rassoc socket *saved-sockets-alist*
                                        :test #'eq))
                            *saved-sockets-alist*))
              t))
        t
      (generic-error "couldn't kill the NOKBC listener daemon"))))

#+(or Allegro Harlequin-Common-Lisp)
(defun fork-nokbc-request (catch-errors-p server-type stream
					  &key fd &allow-other-keys)
  (declare (ignore fd))
  (okbc-assert stream)
  (catch :abort
    (catch :disconnect
      (unwind-protect
	   (let ((*catch-errors-in-persistent-connections-p*
		  catch-errors-p)) 
	     (nokbc-server-internal stream server-type))
	(ignore-errors (close stream :abort t))))))

#+Lucid
(defun ok-utils:nokbc-server
    (&key (port *nokbc-port*) (catch-errors-p t) (server-type :okbc)
	  (max-port port))
  (assert (>= max-port port))
  (multiple-value-bind (spec error-p actual-port)
      (loop for p from port to max-port
	    for (res error-p) = (multiple-value-list
				    (ignore-errors
				     (multiple-value-list
					 (#+XLT lucid::make-tcp-socket
						#+lcl5.0
						make-tcp-socket
						#-(or XLT lcl5.0)
						lucid::lep-make-tcp-socket
						p))))
	    when (not error-p) return (values res error-p p)
	    when error-p do (format t "~%;;; Port ~D is occupied." p)
	    finally (return (values nil t max-port)))
    (multiple-value-bind (*socket* *socaddr*)
	(if error-p
	    (if (assoc actual-port *saved-sockets-alist* :test #'equal)
		(values-list
		 (rest (assoc actual-port *saved-sockets-alist*
			      :test #'equal)))
		(if (= port max-port)
		    (generic-error "Cannot bind port ~D." actual-port)
		    (generic-error "Cannot bind port in range ~D:~D."
				   port max-port)))
	    (values-list spec))
      (setf *saved-sockets-alist*
	    (cons (list actual-port *socket* *socaddr*)
		  (remove (assoc actual-port *saved-sockets-alist*
				 :test #'equal)
			  *saved-sockets-alist*)))
      (format t "~%;;; Starting OKBC server on port ~D" actual-port)
      ;; We do things this way rather than with a with-open-stream
      ;; because this way we have control over how the close happens.
      ;; We need to make sure that we do a close :abort t to make sure
      ;; that the buffer is NOT flushed.  If we flush and the stream
      ;; is closed then we lose with a broken pipe.
      (loop for stream = (ignore-errors
			  (#+XLT lucid::accept-tcp-stream
				 #+lcl5.0
				 accept-tcp-socket
				 #-(or XLT lcl5.0)
				 lucid::lep-accept-tcp-stream
				 *socket* *socaddr*))
	    when stream
	    do (okbc-assert stream)
	    (catch :abort
	      (catch :disconnect
		(unwind-protect
		     (let ((*catch-errors-in-persistent-connections-p*
			    catch-errors-p)) 
		       (nokbc-server-internal stream server-type))
		  (ignore-errors (close stream :abort t)))))))))

(defun nokbc-server-internal (stream server-type)
  (let ((error nil))
    (with-standard-io-syntax
	(let ((initialiser
	       (handler-case
		(decode-data-structure-from-stream stream :portable)
		(error (condition) (setq error condition) nil)))
	      (*print-readably* nil);; this is important!
	      (*encode-other-data-structure-function*
	       'encode-other-objects-as-frame-handles-or-remote-values-in-kb)
	      (*inside-okbc-server-p* t))
	  (if error
	      (handle-okbc-eval-error stream error :portable nil
				      *current-transport-version* :a)
	      (let ((query-format (getf initialiser :query-format))
		    (reply-format (getf initialiser :reply-format))
		    (transport-version (getf initialiser :transport-version))
		    (kb-library (getf initialiser :kb-library)))
		(let ((*current-transport-version* transport-version))
		  (#+Lucid handler-case #-Lucid progn
		   (connect-and-go-to-read-eval-print-loop
		    stream query-format reply-format transport-version
		    kb-library server-type)
		   #+Lucid
		   (broken-pipe-io-error
		    (condition)
		    (declare (ignore condition))
		    (format t "~%;;; Broken pipe caught.")
		    nil)
		   #+Lucid
		   (connection-reset-by-peer-io-error
		    (condition)
		    (declare (ignore condition))
		    (format t "~%;;; Connection reset by peer caught.")
		    nil)))))))))

#+Lucid
(define-condition broken-pipe-io-error (liquid::file-io-error) ())

#+Lucid
(define-condition connection-reset-by-peer-io-error (liquid::file-io-error) ())

#+Lucid
(lcl:defadvice (error :hack-broken-pipe) (&rest args)
  (when (and (eq (first args) 'liquid::file-io-error))
    (cond ((equal (getf (rest args) :osi-message) "Broken pipe")
	   (setf (first args) 'broken-pipe-io-error))
	  ((equal (getf (rest args) :osi-message) "Connection reset by peer")
	   (setf (first args) 'connection-reset-by-peer-io-error))
	  (t nil)))
  (lcl::apply-advice-continue args))

(defdoc ok-utils:nokbc-server (function)
  "Starts network OKBC server that listens to a socket for attempts to
   connect, and handles OKBC requests when they arrive.<P>

   <code>Server-type</code> is some unique identifying key known to the
   server implementor.  It is used in specializing concurrency control
   for the server (see <code>eval-maybe-with-session-locks</code>).<P>

   If <code>max-port</code> is supplied it should be an integer
   &gt;=<code>port</code>.  The server will iterate checking ports
   until a free port is found.  The allocated socket and the port are
   returned.  Note: Care should be exercised when using the
   <code>max-port</code> argument.  If there is already an OKBC server
   running on <code>port</code> in a different Lisp process then a
   new server will be started.  This may result in concurrency control
   problems in certain KBs.  This server is intended primarily to be
   single-threaded.  If you plan to run multiple OKBC servers within the
   same Lisp image, you should take care of any concurrency control and
   locking issues, possibly by introducing a lock at
   <code>eval-maybe-with-session-locks</code>, or
   <code>get-network-okbc-request-results</code>.<P>

   In some implementations, a daemon process may be spun off to handle
   the server.  If the server daemon process ever completes, the daemon
   makes sure any outstanding connections are closed.  Such daemon servers
   can be killed using <code>kill-nokbc-server</code>.  In implementations
   in which a server is not spun off as a daemon, the server can be
   terminated simply by interrupting, and aborting out.")

;==============================================================================

(defmethod maybe-free-session-locks ((server-type t))
  nil)

(defun disconnect-connection ()
  (throw :abort :disconnect))

(defokbcgeneric ok-back:add-notifications-for-okbc-side-effect
    (stream function args server-type)
  (:documentation "This is a hook to allow particular OKBC server
   implementations to log side effects and notify addordingly.
   <code>Stream</code> is the TCP stream being used by the server.
   <code>Function</code> and <code>args</code> are the function and arguments
   being executed by the server.  <code>Server-type</code> is some unique
   identifying key known to the server implementor."))

(defmethod ok-back:add-notifications-for-okbc-side-effect
    ((stream t) (function t) (args t) (server-type t))
  nil)

(defokbcgeneric ok-cache:flush-any-necessary-caches (thing)
  (:documentation "Flushes any OKBC caches that might be associated with
   <code>thing</code>."))

(defmethod ok-cache:flush-any-necessary-caches ((thing t))
  nil)

(defokbcgeneric get-network-okbc-request-results
    (stream args ontology-args server-type)
  (:documentation "Actually executes a networked OKBC request and returns
   the resulting values to the network transport layer as a list.
   <code>Server-type</code> is some unique
   identifying key known to the server implementor.  If you plan to add any
   concurrency control to the server, adding an <code>:around</code> method
   on this generic function that introduces a process lock would be likely to
   do the right thing.  Locking at this point is a little finer grained and
   a little more risky than locking at
   <code>eval-maybe-with-session-locks</code>."))

(defmethod get-network-okbc-request-results
    (stream args ontology-args (server-type t))
  (okbc-assert (gethash (first args)
		       *acceptable-okbcops-for-call-procedure*)
	      () "~S is not an acceptable OKBC operator"
	      (first args))
  (okbc-assert (not (handles-in-tree-p args (current-kb))) ()
	      "Cannot process expression ~S, it contains unresolved handles."
	      args)
  (macrolet
      ((doit ()
	 `(if (causes-side-effects-p (first args))
	      (prog1 (multiple-value-list
			 (apply (first args) (rest args)))
		(ok-cache:flush-any-necessary-caches nil)
		(add-notifications-for-okbc-side-effect
		 stream (first args) (rest args) server-type))
	      (multiple-value-list
		  (apply (first args) (rest args))))))
    (if ontology-args
	(with-kb-io-syntax (:kb (first ontology-args)
				     ;; leave as :file for now
					;:purpose :user-interface
				     )
	  (let ((*print-readably* nil))
	    (doit)))
	(let ((*print-readably* nil)) (doit)))))

;;; Find or create a remote value to send
(defun intern-remote-value (thing)
  "Given a random <code>thing</code>, finds or creates a
   <code>remote-value</code> object to represent that <code>thing</code>.
   <code>Remote-value</code>s are interned so that object identity is preserved
   by the network transport layer."
  (let ((key (gethash thing *remote-value-to-remote-value-key-table*)))
    (if key
	(let ((rv (gethash key
			   *remote-value-key-to-remote-value-table*)))
	  (okbc-assert rv)
	  rv)
	(let ((new-id (+ (image-unique-tag)
			 (allocate-remote-value-id)))
	      (kb-id (unique-id (or *current-kb*
				    (meta-kb-internal
				     (local-connection))))))
	  (let ((new-key (make-handle-key new-id kb-id)))
	    (setf (gethash thing
			   *remote-value-to-remote-value-key-table*)
		  new-key)
	    (let ((new-remote-value
		   (make-remote-value
		    :id new-id :kb-id kb-id :thing thing)))
	      (initialize-fast-hash-key new-remote-value)
	      (setf
	       (gethash new-key
			*remote-value-key-to-remote-value-table*)
	       new-remote-value)
	      new-remote-value))))))

(defmethod encode-other-objects-as-frame-handles-or-remote-values-in-kb
    ((thing t) stream)
  (let ((remote-value (intern-remote-value thing)))
    (encode-data-structure-to-stream-internal remote-value stream)
    remote-value))

(defun maybe-emit-reply-tag (reply-stream reply-tag)
  (declare (special *request-cookie*))
  (cond (reply-tag
	 (princ *request-cookie* reply-stream)
	 (terpri reply-stream)
	 (princ reply-tag reply-stream)
	 (terpri reply-stream)
	 t)
	(t nil)))

(defun print-error-string-from-condition
    (stream condition)
  (if stream
      (progn
	#-Lucid
	(format stream "~A" condition
		(with-output-to-string (str) (describe condition str)))
	#+lucid
	(format stream " ~A "
		(with-output-to-string (str)
		  (or (ignore-errors
		       (progn (lucid::condition-report condition str) t))
		      (format str " Some error occured during the ~
                                reporting of the error.")))))
      (with-output-to-string (stream)
	(print-error-string-from-condition stream condition))))

(defun handle-okbc-eval-error (reply-stream condition reply-format reply-tag
					   transport-version kb-library)
  (declare (ignore kb-library))
  (let ((*print-readably* nil))
    (maybe-emit-reply-tag reply-stream reply-tag)
    (encode-data-structure-to-stream nil reply-stream reply-format)
    (encode-data-structure-to-stream nil reply-stream reply-format)
    (encode-data-structure-to-stream t reply-stream reply-format);;error-p
    (encode-data-structure-to-stream
     (if (and (okbc-condition-p-internal condition)
	      (string>= transport-version :b))
	 (cons (print-error-string-from-condition nil condition)
	       (cons (type-of-name condition)
		     (decode-okbc-condition condition)))
	 (with-standard-io-syntax
	     (with-output-to-string (str)
	       (format str
		       "An error occured during the processing ~
                          of this request, ~%resulting in the signalling ~
                          of a condition: ~%  ")
	       (let ((*print-escape* nil)
		     (*print-readably* nil))
		 (princ condition str)
		 #-Lucid
		 (describe condition str)))))
     reply-stream reply-format)
    ;; ok-to-cache-p
    (encode-data-structure-to-stream nil reply-stream reply-format)
    (when (string>= transport-version :b)
      ;; no messages
      (encode-data-structure-to-stream nil reply-stream reply-format))
    (force-output reply-stream)))

(defmethod eval-network-okbc-request-in-library-context
    ((kb-library t) (body-function t) (error-handler t))
  (eval-network-okbc-request-in-library-context
   :a body-function error-handler))

(defmethod eval-network-okbc-request-in-library-context
    ((kb-library (eql :a)) (body-function t) (error-handler t))
  (if *catch-errors-in-persistent-connections-p*
      (handler-case
       (funcall body-function)
       (error (condition)
	      (funcall error-handler condition)))
      (funcall body-function)))

(defvar *okbc-server-trace-stream* nil)

(defvar *capture-okbc-server-trace-messages-p* t)

(defun eval-network-okbc-request
    (stream args ontology-args reply-format transport-version kb-library
	    server-type &optional (reply-tag nil))
  (declare (special *request-cookie* *ok-to-cache-p*))
  (let ((reply-stream (underlying-stream stream :output))
	(*okbc-server-trace-stream*
	 (if *capture-okbc-server-trace-messages-p*
	     (make-string-output-stream)
	     nil))
	#+ignore (transmit-handles-p (string>= transport-version :b)))
    (flet ((body ()
		 (let ((*ok-to-cache-p* t)
		       (*print-readably* nil))
		   (let ((results
			  (let ((*trace-output*
				 (if *capture-okbc-server-trace-messages-p*
				     *okbc-server-trace-stream*
				     *trace-output*)))
			    (get-network-okbc-request-results
			     stream args ontology-args server-type)))
			 (coerce-indices nil))
		     (let ((coerced-results
			    (loop for res in results
				  for index from 0
				  collect
				  (if *current-kb*
				      (decontextualize-internal
				       res :value *current-kb*)
				    res)
				  #+ignore ;;; the old way
				  (cond (ontology-args
					 (deframify
					   res (first
						ontology-args)
					   transmit-handles-p))
					((current-kb)
					 (deframify
					   res (current-kb)
					   transmit-handles-p))
					(t res))))
			   (trace-results
			    (if *capture-okbc-server-trace-messages-p*
				(get-output-stream-string
				 *okbc-server-trace-stream*)
				"")))
		       (maybe-emit-reply-tag reply-stream reply-tag)
		       (encode-data-structure-to-stream
			coerced-results reply-stream reply-format)
		       (encode-data-structure-to-stream
			coerce-indices reply-stream reply-format)
		       (encode-data-structure-to-stream;; error-p
			nil reply-stream reply-format)
		       (encode-data-structure-to-stream
			:ok reply-stream reply-format);; status
		       (encode-data-structure-to-stream
			*ok-to-cache-p* reply-stream reply-format)
		       (when (string>= transport-version :b)
			 (encode-data-structure-to-stream
			  (if (equal "" trace-results)
			      ;; no messages
			      nil
			      trace-results)
			  reply-stream reply-format))
		       (force-output reply-stream))
		     (values-list results))))
	   (error-handler
	    (condition)
	    (handle-okbc-eval-error reply-stream condition reply-format
				   reply-tag transport-version
				   kb-library)))
      (eval-network-okbc-request-in-library-context
       kb-library #'body #'error-handler))))

(defokbcgeneric eval-maybe-with-session-locks
    (server-type stream args ontology-args reply-format transport-version
     kb-library reply-tag)
  (:documentation "This generic function is a specific implementation hook
   provided to allow implementations to introduce concurrency control when
   running multi-threaded servers.  Concurrency control should be introduced
   here by defining an <code>:around</code> method (presumably)
   <code>:eql</code> specialized on the <code>server-type</code>.
   <code>Server-type</code> is the same as the type key provided to
   <code>nokbc-server</code>.<P>

   All arguments other than <code>server-type</code> are part of the
   implementation of the server, and should not be changed.  See also
   <code>get-network-okbc-request-results</code>"))
  
(defmethod eval-maybe-with-session-locks
    ((server-type t) stream args ontology-args reply-format transport-version
     kb-library reply-tag)
  (eval-network-okbc-request stream args ontology-args
			    reply-format transport-version
			    kb-library server-type reply-tag))

(defun get-kb-args (stream args find-args) ;; obsolete
  (declare (ignore stream args find-args))
  nil)

(defmethod prototype-p ((thing t)) nil)

(defmethod prototype-p ((thing kb))
  (eq thing (class-prototype-safe (class-of thing))))

(defmethod prototype-p ((thing structure-kb))
  (eq thing (class-prototype-safe (class-of thing))))

(defvar *network-okbc-requests-handled* 0)
(defparameter *default-kb-class* 'ok-back::abstract-ontology-kb)


(defun extract-class-for-kb-type (spec)
  (if (eq spec :default)
      (concrete-kb-class-from-abstract-kb-class-name
       *default-kb-class*)
      (if (and (consp spec)
	       (eq (first spec)
		   'concrete-kb-class-from-abstract-kb-class-name))
	  (concrete-kb-class-from-abstract-kb-class-name (second spec))
	  (if (symbolp spec)
	      (or (concrete-kb-class-from-abstract-kb-class-name spec)
		  spec)
	      spec))))

(defun coerce-kb-types-etc (thing &optional (error-p t))
  (declare (special $meta-kb$))
  (cond ((not (consp thing))
	 (if error-p
	     (error 'kb-not-found :kb thing)
	     thing))
	((eq (first thing) 'okbc:get-kb-type)
	 (let ((class (extract-class-for-kb-type (second thing))))
	   (if (eq class 'meta-kb)
	       ;; there is only ever exactly one of these
	       $meta-kb$ 
	       (get-kb-type-internal class (okbc:local-connection)))))
	(error-p (error 'kb-not-found :kb thing))
	(t thing)))

(defmethod connect-and-go-to-read-eval-print-loop
    (stream query-format reply-format transport-version kb-library server-type)
  (declare (special *request-cookie*))
  (let ((reply-stream (underlying-stream stream :output))
	(query-stream (underlying-stream stream :input)))
    (with-standard-io-syntax;; return handshake
	(let ((*print-readably* nil))
	  (encode-data-structure-to-stream '(:ok) reply-stream reply-format)
	  (encode-data-structure-to-stream    nil reply-stream reply-format)
	  (encode-data-structure-to-stream    nil reply-stream reply-format)
	  (encode-data-structure-to-stream    :ok reply-stream reply-format)
	  ;; ok-to-cache-p
	  (encode-data-structure-to-stream    nil reply-stream reply-format)
	  (when (string>= transport-version :b)
	    ;; messages
	    (encode-data-structure-to-stream
	     "Persistent Network OKBC connection established." 
	     reply-stream reply-format))
	  (force-output reply-stream)))
    (maybe-free-session-locks server-type)
    (loop for reply-tag
	  = (progn ;;; loopingly look for cookie
	      (loop for line = (fast-read-line stream nil nil)
		    when (not line) do (throw :abort :eof-abort)
		    when (and (>= (length line) (length *request-cookie*))
			      (string= line *request-cookie* :end1
				       (length *request-cookie*)))
		    return t)
	      (let ((line (fast-read-line stream nil nil)))
		(parse-integer (string-trim '(#\return #\newline) line))))
	  for find-args =
	      (decode-data-structure-from-stream
	       query-stream query-format)
	  for args
	  = (decode-data-structure-from-stream query-stream query-format)
	  when (or (eq args :eof) (eq find-args :eof))
	  do (throw :abort :eof-abort)
	  do (let ((ontology-args (get-kb-args stream args find-args)))
	       (let ((*current-kb*
		      (or (first ontology-args)
			  (loop for arg in args
				when (and (kb-p arg)
					  (not (prototype-p arg)))
				return arg)
			  (current-kb))))
		 (loop for index in find-args
		       for th in ontology-args
		       do (setf (nth index (rest args)) th))
		 (loop for index from 1
		       for arg in (rest args)
		       do (setf (nth index args)
				(coerce-kb-types-etc arg nil)))
		 (case (first args)
		   (:disconnect (disconnect-connection))
		   (otherwise
		    (eval-maybe-with-session-locks
		     server-type stream args ontology-args reply-format
		     transport-version kb-library reply-tag)))))
	     (incf *network-okbc-requests-handled*))))

;==============================================================================

;;; Client stuff

(defvar *ignore-network-read-errors-p* t)

(defmacro maybe-ignore-errors (&body body)
  (let ((res (gensym))
	(error-p (gensym)))
    `(if *ignore-network-read-errors-p*
      (multiple-value-bind
	  (,res ,error-p) (ignore-errors ,@body)
	  (when ,error-p
	    (warn "Some sort of read error occured in the OKBC network ~
                   transport layer.  To debug this, close your connection, ~
                   (setq ~S nil) ~
                   and retry."
		  '*ignore-network-read-errors-p*))
	  (values ,res ,error-p))
      (progn ,@body))))

(defvar *request-cookie* "REQUEST!")

(defun skip-until-we-hit-the-right-reply-tag (stream connection)
  (loop do (loop for line = (fast-read-line stream nil nil)
		 when (not line)
		 do (error-on-stream
		     stream
		     "Couldn't find magic cookie on reply stream.")
		 when (string= line *request-cookie*)
		 return t)
	(let ((line (fast-read-line stream nil nil)))
	  (when (not line)
	    (error-on-stream
	     stream
	     "Couldn't find reply tag ~D on reply stream."
	     (request-tag connection)))
	  (let ((tag-received (parse-integer line))
		(current (request-tag connection)))
	    (cond ((not (numberp tag-received))
		   (error-on-stream
		    stream
		    "Couldn't find reply tag ~D on reply stream."
		    current))
		  ((= tag-received current) (return t)) ;; found it
		  ((< tag-received current)
		   nil);; skip, we haven't synched yet.
		  (t (setf (request-tag connection) tag-received) ;;resynch
		     (error-on-stream
		      stream
		      "Couldn't find reply tag ~D on reply stream.  ~
                              We have already gone too far some how.  Tag ~
                              received was ~D."
		      current tag-received)))))))

(defun make-network-call (kb args-to-find-kb-on &rest args)
  (let ((*current-kb* kb)
	(connection (connection kb)))
    (let ((*current-connection* connection))
      (if (eq :ephemeral (connection-method connection))
	  (with-connection-to-socket (str (host connection)
					  (port connection))
	    (emit-network-call str connection args-to-find-kb-on args))
	  (progn (initialize-connection connection)
		 (emit-network-call (net-stream connection) connection
				    args-to-find-kb-on args))))))

(defun make-network-call-from-connection
    (connection args-to-find-kb-on &rest args)
  (let ((*current-connection* connection))
    (if (eq :ephemeral (connection-method connection))
	(with-connection-to-socket (str (host connection)
					(port connection))
	  (emit-network-call str connection args-to-find-kb-on args))
	(progn (initialize-connection connection)
	       (emit-network-call (net-stream connection) connection
				  args-to-find-kb-on args)))))

(defun emit-network-call-to-persistent-stream (stream connection
						      args-to-find-kb-on
						      args query-format)
  (let ((*print-case* :downcase)
	(*print-readably* nil))
    #+MCL
    (progn (ccl::telnet-write-line stream "~A~%" *request-cookie*)
	   (ccl::telnet-write-line stream "~A~%"
				   (incf (request-tag connection))))
    #-MCL
    (progn
      (princ *request-cookie* stream)
      (terpri stream)
      (princ (incf (request-tag connection)) stream)
      (terpri stream))
    #+ignore
    (format t "~%;;; Sending request on existing stream ~S for ~D"
	    stream (request-tag connection))
    (encode-data-structure-to-stream
     args-to-find-kb-on stream query-format)
    (encode-data-structure-to-stream
     args stream query-format)
    (force-output stream)))

(defokbcgeneric emit-network-call-to-ephemeral-connection
    (stream connection args-to-find-kb-on args query-format
	    reply-format transport-version kb-library user-id session-id key))

(defun emit-network-call-internal
    (stream connection args-to-find-kb-on args &optional
	    (query-format *default-network-okbc-query-format*)
	    (reply-format *default-network-okbc-reply-format*)
	    (transport-version *default-network-okbc-transport-version*)
	    (kb-library (kb-library connection)))
  ;;(princ "." *initial-io*)
  ;;(print (list (first args) (second args)) *initial-io*)
  (okbc-assert stream)
  (okbc-assert
   (open-p connection) ()
   "Connection ~S is not open.  You must reestablish the connection."
   connection)
  (let ((persistent-p (eq stream (net-stream connection)))
	(user-id (user-id connection))
	(session-id (session-id connection))
	(key (key connection))
	(*network-okbc-client-p* t))
    (with-standard-io-syntax
	(if persistent-p
	    (handler-case
	     (emit-network-call-to-persistent-stream
	      stream connection args-to-find-kb-on args query-format)
	     #+Lucid
	     (lucid::file-io-error
	      (condition)
	      (if (equal "Broken pipe"
			 (lucid::file-io-error-osi-message condition))
		  ;;; do a retry if we sense that the stream is broken.
		  (progn (setf (connection-method connection)
			       :connect-using-http-initially)
			 (when (streamp (net-stream connection))
			   (close stream :abort t))
			 (setf (net-stream connection) nil)
			 (initialize-connection connection)
			 (setq stream (net-stream connection))
			 (emit-network-call-to-persistent-stream
			  stream connection args-to-find-kb-on args
			  query-format))
		  (error condition))))
	    (emit-network-call-to-ephemeral-connection
	     stream connection args-to-find-kb-on args query-format
	     reply-format transport-version kb-library user-id session-id key))
      (force-output stream)
      (when persistent-p
	(skip-until-we-hit-the-right-reply-tag stream connection))
      (let ((*connection* connection))
	(declare (special *connection*))
	(actually-read-and-return-nokbc-reply-values 
	 stream reply-format transport-version)))))

(defmacro with-checking-reply-value ((index arg string) &body body)
  (let ((error-p (intern (format nil "READ-ERROR-~D-P" index) :okbc)))
    `(multiple-value-bind (,arg ,error-p)
      (maybe-ignore-errors
       (values (decode-data-structure-from-stream
		stream reply-format)))
      (if ,error-p
	  (error-on-stream
	   stream
	   ,(concatenate 'string "Some sort of read error occurred reading "
			 string "."))
	  (progn ,@body)))))

(defun actually-read-and-return-nokbc-reply-values 
  (stream reply-format transport-version)
  (with-checking-reply-value (0 vals "reply values")
    (with-checking-reply-value (1 coerce-mask "coercion mask")
      (with-checking-reply-value (2 error-p "error-p flag")
	(with-checking-reply-value (3 status "status")
	  (with-checking-reply-value (4 ok-to-cache-p "ok-to-cache-p flag")
	    (if (string>= transport-version :b)
		(with-checking-reply-value (5 messages "messages")
		  (values vals coerce-mask error-p status ok-to-cache-p
			  messages))
		(values vals coerce-mask error-p status ok-to-cache-p
			nil))))))))

(defun emit-network-call
    (stream connection args-to-find-kb-on
	    args &optional
	    (query-format *default-network-okbc-query-format*)
	    (reply-format *default-network-okbc-reply-format*)
	    (transport-version *default-network-okbc-transport-version*)
	    (kb-library (kb-library connection)))
  (multiple-value-bind (vals coerce-mask error-p status ok-to-cache-p messages)
      (emit-network-call-internal stream connection args-to-find-kb-on args
				  query-format reply-format transport-version
				  kb-library)
    (when messages
      (funcall (notification-callback-function connection) messages))
    (setq *ok-to-cache-p* ok-to-cache-p)
    (if error-p
	(cond ((stringp status) (generic-error "~A" status))
	      ((consp status)
	       (if (find-class (second status))
		   (apply 'error (rest status))
		   (generic-error "~S" status)))
	      (t (generic-error
		  "Some sort of internal error occurred with ~
                    ~S, ~S, ~S, ~S, ~S, ~S"
			vals coerce-mask error-p status ok-to-cache-p
			messages)))
	(progn
	  (loop for index in coerce-mask
		for val = (nth index vals)
		do (setf (nth index vals)
			 (apply (first val)
				(rest val))))
	  (when (typep (first vals) 'network-enumerator)
	    (setf (network-enumerator-creating-args (first vals))
		  args))
	  (values-list vals)))))

(defun error-on-stream (stream string &rest args)
  (let ((lines (loop for line = (with-timeout (2 nil)
				  (fast-read-line stream nil nil))
		     while line collect line)))
    (generic-error
     "~A~%~{~A~^~%~}" (if args (apply 'format nil string args) string)
     lines)))

(defmethod network-kb-p ((instance t)) nil)
(defmethod network-kb-p ((instance network-kb)) t)

(defmethod print-object ((kb network-kb) stream)
  (if (slot-boundp kb 'connection)
      (print-unreadable-object
       (kb stream :type t :identity t)
       (ignore-errors
	(if (eq (connection kb) :ephemeral)
	    (call-next-method)
	    (if (and (abstract-network-connection-p (connection kb))
		     (not (symbolp (net-stream (connection kb)))))
		(format stream "~A on stream ~A:~D"
			(name kb) (net-stream (connection kb))
			(socket (connection kb)))
		(format stream "~A on ~A"
			(name kb) (connection kb))))))
      (print-unreadable-object
       (kb stream :type t :identity t)
       (or (if (and (slot-boundp kb 'name)
		    #+EXCL
		    (or (name kb)
			(not (eq kb (class-prototype-safe
				     (class-of kb))))))
	       (ignore-errors (princ (name kb) stream))
	       (if (eq kb (class-prototype-safe (class-of kb)))
		   (princ "Prototype" stream)
		   (princ "Uninitialized" stream)))
	   (princ "?????" stream)))))

(defmethod print-object ((kb network-structure-kb) stream)
  (if (connection kb)
      (print-unreadable-object
       (kb stream :type t :identity t)
       (ignore-errors
	(if (eq (connection kb) :ephemeral)
	    (call-next-method)
	    (if (and (abstract-network-connection-p (connection kb))
		     (not (symbolp (net-stream (connection kb)))))
		(format stream "~A on stream ~A:~D"
			(name kb) (net-stream (connection kb))
			(socket (connection kb)))
		(format stream "~A on ~A"
			(name kb) (connection kb))))))
      (print-unreadable-object
       (kb stream :type t :identity t)
       (or (if (and (name kb)
		    #+Lucid
		    (not (equal 0 (name kb)))
		    #+EXCL
		    (or (name kb)
			(not (eq kb (class-prototype-safe
				     (class-of kb))))))
	       (ignore-errors (princ (name kb) stream))
	       (if (eq kb (class-prototype-safe (class-of kb)))
		   (princ "Prototype" stream)
		   (princ "Uninitialized" stream)))
	   (princ "?????" stream)))))




;==============================================================================
;;; Add these method to override the default method on (symbol kb)
(defmethods call-procedure-internal
    ((procedure symbol) (kb network-kb) arguments)
  (make-network-call kb 'nil 'call-procedure-internal procedure kb
		     arguments))

(defmethods call-procedure-internal
    ((procedure procedure) (kb network-kb) arguments)
  (make-network-call kb 'nil 'call-procedure-internal procedure kb
		     arguments))

(defmethods register-procedure-internal
    ((name symbol) (procedure procedure) (kb network-kb))
  (make-network-call kb 'nil 'register-procedure-internal name
		     procedure kb))

(defmethods unregister-procedure-internal ((name symbol) (kb network-kb))
  (make-network-call kb 'nil 'unregister-procedure-internal name kb))

(defmethods get-procedure-internal ((name symbol) (kb network-kb))
  (make-network-call kb 'nil 'get-procedure-internal name kb))

(defmethods get-kbs-of-type-internal
    ((kb-type (network-kb network-structure-kb)) (connection local-connection))
  (let ((abstract-name (abstract-kb-class-name-from-kb kb-type)))
    (loop for kb in *network-okbc-kbs*
	  when (and (find-class abstract-name nil) (typep kb abstract-name))
	  collect kb)))

(defmethod find-kb-of-type-internal :around
  (name-or-kb (kb-type network-kb) (connection local-connection))
  (let ((name (if (kb-p name-or-kb)
		  (if (slot-boundp name-or-kb 'name)
		      (name name-or-kb)
		      nil)
		  name-or-kb)))
    (or (and name
	     (loop for match = (find name *network-okbc-kbs* :key 'name)
		   when (not match) return nil
		   when match
		   do (let ((con (connection match)))
			(if (open-p con)
			    (return match)
			    (progn (warn "Deleting reference to zombie ~
                                          network KB ~S on closed connection."
					 name)
				   (setq *network-okbc-kbs*
					 (remove match
						 *network-okbc-kbs*)))))))
	(call-next-method))))

(defmethod openable-kbs-internal
    ((kb-type network-kb) (connection t) (place t))
  nil)

(defmethod openable-kbs-internal
    ((kb-type network-kb) (connection abstract-network-connection) (place t))
  (make-network-call-from-connection
   connection '(0)
   'openable-kbs-internal kb-type
   :__establish-local-connection place))

(defmethod get-package-and-name-internal
    ((kb-type network-kb) (filename t) (connection t))
  nil)

(defmethod create-kb-internal
    (name (kb-type network-kb) (kb-locator t) (initargs t)
	  (connection abstract-network-connection))
  (let ((local-init-keys '(:connection)))
    (let ((filtered (loop for (key value) on initargs by #'cddr
			  unless (member key local-init-keys :test #'eq)
			  append (list key value))))
      (let ((instance
	     (make-network-call-from-connection
	      connection '(1) 'create-kb-internal name
	      (if (eq (type-of-name kb-type) 'network-kb)
		  `(okbc:get-kb-type :default)
		  `(okbc:get-kb-type
		    (concrete-kb-class-from-abstract-kb-class-name
		     ,(abstract-kb-class-name-from-kb kb-type))))
	      kb-locator
	      (cons :name (cons name filtered))
	      :__establish-local-connection)))
	instance))))

(defmethod get-all-kb-kb-types-internal
    ((connection abstract-network-connection))
  ;; Extra remove duplicates here because multiple leaf classes on the
  ;; server side might map into a single superclass's abstract type.
  (remove-duplicates
   (make-network-call-from-connection
    connection nil 'get-all-kb-kb-types-internal
    :__establish-local-connection)))

(defmethod get-kb-type-internal ((thing symbol) 
				 (connection abstract-network-connection))
  (make-network-call-from-connection
   connection nil 'get-kb-type-internal
   thing :__establish-local-connection))

;==============================================================================

;;; Abstract Connections.

(defmacro check-plist-then-slot (slot &optional (default nil specified-p))
  `(or (getf plist ,(intern (string slot) :keyword))
    (and (slot-boundp connection ',slot)
     (slot-value connection ',slot))
    ,(if specified-p
	 default
	 `(generic-error ,(format nil "Error no ~A specified" slot)))))

(defmethod ok-back:find-connection-key
    append ((connection abstract-network-connection) &rest plist)
    `(:host ,(check-plist-then-slot host)
      :port ,(check-plist-then-slot port)
      :kb-library ,(check-plist-then-slot kb-library
					  *default-network-okbc-kb-library*)))

(defmethod abstract-network-connection-p ((thing t)) nil)

(defmethod abstract-network-connection-p
  ((thing abstract-network-connection)) t)

(defmethod kb-library ((thing t)) *default-network-okbc-kb-library*)

(defmethod get-kbs-of-type-internal
    ((kb-type network-kb) (connection abstract-network-connection))
  (make-network-call-from-connection
   connection '(0)
   'get-kbs-of-type-internal
   `(okbc:get-kb-type (concrete-kb-class-from-abstract-kb-class-name
		       ,(abstract-kb-class-name-from-kb kb-type)))
   :__establish-local-connection))


(defmethod shared-initialize :after
  ((instance network-kb) (slots t) &rest inits)
  (declare (ignore inits))
  ;; Don't record the class kb-type
  (when (slot-boundp instance 'name)
    (pushnew instance *network-okbc-kbs*)))

(defmethod abstract-kb-class-name-from-kb ((instance network-kb))
  (if (eq 'network-kb (type-of-name instance))
      nil ;; we are abstract
      (slot-value instance 'abstract-name)))

(defmethod slot-unbound
    ((class standard-class) (instance network-kb)
     (slot-name (eql 'abstract-name)))
  (let ((name (string (class-name class))))
    (intern (concatenate 'string "ABSTRACT-"
			 (subseq name 0 (- (length name)
					   (length "-NETWORK-KB")))
			 "-KB")
	    :okbc)))

(defmethod close-kb-internal :after ((kb network-kb) (save-p t))
	   nil)

(defmethod save-kb-as-internal :after ((new-name-or-locator t) (kb network-kb))
  ;; Rename the local stub of the KB to match the one at the other end.
  (when (or (symbolp new-name-or-locator) (stringp new-name-or-locator)
	    (quasi-symbol-p new-name-or-locator))
    (setf (name kb) new-name-or-locator)))

(defmethod get-frame-name-internal
    ((frame symbol) (kb network-kb) (kb-local-only-p t))
  frame)

;==============================================================================

;;; Simple Connections.

(defmethod shared-initialize
    :after ((connection simple-network-connection) (slot-names t) 
	    &rest args)
    (declare (ignore args))
    (make-nokbc-stream connection)
    (setf (open-p connection) t))

(defmethod (setf connection-method)
    ((new-value t) (connection simple-network-connection))
  nil)

(defmethod connection-method ((connection simple-network-connection))
  :persistent)

(defmethod user-id ((connection simple-network-connection)) nil)

(defmethod session-id ((connection simple-network-connection)) nil)

(defmethod key ((connection simple-network-connection)) nil)

(defmethod close-connection-internal 
    ((connection abstract-network-connection) (force-p t) (error-p t))
  (flet ((do-it ()
	   (loop for kb in (copy-list *network-okbc-kbs*)
		 when (eq connection (connection kb))
		 do (setf (connection kb)
			  (okbc:local-connection))
		 (setq *network-okbc-kbs* (remove kb *network-okbc-kbs*)))
	   (ignore-errors
	    (emit-network-call-to-persistent-stream 
	     (net-stream connection) connection nil '(:disconnect) :portable)
	    (close (net-stream connection) :abort t)
	    (setf (net-stream connection) :closed))
	     (format t "~%;;; Closed simple-network-connection ~S"
		     connection)))
    (ok-utils:with-timeout (5 nil) (do-it))))

(defmethod close-connection-internal :before
    ((connection abstract-network-connection) (force-p t) (error-p t))
 ;; flush out any enumerators associated with this connection.
 (maphash #'(lambda (key enumerator)
	      (when (and (network-enumerator-p enumerator)
			 (eq connection (connection enumerator)))
		(unwind-protect
		     (ok-utils:with-timeout (5 nil)
		       (ignore-errors (free-remote-enumerator enumerator)))
		  (remhash key *enumerator-id-to-enumerator-table*))))
	  *enumerator-id-to-enumerator-table*))


(defmethod initialize-connection ((connection simple-network-connection))
  nil)

(defun make-nokbc-stream (connection)
  (let ((ok-p nil)
	(sock nil)
	(stream nil)
	(host (host connection))
	(port (port connection)))
    (unwind-protect
	 (progn #+Lucid
		(progn
		  (setq sock (connect-socket host port))
		  (when (equal -1 sock)
		    (error 'network-connection-error
			   :host host :port port))
		  (setf stream
			(make-lisp-stream :input-handle sock
					  :output-handle sock
					  :auto-force NIL)))
		#+MCL (setq stream
			    (ccl::open-tcp-stream
			     host port :commandtimeout
			     *mcl-command-timeout*))
		#+Harlequin-Common-Lisp
		(setq stream (comm:open-tcp-stream host port
						   :direction :io
						   :element-type 'base-char))
                #+Allegro
	        (progn #-(and allegro-version>= (version>= 5))
		       (setq stream 
			     (ipc:open-network-stream :host host :port port))
		       #+(and allegro-version>= (version>= 5))
		       (setq stream
			     (socket:make-socket :remote-host host
						 :remote-port port)))
		#-(or Lucid MCL Allegro Harlequin-Common-Lisp)
		(generic-error "Implement me")
		(multiple-value-bind (res mask er status ok-to-cache-p
					  messages)
				     (emit-connection-establishing-request
				      stream connection)
		  (declare (ignore res mask er ok-to-cache-p))
		  (when messages
		    (funcall (notification-callback-function connection)
			     messages))
		  (when (eq :ok status)
		    (setq ok-p t)
		    (setf (connection-method connection) :persistent)
		    (setf (net-stream connection) stream))
		  connection))
      (when (and (not ok-p) #-MCL sock #-MCL (not (equal -1 sock)))
	#+Lucid (disconnect-socket sock)
	#+(or MCL Allegro Harlequin-Common-Lisp)
	(when stream (close stream))
	#-(or Lucid MCL Allegro Harlequin-Common-Lisp)
	(generic-error "Implement me"))
      connection)))

(defmethod emit-connection-establishing-request 
    (stream (connection simple-network-connection))
  (encode-data-structure-to-stream
   (list :query-format :portable
	 :reply-format :portable
	 :transport-version 
	 *default-network-okbc-transport-version*
	 :kb-library (kb-library connection))
   stream
   :portable)
  (force-output stream)
  (terpri stream)
  (actually-read-and-return-nokbc-reply-values
   stream :portable *default-network-okbc-transport-version*))


;==============================================================================

(defmethod ok-back:next-internal :around ((enumerator enumerator))
  (when (and (inside-okbc-server-p) (not (current-kb)))
    (setq *current-kb* (enumerator-associated-kb enumerator)))
  (call-next-method))

(defmethod ok-back:has-more-internal :around ((enumerator enumerator))
  (when (and (inside-okbc-server-p) (not (current-kb)))
    (setq *current-kb* (enumerator-associated-kb enumerator)))
  (call-next-method))

(defmethod ok-back:prefetch-internal :around
    ((enumerator enumerator) (number-of-values t) (increment t))
  (when (and (inside-okbc-server-p) (not (current-kb)))
    (setq *current-kb* (enumerator-associated-kb enumerator)))
  (call-next-method))

(defmethod ok-back:free-internal :around ((enumerator enumerator))
  (when (and (inside-okbc-server-p) (not (current-kb)))
    (setq *current-kb* (enumerator-associated-kb enumerator)))
  (call-next-method))

(defmethod ok-back:fetch-internal :around
    ((enumerator enumerator) (number-of-values t))
  (when (and (inside-okbc-server-p) (not (current-kb)))
    (setq *current-kb* (enumerator-associated-kb enumerator)))
  (call-next-method))


;;; Enumerator support

(defun list-to-enumerator (list)
  (if (listp list)
      (make-exhaustive-enumerator
       :all-elements list)
      (continuable-error "~S is not as list" list)))

(defmethod enumerator-has-more :before ((enumerator enumerator))
  (continuable-assert (not (enumerator-freed enumerator)) object-freed
		      :object enumerator))

(defmethod enumerator-has-more
    ((enumerator exhaustive-enumerator))
  (not (null (exhaustive-enumerator-all-elements enumerator))))

(defmethod enumerator-has-more ((enumerator network-enumerator))
  (or (> (network-enumerator-number-of-local-elements enumerator) 0)
      (and (not (network-enumerator-remote-exhausted-p enumerator))
	   (remote-has-more enumerator))))

(defun remote-has-more (enumerator)
  (let ((result (make-network-call-from-connection
		 (network-enumerator-connection enumerator)
		 'nil 'has-more-internal enumerator)))
    (when (not result)
      ;; We have exhausted it, so free the remote enumerator.
      (free-remote-enumerator enumerator))
    (setf (network-enumerator-remote-exhausted-p enumerator)
	  (not result))
    result))


(defmethod enumerator-prefetch :before
  ((enumerator enumerator) (number-of-values t) (increment t))
  (continuable-assert (not (enumerator-freed enumerator)) object-freed
		      :object enumerator)
  (continuable-assert (or (eq number-of-values :all)
			  (and (integerp number-of-values)
			       (> number-of-values 0)))
		      () "Illegal number-of-values.  Number-Of-Valuess must ~
                          be :ALL, or a positive integer.")
  (continuable-assert (or (member increment '(nil :all))
			  (and (integerp increment) (> increment 0)))
		      () "Illegal increment.  Increments must be NIL, :ALL, ~
                          or a positive integer."))

(defmethod enumerator-prefetch
    ((enumerator exhaustive-enumerator) (number-of-values t) (increment t))
  nil)

(defmethod enumerator-prefetch
    ((enumerator network-enumerator) (number-of-values t) (increment t))
  (setf (network-enumerator-last-prefetch-increment enumerator)
	(or increment
	    (network-enumerator-last-prefetch-increment enumerator)))
  (if (network-enumerator-remote-exhausted-p enumerator)
      nil
      (if (or (eq :all number-of-values)
	      (> number-of-values (network-enumerator-number-of-local-elements
				   enumerator)))
	  (if (remote-has-more enumerator)
	      (let ((results (make-network-call-from-connection
			      (network-enumerator-connection enumerator)
			      'nil 'fetch-internal enumerator
			      (case increment
				(:all :all)
				((nil) number-of-values)
				(otherwise increment)))))
		(setf (network-enumerator-local-elements enumerator)
		      (append (network-enumerator-local-elements enumerator)
			      results))
		(setf (network-enumerator-number-of-local-elements enumerator)
		      (+ (network-enumerator-number-of-local-elements
			  enumerator)
			 (length results)))
		(when (eq number-of-values :all)
		  (free-remote-enumerator enumerator)
		  (setf (network-enumerator-remote-exhausted-p enumerator) t)))
	      nil)
	  nil)))

(defmethod enumerator-free :before ((enumerator enumerator))
  (continuable-assert (not (enumerator-freed enumerator)) object-freed
		      :object enumerator))

(defmethod enumerator-free
    ((enumerator exhaustive-enumerator))
  (setf (exhaustive-enumerator-all-elements enumerator) nil))

(defun free-remote-enumerator (enumerator)
  (make-network-call-from-connection (network-enumerator-connection enumerator)
				     'nil 'free-internal enumerator))

(defmethod enumerator-free ((enumerator network-enumerator))
  (when (not (network-enumerator-remote-exhausted-p enumerator))
    (free-remote-enumerator enumerator)))

(defmethod enumerator-free :after ((enumerator enumerator))
  (remhash (enumerator-id enumerator) *enumerator-id-to-enumerator-table*)
  (setf (enumerator-freed enumerator) t))

(defmethod enumerator-free :after ((enumerator network-enumerator))
  (setf (network-enumerator-remote-exhausted-p enumerator) t)
  (setf (network-enumerator-connection enumerator) nil)
  (setf (network-enumerator-last-prefetch-increment enumerator) nil))

(defmethod enumerator-next :before ((enumerator enumerator))
  (continuable-assert (not (enumerator-freed enumerator)) object-freed
		      :object enumerator))

(defmethod enumerator-next
    ((enumerator exhaustive-enumerator))
  (if (enumerator-has-more enumerator)
      (pop (exhaustive-enumerator-all-elements enumerator))
      (error 'enumerator-exhausted :enumerator enumerator)))

(defmethod enumerator-next ((enumerator network-enumerator))
  (if (> (network-enumerator-number-of-local-elements enumerator) 0)
      (progn (decf (network-enumerator-number-of-local-elements enumerator))
	     (pop (network-enumerator-local-elements enumerator)))
      (progn (okbc-assert
	      (not (network-enumerator-local-elements enumerator)) ()
	      "Internal consistency error!  Value(s) found in ~
               network enumerator, but value count indicates that ~
               there should be none.")
	     (if (network-enumerator-remote-exhausted-p enumerator)
		 (error 'enumerator-exhausted :enumerator enumerator)
		 (let ((inc (network-enumerator-last-prefetch-increment
			     enumerator)))
		   ;; We've snagged the number the user last asked for.
		   ;; We'll heuristically use this as a cue to tell us how
		   ;; many values to get this time.
		   (if inc
		       ;; Heuristic prefetch
		       (progn
			 (prefetch-internal enumerator inc inc)
			 (if (> (network-enumerator-number-of-local-elements
				 enumerator) 0)
			     ;; We know that we got a local value, so
			     ;; try again.
			     (enumerator-next enumerator)
			     (error 'enumerator-exhausted :enumerator
				    enumerator)))
		       (make-network-call-from-connection
			(network-enumerator-connection enumerator)
			'nil 'next-internal enumerator)))))))

(defmethod enumerator-fetch :before
  ((enumerator enumerator) (number-of-values t))
  (continuable-assert (not (enumerator-freed enumerator)) object-freed
		      :object enumerator)
  (continuable-assert (or (eq number-of-values :all)
			  (and (integerp number-of-values)
			       (> number-of-values 0)))
		      () "Illegal number-of-values.  Number-Of-Valuess must ~
                          :ALL, or a positive integer."))

(defmethod enumerator-fetch
    ((enumerator exhaustive-enumerator) (number-of-values t))
  (if (enumerator-has-more enumerator)
      (if (eq :all number-of-values)
	  (let ((values (exhaustive-enumerator-all-elements enumerator)))
	    (setf (exhaustive-enumerator-all-elements enumerator) nil)
	    values)
	  (loop for i from 0 below number-of-values
		while (enumerator-has-more enumerator)
		collect (pop (exhaustive-enumerator-all-elements enumerator))))
      (error 'enumerator-exhausted :enumerator enumerator)))

(defmethod enumerator-fetch
    ((enumerator network-enumerator) (number-of-values t))
  (cond ((eq :all number-of-values)
	 (if (network-enumerator-remote-exhausted-p enumerator)
	     (if (> (network-enumerator-number-of-local-elements enumerator) 0)
		 (progn (setf (network-enumerator-number-of-local-elements
			       enumerator)
			      0)
			(let ((res (network-enumerator-local-elements
				    enumerator)))
			  (setf (network-enumerator-local-elements enumerator)
				nil)
			  res))
		 (error 'enumerator-exhausted :enumerator enumerator))
	     (let ((extra (make-network-call-from-connection
			   (network-enumerator-connection enumerator)
			   'nil 'fetch-internal enumerator number-of-values))
		   (existing (network-enumerator-local-elements enumerator)))
	       (free-remote-enumerator enumerator)
	       (setf (network-enumerator-remote-exhausted-p enumerator) t)
	       (setf (network-enumerator-local-elements enumerator) nil)
	       (setf (network-enumerator-number-of-local-elements enumerator)
		     0)
	       (append existing extra))))
	((> number-of-values
	    (network-enumerator-number-of-local-elements enumerator))
	 (let ((extra (make-network-call-from-connection
		       (network-enumerator-connection enumerator)
		       'nil 'fetch-internal enumerator
		       (- number-of-values
			  (network-enumerator-number-of-local-elements
			   enumerator))))
	       (existing (network-enumerator-local-elements enumerator)))
	   (setf (network-enumerator-local-elements enumerator) nil)
	   (setf (network-enumerator-number-of-local-elements enumerator)
		 0)
	   (append existing extra)))
	(t (loop for i from 0 below number-of-values
		 collect (pop (network-enumerator-local-elements enumerator))
		 do (decf (network-enumerator-number-of-local-elements
			   enumerator))))))