(in-package :ok-kernel)

;-----------------------------------------------------------------
;                        Conditions
;-----------------------------------------------------------------

(eval-when #-(or TI LUCID ALLEGRO-V3.1 ALLEGRO-V3.2)
	   (:load-toplevel :compile-toplevel :execute)
	   #+(or TI LUCID ALLEGRO-V3.1 ALLEGRO-V3.2)
	   (compile load eval)

  (defparameter *non-lisp-define-condition-okbc-options* '(:java-report-body))
  (defparameter *define-condition-okbc-options-to-transform*
    '((:report transform-report)
      (:documentation transform-condition-doc-string)))

  (defun okbc-condition-common (name slots)
    `((defmethod okbc-condition-p-internal ((thing ,name)) t)
      (defmethod decode-okbc-condition ((condition ,name))
	(with-condition-slots
	    (,@(mapcar #'first slots)) condition
	    (list ,@(loop for (slot-name . slot-plist) in slots
			  for initarg = (getf slot-plist :initarg)
			  append (list (or initarg
					   (intern (string slot-name)
						   :keyword))
				       slot-name)))))))

  (defun transform-condition-doc-string (name string)
    (values (detex string)
	    `((defmethod raw-documentation ((name (eql ',name))) ,string))))
  
  (defun transform-report (name report-body)
    (declare (ignore name))
    (destructuring-bind (lambda (condition stream) &body body) report-body
	`(,lambda (,condition ,stream)
	  ,(if (is-in-tree 'okbc:error-message body)
	       `(with-condition-slots (okbc:error-message) condition ,@body)
	       `(with-condition-slots (okbc:error-message) condition
		 (if (stringp okbc:error-message)
		     (format stream "~A" okbc:error-message)
		     (progn ,@body)))))))
	  
  (defun filter-options (condition-name options)
    (let ((extra-forms nil))
      (values
       (loop for x in options
	     when (or (not (consp x))
		      (not (member (first x)
				   *non-lisp-define-condition-okbc-options*)))
	     collect
	     (if (consp x)
		 (let ((entry
			(assoc (first x)
			       *define-condition-okbc-options-to-transform*)))
		   (if entry
		       (multiple-value-bind (result extras)
			   (funcall (second entry) condition-name (second x))
			 (setq extra-forms (append extras extra-forms))
			 (list (first x) result))
		       x))
		 x))
       extra-forms)))
  
  (defun validate-define-condition-args (slots options)
    "Used to check args to DEFINE-CONDITION-ONTO for portability."
    (loop for (slot-name . slot-plist) in slots
	  for initarg = (getf slot-plist :initarg) do 
	  (remf slot-plist :initarg)
	  (remf slot-plist :initform)
	  (when slot-plist
	    (error "For portability reasons, only :INITARGS and :INITFORM ~
		    slot options are allowed in OL condition slot specs."))
	  (when (and initarg
		     (not (string= (symbol-name initarg)
				   (symbol-name slot-name))))
	    (error "For portability reasons, the :INITARG of an OL condition ~
		    slot may only be the keyword corresponding to the ~
		    slot name.")))
    (loop for key in (append '(:report :documentation)
			     *non-lisp-define-condition-okbc-options*)
	  do (setf options (remove key options :key #'first)))
    (when options
      (error "For portability reasons, only :DOCUMENTATION and :REPORT ~
	      options are allowed in OL condition definitions.")))

(defun record-condition (name slots)
  (setq *all-okbc-conditions*
	(cons (cons name
		    (loop for (slot-name . slot-plist) in slots
			  for initarg = (getf slot-plist :initarg)
			  collect (or initarg
				      (intern (string slot-name)
					      :keyword))))
	      (remove (assoc name *all-okbc-conditions*)
		      *all-okbc-conditions*))))

(defparameter *all-files-defining-okbc-conditions* nil)

(defun record-condition-source-file ()
  (let ((source-path (current-source-file)))
    (when source-path
      (let ((true (namestring (or (ignore-errors (truename source-path))
				  source-path))))
	(when (not (member true
			   *all-files-defining-okbc-conditions*
			   :test #'string=))
	  (push true *all-files-defining-okbc-conditions*)))))))

#-LUCID
(defmacro ok-utils:define-condition-okbc
    (name (parent-type) &optional slots &rest options)
  "Hook for LISPS that don't have CLOS conditions.  Since we do have CLOS
   conditions, this just expands into DEFINE-CONDITION."
  (validate-define-condition-args slots options)
  (ensure-api-symbol-ok name :okbc)
  (loop for spec in slots
	for slot = (first-if-list spec)
	do (ensure-api-symbol-ok slot :okbc))
  (multiple-value-bind
      (filtered extra-forms) (filter-options name options)
      (let ((doc nil)
	    (without-doc nil))
	;; Handle franz bug of dropping class docs.
	#-Allegro (setq without-doc filtered)
	#+Allegro
	(loop for opt in filtered
	      do (if (or (not (consp opt))
			 (not (eq :documentation (first opt))))
		     (push opt without-doc)
		     (setq doc (second opt))))
	`(progn
	  (record-condition ',name ',slots)
	  ,@extra-forms
	  (record-condition-source-file)
	  (define-condition
	      ,name (,parent-type) ,slots
	      ;; Changed by JPR on 1-Oct-98.  Used to be filtered.
	      ,@without-doc)
	  ,@(if doc `((defdoc ,name (type) ,doc)) nil)
	  ,@(okbc-condition-common name slots)))))

#-LUCID
(defmacro ok-utils:with-condition-slots (slots instance-form &body body)
  "Hook for LISPS that don't have CLOS conditions.  Since we do have CLOS
   conditions, this just expands into a WITH-SLOTS."
  (loop for slot in slots
	do (ensure-api-symbol-ok slot :okbc))
  `(with-slots ,slots ,instance-form
     ,@body))

#+LUCID
(defmacro ok-utils:define-condition-okbc
    (name (parent-type) &optional slots &rest options)
  "Like CL:DEFINE-CONDITION (accepts CLOS style slot specs.)"
  (validate-define-condition-args slots options)
  (ensure-api-symbol-ok name :okbc)
  (loop for spec in slots
	for slot = (first-if-list spec)
	do (ensure-api-symbol-ok slot :okbc))
  (multiple-value-bind (filtered extra-forms) (filter-options name options)
    `(progn (export ',name :okbc)
      (record-condition ',name ',slots)
      ,@extra-forms
      (record-condition-source-file)
      (define-condition ,name (,parent-type)
	,(loop for (slot-name . slot-plist) in slots
	       for initform = (getf slot-plist :initform)
	       collect (if initform
			   (list slot-name initform)
			   slot-name))
	,@filtered)
      ,@(okbc-condition-common name slots))))

#+LUCID
(defmacro ok-utils:with-condition-slots (slots instance-form &body body)
  "Like WITH-SLOTS, but works with condition objects."
  (let ((instance-var (gensym))
	(conc-name-var (gensym)))
    (loop for slot in slots
	  do (ensure-api-symbol-ok slot :okbc))
    `(let* ((,instance-var ,instance-form)
	    (,conc-name-var (symbol-name (get (type-of ,instance-var)
					      'system:conc-name)))
	    ,@(mapcar
	       #'(lambda (slot-name)
		   `(,slot-name
		     (funcall (intern (concatenate 'string
						   ,conc-name-var
						   ,(symbol-name slot-name))
			       ;; Conditions are all defined in the OKBC
			       ;; package, so are the slots.
			       :ok-kernel)
		      ,instance-var)))
	       slots))
      ,@body)))

(defokbcfun okbc:continuable-error-p (thing)
  (:manual-category :condition
   :returned-values boolean)
  "Returns \\true\\ if \\karg{thing} is a continuable error, and \\false\\
   otherwise.  An error is said to be continuable only if the state of the KB
   is known not to have been damaged by the error in such a way that the
   behavior of subsequent OKBC operations becomes undefined.  Thus, although
   the signalling of a continuable error will interrupt any processing
   currently being performed, subsequent OKBC calls will be well defined.
   After a noncontinuable error, the state of the KB and the behavior of the
   KRS and application are undefined."
  (continuable-error-p-1 thing))

;==============================================================================


(define-condition-okbc okbc:abstract-error (error)
  ((error-message :initarg :error-message :initform nil)
   (continuable   :initarg :continuable   :initform nil))
  (:documentation "The abstract OKBC error condition.  \\karg{Error-message}
   is a string to print out for the error.  If the error is not so severe that
   processing with the KB will have undefined results, \\karg{continuable}
   is \\true.  This is the abstract superclass of OKBC errors.  No
   unspecialized instances of this error type will ever be signaled.")
  (:report (lambda (condition stream)
	     (format stream "~A" error-message)))
  (:java-report-body "[" error-message "]"))

(defmethod continuable-error-p-1 ((thing t)) nil)

(defmethod continuable-error-p-1 ((thing okbc:abstract-error))
  (with-condition-slots (continuable) thing continuable))

(define-condition-okbc okbc:cannot-handle (okbc:abstract-error)
  ((sentence :initarg :sentence))
  (:documentation "The condition signaled when a \\kfn{tell} is performed on
   a \\karg{sentence} that cannot be handled.")
  (:report (lambda (condition stream)
	     (with-condition-slots (sentence) condition
				   (format stream "Cannot handle sentence ~S"
					   sentence))))
  (:java-report-body "Cannot handle sentence [" sentence "]"))

(define-condition-okbc okbc:constraint-violation (okbc:abstract-error)
  ((constraint :initarg :constraint)
   (frame :initarg :frame)
   (slot :initarg :slot)
   (slot-type :initarg slot-type)
   (facet      :initarg :facet)
   (kb :initarg :kb))
  (:documentation
   "The condition signaled when a value stored in a slot or facet violates a 
    constraint on that slot.")
  (:report
   (lambda (condition stream)
     (with-condition-slots
	 (slot frame kb constraint) condition
	 (format stream
		 "Violation of constraint ~A in slot ~A in frame ~A in kb ~A"
		 constraint slot frame (name kb)))))
  (:java-report-body
   "Violation of constraint " constraint " in slot " slot " in frame " frame
   " in " kb))

(define-condition-okbc okbc:cardinality-violation (okbc:constraint-violation)
  ()
  (:documentation
   "The condition signaled when a value stored in a slot violates a cardinality
    constraint on that slot.")
  (:report
   (lambda (condition stream)
     (with-condition-slots (slot frame kb constraint)
       condition
       (format stream "Violation of cardinality constraint ~A in slot ~A in ~
                       frame ~A in kb ~A"
	       constraint slot frame (name kb)))))
  (:java-report-body
   "Violation of cardinality constraint " constraint " in slot " slot
   " in frame " frame " in " kb
   |(constraint!=null? \".  \" + constraint:"")|))

(define-condition-okbc okbc:class-not-found (okbc:abstract-error)
  ((missing-class :initarg :missing-class)
   (kb :initarg :kb))
  (:documentation
   "The condition signaled on reference to a \\karg{missing-class} that is not
    defined.")
  (:report
   (lambda (condition stream)
     (with-condition-slots (missing-class kb) condition
       (format stream "Class ~A not found in kb ~A"
	       missing-class (name kb)))))
  (:java-report-body "Class " missing-class " not found in " kb))

(define-condition-okbc okbc:domain-required (okbc:abstract-error)
  ((frame :initarg :frame)
   (slot :initarg :slot)
   (facet :initarg :facet)
   (kb :initarg :kb))
  (:documentation "The condition signaled when an attempt is made to create
   a slot or facet with an unconstrained domain in an KRS that does not support
   unconstrained slot (or facet) domains.")
  (:report (lambda (condition stream)
	     (format stream "Domain required when creating a slot or facet")))
  (:java-report-body "Domain required when creating a slot or facet"))

(define-condition-okbc okbc:enumerator-exhausted (okbc:abstract-error)
  ((enumerator :initarg :enumerator))
  (:documentation "The condition signaled when an enumerator is exhausted, 
   and an attempt is made to get a value from it.")
  (:report (lambda (condition stream)
	     (with-condition-slots (enumerator) condition
				   (format stream "Enumerator ~S is exhausted"
					   enumerator))))
  (:java-report-body "Enumerator " enumerator " is exhausted"))

(define-condition-okbc okbc:facet-already-exists (okbc:abstract-error)
  ((facet :initarg :facet)
   (kb :initarg :kb))
  (:documentation
   "The condition signaled on an attempt to create a facet that already 
    exists.")
  (:report
   (lambda (condition stream)
     (with-condition-slots (facet kb) condition
			   (format stream "Facet ~A already exists in KB ~A"
				   facet (name kb)))))
  (:java-report-body "Facet " facet " already exists in " kb))

(define-condition-okbc okbc:facet-not-found (okbc:abstract-error)
  ((frame :initarg :frame)
   (slot :initarg :slot)
   (slot-type :initarg :slot-type)
   (facet :initarg :facet)
   (kb :initarg :kb))
  (:documentation
   "The condition signaled on reference to a nonexistent facet.")
  (:report
   (lambda (condition stream)
     (with-condition-slots (facet slot frame kb) condition
       (format stream "Facet ~A not found on slot ~A in frame ~A of kb ~A"
	       facet slot frame (name kb)))))
  (:java-report-body "Facet " facet " not found on slot " slot " in frame "
		     frame " of " kb))

(define-condition-okbc okbc:frame-already-exists (okbc:abstract-error)
  ((frame :initarg :frame)
   (kb :initarg :kb))
  (:documentation
   "The condition signaled on an attempt to create a frame that already 
    exists.  This error is signaled only when the
    {\\tt :frame-names-required} behavior is active.")
  (:report
   (lambda (condition stream)
     (with-condition-slots (frame kb) condition
			   (format stream "Frame ~A already exists in KB ~A"
				   frame (name kb)))))
  (:java-report-body "Frame " frame " already exists in " kb))

(define-condition-okbc okbc:generic-error (okbc:abstract-error)
  ()
  (:documentation "The generic OKBC error condition.
   This error is signaled when no more specific and appropriate error type
   can be found.")
  (:report (lambda (condition stream)
	     (format stream "~A" error-message)))
  (:java-report-body "[" error-message "]"))

;; This class need the error message unlike most of them.
(defmethod decode-okbc-condition :around ((condition okbc:generic-error))
  (let ((rest (call-next-method)))
    (with-condition-slots (error-message) condition
			  (append (list :error-message error-message) rest))))

(define-condition-okbc okbc:illegal-behavior-values (okbc:abstract-error)
  ((behavior :initarg :behavior)
   (proposed-values :initarg :proposed-values))
  (:documentation "The condition signaled when an application attempts to
   set illegal behavior values.  \\karg{Proposed-values} are the values
   that the application is attempting to set for the behavior.")
  (:report (lambda (condition stream)
	     (with-condition-slots
		 (behavior proposed-values) condition
		 (format stream "Illegal values ~S for behavior ~A"
			 proposed-values behavior))))
  (:java-report-body "Illegal values [" proposed-values "] for behavior "
		     behavior))

(define-condition-okbc okbc:individual-not-found (okbc:abstract-error)
  ((missing-individual :initarg :missing-individual)
   (kb :initarg :kb))
  (:documentation
   "The condition signaled on reference to a \\karg{missing-individual}
    that is not defined.")
  (:report
   (lambda (condition stream)
     (with-condition-slots (missing-individual kb) condition
       (format stream "Individual ~A not found in kb ~A"
	       missing-individual (name kb)))))
  (:java-report-body "Individual " missing-individual " not found in " kb))

(define-condition-okbc okbc:kb-not-found (okbc:abstract-error)
  ((kb :initarg :kb))
  (:documentation
   "The condition signaled on reference to a nonexistent \\karg{kb}.")
  (:report
   (lambda (condition stream)
     (with-condition-slots (kb) condition
       (format stream "KB ~A not found"
	       kb))))
  (:java-report-body "KB " kb " not found"))

(define-condition-okbc okbc:kb-value-read-error (okbc:abstract-error)
  ((read-string :initarg :read-string)
   (kb          :initarg :kb))
  (:documentation
   "The condition signaled on read errors.  \\karg{Read-string} is the string
    from which the KB value is being read.  See \\kfn{coerce-to-kb-value}.")
  (:report
   (lambda (condition stream)
     (with-condition-slots (read-string kb) condition
       (format stream
	       "A read error occurred whilst reading from \"~A\" in KB ~A"
	       read-string (name kb)))))
  (:java-report-body
   "A read error occurred whilst reading from [" read-string "] in " kb))

(define-condition-okbc okbc:method-missing (okbc:abstract-error)
  ((okbcop :initarg :okbcop)
   (kb :initarg :kb))
  (:documentation
   "The condition signaled on reference to a nonhandled method for a OKBC
    operation.  \\karg{Okbcop} is the name of the operation in question.
    This error is signaled when a OKBC back end detects either that it is not
    compliant, or that is has been called in a manner that is inconsistent
    with its advertized capabilities, according to the value of the
    {\\tt :compliance} behavior.")
  (:report
   (lambda (condition stream)
     (with-condition-slots (okbcop kb) condition
       (format stream "Method missing for ~S in kb ~A"
	       okbcop (name kb)))))
  (:java-report-body "Method missing for " okbcop " in " kb))

(define-condition-okbc okbc:missing-frames (okbc:abstract-error)
  ((missing-frames :initarg :missing-frames)
   (frame :initarg :frame)
   (kb :initarg :kb))
  (:documentation "The condition signaled by \\kfn{copy-frame} when
   \\karg{missing-frame-action} is either {\\tt :stop} or {\\tt :abort}
   and \\karg{error-p} is \\true, and frames are found to be missing.
   \\kcond{Missing-frames} is the list of missing
   frames.")
  (:report (lambda (condition stream)
	     (with-condition-slots (frame) condition
	       (format stream "Missing frames whilst copying ~S" frame))))
  (:java-report-body "Missing frames whilst copying [" frame "]"))

(define-condition-okbc okbc:network-connection-error (okbc:abstract-error)
  ((host :initarg :host)
   (port :initarg :port))
  (:documentation "The error signaled when OKBC fails to make a network
    connection.  \\karg{Host} is the host to which it is trying to connect,
    and \\karg{port} is the port number.")
  (:report (lambda (condition stream)
	     (with-condition-slots (host port) condition
	       (format stream "Cannot connect to ~A:~A" host port))))
  (:java-report-body "Cannot connect to " host ":" port))

(define-condition-okbc okbc:not-a-frame-type (okbc:abstract-error)
  ((frame-type :initarg :frame-type)
   (kb :initarg :kb))
  (:documentation
   "The condition signaled on an attempt to create an entity supplying
    frame-like arguments (such as \\karg{own-slots}) in a KRS that does
    not represent entities of that frame-type as frames.")
  (:report
   (lambda (condition stream)
     (with-condition-slots (frame-type kb) condition
       (format stream
	       "Entities of frame-type ~A are not represented as frames ~
                in KB ~A"
	       frame-type (name kb)))))
  (:java-report-body "Entities of frame-type " frame-type
		     " are not represented as frames in " kb))

(define-condition-okbc okbc:not-coercible-to-frame (okbc:abstract-error)
  ((frame :initarg :frame)
   (kb :initarg :kb))
  (:documentation
   "The condition signaled on an attempt to coerce an object to a frame that 
    does not identify a frame.")
  (:report
   (lambda (condition stream)
     (with-condition-slots (frame kb) condition
       (format stream "Object ~A is not coercible to a frame for KB ~A"
	       frame (name kb)))))
  (:java-report-body "Object " frame " is not coercible to a frame for " kb))

(define-condition-okbc okbc:not-unique-error (okbc:abstract-error)
  ((pattern :initarg :pattern)
   (matches :initarg :matches)
   (context :initarg :context)
   (kb      :initarg :kb))
  (:documentation
   "The condition signaled when a match operation has nonunique results.
    \\karg{Pattern} is the pattern given to the completion operation
    (e.g., \\kfn{coerce-to-kb-value}).
    \\karg{Matches} is the list of matches.
    \\karg{Context} is the context type expected, e.g. {\\tt :slot}.")
  (:report
   (lambda (condition stream)
     (with-condition-slots (pattern matches kb context) condition
       (format stream
	       "Pattern \"~A\" does not uniquely identify a ~A in KB ~A.  ~
                It matches ~{~S~^, ~}."
	       pattern context (name kb) matches))))
  (:java-report-body
   "Pattern [" pattern "] does not uniquely identify a " context " in " kb
   ".  It matches " matches "."))

(define-condition-okbc okbc:object-freed (okbc:abstract-error)
  ((object :initarg :object))
  (:documentation "The condition signaled when possible when a user accesses
   a freed data structure.  \\karg{Object} is the object being accessed.")
  (:report (lambda (condition stream)
	     (with-condition-slots (object) condition
	       (format stream "~S has been freed" object))))
  (:java-report-body "[" object "] has been freed"))

(define-condition-okbc okbc:read-only-violation (okbc:abstract-error)
  ((kb :initarg :kb))
  (:documentation
   "The condition signaled upon a read-only violation on a read-only KB.")
  (:report (lambda (condition stream)
	     (format stream "~A" error-message)))
  (:java-report-body "[" error-message "]"))

;; This class need the error message unlike most of them.
(defmethod decode-okbc-condition :around ((condition okbc:read-only-violation))
  (let ((rest (call-next-method)))
    (with-condition-slots (error-message) condition
			  (append (list :error-message error-message) rest))))

(define-condition-okbc okbc:slot-already-exists (okbc:abstract-error)
  ((slot :initarg :slot)
   (kb :initarg :kb))
  (:documentation
   "The condition signaled on an attempt to create a slot that already 
    exists.")
  (:report
   (lambda (condition stream)
     (with-condition-slots (slot kb) condition
			   (format stream "Slot ~A already exists in KB ~A"
				   slot (name kb)))))
  (:java-report-body "Slot " slot " already exists in " kb))

(define-condition-okbc okbc:slot-not-found (okbc:abstract-error)
  ((frame :initarg :frame)
   (slot :initarg :slot)
   (slot-type :initarg :slot-type)
   (kb :initarg :kb))
  (:documentation
   "The condition signaled on reference to a \\karg{slot} that is not
    defined in \\karg{frame}.")
  (:report
   (lambda (condition stream)
     (with-condition-slots (slot frame kb) condition
       (format stream "Slot ~A not found in frame ~A of kb ~A"
	       slot frame (name kb)))))
  (:java-report-body "Slot " slot " not found in frame " frame " of " kb))

(define-condition-okbc okbc:syntax-error (okbc:abstract-error)
  ((erring-input :initarg :erring-input))
  (:documentation "The condition signaled when a syntax error is detected
   in KIF input.  \\karg{Erring-input} is either a string containing 
   the erring input, or a malformed KIF input.")
  (:report (lambda (condition stream)
	     (with-condition-slots (erring-input) condition
				   (format stream "Syntax error in [~S]"
					   erring-input))))
  (:java-report-body "Syntax error in [" erring-input "]"))

(define-condition-okbc okbc:value-type-violation (okbc:constraint-violation)
  ()
  (:documentation
   "The condition signaled when a value being stored in a slot violates a 
    {\\tt :value-type} constraint on that slot.")
  (:report
   (lambda (condition stream)
     (with-condition-slots (slot frame kb constraint)
       condition
       (format stream "Violation of valuetype constraint ~A in slot ~A in ~
                       frame ~A in kb ~A"
	       constraint slot frame (name kb)))))
  (:java-report-body
   "Violation of valuetype constraint " constraint " in slot " slot
   " in frame " frame " in " kb
   |(constraint!=null? \".  \" + constraint:"")|))

