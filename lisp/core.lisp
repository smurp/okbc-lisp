;;; -*- MODE :Lisp; Syntax:Common-Lisp; Package:OK-kernel; Base:10  -*- 

(in-package :ok-kernel)

(defvar *allow-interpreted-global-assignments-p* nil)
(defvar *unbound-variable-eval-hook* nil)
;; These are used in the translation to C to index the callbacks for Franz.
(defvar *lisp_callback_index_offset* 2000)
(defvar *lisp_callback_extension_index_offset* 3000)

;-----------------------------------------------------------------
;                          Queueing Functions
;-----------------------------------------------------------------

(defun make-queue ()
  "Return a new queue, with no elements."
  (let ((q (cons nil nil)))
    (setf (car q) q)))

(defun enqueue (item q)
  "Insert ITEM at the end of the queue Q. Return Q."
  (setf (car q)
        (setf (rest (car q))
              (cons item nil)))
  q)

(defun dequeue (q)
  "Remove an item from the front of the queue.  Return Q."
  (pop (cdr q))
  (if (null (cdr q)) (setf (car q) q))
  q)

(defun empty-queue-p (q)
  "True if a queue is empty."
  (null (queue-contents q)))

(defun queue-contents (q)
  "Return the list of Q's contents."
  (cdr q))

(defun queue-front (q)
  "Return the element at the front of the Q, or NIL if empty."
  (first (queue-contents q)))

(defun queue-back (q)
  "Return the element at the back of the Q (most recently added), or NIL
if empty."
  (if (eq q (car q))
      nil
      (car (car q))))

(defun queue-nconc (q list)
  "Add the elements of LIST to the end of the queue.  Return Q."
  (setf (car q)
        (last (setf (rest (car q)) list)))
  q)

(defun queue-append (q list)
  "Add the elements of LIST to the end of the queue.  Return Q."
  (setf (car q)
        (last (setf (rest (car q)) (copy-list list))))
  q)

(defun clear-queue (q)
  "Flushes a queue."
  (setf (car q) q)
  (setf (cdr q) nil)
  q)

(defun queue-delete (q x &key count)
  "Delete the item x from the q."
  (if (eql x (queue-back q))
      (setf (car q)
	    (last (nbutlast q)))
      (setf (cdr q)
	    (delete x (cdr q) :count count)))
  q)

;-----------------------------------------------------------------
;                          Mapping Functions
;-----------------------------------------------------------------

;; Note that since all frames are coerced to frame-objects in functions
;; such as get-kb-frames, get-kb-classes, etc., they have in fact
;; been referenced, so these functions do need monitor-bodies that iterate
;; over all frames.  Does this sound right? -- SMP

;;; The following methods enshrine the official naming convention for
;;; OKBC kb component classes.

(defmethods abstract-kb-class-name-from-kb
    ((instance (kb structure-kb)))
  (let ((class (clos::class-of instance)))
    ;; The class must have been finalized to have been instantiated so we can
    ;; safely call CPL
    (let ((cpl (clos::class-precedence-list class)))
      (loop for c in cpl
	    for name = (clos::class-name c)
	    for string = (symbol-name name)
	    when (and (> (length string)
			 (+ (length "ABSTRACT-") (length "-KB")))
		      (string= "ABSTRACT-" string :end2 (length "ABSTRACT-"))
		      (string= "-KB" string :start2
			       (- (length string) (length "-KB"))))
	    return name))))

;;; When this returns NIL, a network implementation is at liberty to create
;;; a network-*-kb surrogate.
(defmethod concrete-kb-class-from-abstract-kb-class-name ((name t))
  nil)

;;; Note: In the new defokbcop macro, positional args that are not in the
;;; standard set of args that always have the same type interpretation
;;; (e.g., frame or slot) are decorated with a type specifier so that the
;;; right thing happens with frame coercion.  For example, a positional
;;; arg that is spelled (name :value) says that the Name arg is to be
;;; subject to the :value context type coercion and will therefore not
;;; be COERCE-TO-FRAMEd before the call gets to the back end
;;; (assuming you have #+okbc-frame-coercion turned on).

(defokbcfun okbc:local-connection ()
  (:returned-values connection
   :manual-category :connection)
  "Returns a connection to the local OKBC implementation."
  (establish-connection-internal 'local-connection nil))

(defokbcfun okbc:connection-p (thing)
  (:returned-values boolean
   :manual-category :connection)
  "Is \\true\\ if \\karg{thing} is a connection, and \\false\\ otherwise."
  (okbc-connection-p thing))

(defun kb-object (name-or-kb &key (error-p t))
  (let ((kb (find-kb-internal name-or-kb (okbc:local-connection))))
    (if (and error-p (not kb))
	(cerror "Go ahead anyway"
		"~A is not a valid KB name or locator" name-or-kb)
	kb)))

(defmethod connection-arg-default ((kb-type kb) &optional (default nil))
  (if (slot-boundp kb-type 'connection)
      (or (let ((c (connection kb-type)))
	    (and c (okbc-connection-p c) c))
	  default
	  (okbc:local-connection))
      (or default (okbc:local-connection))))

(defmethod connection-arg-default
    ((kb-type structure-kb) &optional (default nil))
  (or (let ((c (connection kb-type)))
	(and c (okbc-connection-p c) c))
      default
      (okbc:local-connection)))

(defun get-frame-facets (frame kb inference-level slot-type kb-local-only-p)
  (let ((all-facets nil)
	(inexact-p nil))
    (multiple-value-bind (slots exact-p)
	(get-frame-slots-internal
	 frame kb inference-level slot-type kb-local-only-p)
      (when (not exact-p) (setq inexact-p t))
      (loop with facets = nil
	    with exact-p = nil
	    for slot in slots
	    do (multiple-value-setq (facets exact-p)
		 (get-slot-facets-internal
		  frame slot kb :all-inferable slot-type
		  kb-local-only-p))
	    (when (not exact-p) (setq inexact-p t))
	    do (setq all-facets (union all-facets facets)))
      (values all-facets (not inexact-p)))))

(defmethod print-object ((object kb) stream)
  "Print KBs with their names."
  (print-unreadable-object (object stream :type t :identity t)
     (or (if (and (slot-boundp object 'name)
		  #+EXCL
		  (or (name object)
		      (not (eq object (class-prototype-safe
				       (class-of object))))))
	     (ignore-errors (princ (name object) stream))
	     (if (eq object (class-prototype-safe (class-of object)))
		 (princ "Prototype" stream)
		 (princ "Uninitialized" stream)))
	 (princ "?????" stream))
     (when (and (slot-boundp object 'kb-has-been-modified-p)
		(kb-modified-p-internal object))
       (format stream " (Unsaved)"))))

(defmethod print-object ((object structure-kb) stream)
  "Print KBs with their names."
  (print-unreadable-object (object stream :type t :identity t)
     (or (if (and (name object)
		  #+Lucid
		  (not (equal 0 (name object)))
		  #+EXCL
		  (or (name object)
		      (not (eq object (class-prototype-safe
				       (class-of object))))))
	     (ignore-errors (princ (name object) stream))
	     (if (eq object (class-prototype-safe (class-of object)))
		 (princ "Prototype" stream)
		 (princ "Uninitialized" stream)))
	 (princ "?????" stream))
     (when (kb-modified-p-internal object) (format stream " (Unsaved)"))))


(defmacro ok-back:with-current-kb (kb &rest body)
  "A macro that binds the <code>current-KB</code> to the specified KB and
   executes the <code>body</code> in that context."
  `(let ((.kb. ,kb)
	 (.the-current-kb. (current-kb)))
    (let ((*current-kb* .kb.))
      (flet ((.body. () ,@body))
	(cond ((not (eq .kb. .the-current-kb.))
	       (ok-back:goto-kb-internal .kb.)
	       (unwind-protect (.body.)
		 (when .the-current-kb.
		   (ok-back:goto-kb-internal .the-current-kb.))))
	      (t (.body.)))))))

(defun get-collection-type (frame slot kb slot-type kb-local-only-p)
  (or (get-facet-value-internal frame slot :collection-type kb :all-inferable
				slot-type :either  kb-local-only-p)
      (first (get-behavior-values-internal :collection-types kb))
      :set))  ;; make :set the default if none specified

(defvar *closure*) ;; note:  these _*must*_ be globally unbound.  JPR
(defvar *closure-table*)
(defvar *inexact-p*)

;; global resource.  Only accessed in thread-safe code.  JPR.
(defvar *closure-table-resource* nil) 

(defun allocate-closure-table ()
  (or (let ((table (without-scheduling (pop *closure-table-resource*))))
	(when table (clrhash table))
	table)
      (make-hash-table)))

(defun deallocate-closure-table (table)
  (without-scheduling (push table *closure-table-resource*)))

; In the initial version of this function, a new hashtable was created
; for each non-recursive call.  That was found to be much slower than
; re-using the same table, and clearing it as being done now.
;;; See JPR comment inside..

;(defun member-frame-list (frame frame-list kb)
;  (unless (symbolp frame)
;    (setq frame (get-frame-handle-internal frame kb)))
;  (loop for f in frame-list
;        thereis
;        (or (and (symbolp f)
;                 (eq f frame))
;            (eql frame (get-frame-handle-internal f kb))
;            ))
;  )

(defun member-frame-list (frame frame-list kb kb-local-only-p)
  (multiple-value-bind (real-frame found-p)
      (coerce-to-frame-internal frame kb nil kb-local-only-p)
    (when found-p (setq frame real-frame)))
  (loop for f in frame-list
	thereis
	(eql-in-kb-internal f frame kb kb-local-only-p)))

(defun maybe-trim-values-to-return-internal
    (all-values kb number-of-values kb-local-only-p known-more-status)
  (if (or (eq known-more-status :more) (numberp known-more-status))
      ;; Then an inferior has already limited the number of values,
      ;; so just return them.
      (values all-values known-more-status)
      (let ((unique-all-values
	     (if (rest all-values)
		 (remove-duplicates-using-trie-and-coercion
		  all-values (maybe-coerce-to-frame-fun kb kb-local-only-p))
		 all-values)))
	(let ((len (length unique-all-values)))
	  (if (> len number-of-values)
	      (values (firstn number-of-values unique-all-values)
		      (- len number-of-values))
	      (values unique-all-values nil))))))

(defun ok-utils:initialize-slots-and-facets
    (frame kb slot-specs facet-specs slot-type kb-local-only-p
	   &optional (defined-slot-alist nil) (defined-facet-alist nil))
  "This function takes a <code>frame</code> and a set of specifications
   for slots and facets of the given <code>slot-type</code> in the format
   used for <code>create-frame</code> and <code>put-frame-details</code>.
   It initializes the frame and fills in all necessary slot and facet values,
   creating and attaching any necessary slots and facets.<P>

   Returns a pair of lists:
   <OL>
   <LI><code>defined-slot-alist</code> - an alist each element of which is
   of the form <code>(slot-identification slot)</code>.  The initial value
   of this returned value is the <code>defined-slot-alist</code> argument.
   One entry will be added to this list for every slot that is created
   during the processing of this function.
   <LI><code>defined-facet-alist</code> - an alist each element of which is
   of the form <code>(facet-identification facet)</code>.  The initial value
   of this returned value is the <code>defined-facet-alist</code> argument.
   One entry will be added to this list for every facet that is created
   during the processing of this function.
   </OL>
   These returned values and argumentsd are used when this function is used
   repeatedly to initialize a large number of frames such as whilst loading
   a KB to make sure that multiple slots and facets are not created for the
   same name."
  (loop for slot-spec in slot-specs
	for slot = (first-if-list slot-spec)
	for values = (if (consp slot-spec) (rest slot-spec) nil)
	do (setq slot (or (second (assoc slot defined-slot-alist))
			  (let ((s (maybe-create-slot frame slot slot-type kb
						      kb-local-only-p)))
			    (push (list slot s) defined-slot-alist)
			    s)))
	when values
	do (let ((monotonic nil)
		 (default nil))
	     (loop for val in values
		   do (if (and (consp val) (eq :default (first val)))
			  (push (second val) default)
			  (push val monotonic)))
	     (when monotonic
	       (put-slot-values-internal frame slot monotonic kb
					 slot-type :known-true
					 kb-local-only-p))
	     (when default
	       (if (get-behavior-values-internal :defaults kb)
		   (put-slot-values-internal frame slot default kb
					     slot-type :default-only
					     kb-local-only-p)
		   (warn "Cannot assert default slot values for ~S because ~
                          defaults are not supported in KB ~S"
			 frame (name kb))))))
  (loop for slot-spec in facet-specs
	for slot = (first-if-list slot-spec)
	for facet-specs = (if (consp slot-spec) (rest slot-spec) nil)
	do (setq slot (or (second (assoc slot defined-slot-alist))
			  (let ((s (maybe-create-slot frame slot slot-type kb
						      kb-local-only-p)))
			    (push (list slot s) defined-slot-alist)
			    s)))
	do (loop for facet-spec in facet-specs
		 for facet = (first-if-list facet-spec)
		 for values = (if (consp facet-spec) (rest facet-spec) nil)
		 do (setq facet (or (second (assoc facet defined-facet-alist))
				    (let ((fa (maybe-create-facet
					       frame slot facet slot-type kb
					       kb-local-only-p)))
				      (push (list facet fa)
					    defined-facet-alist)
				      fa)))
		 when values
		 do (let ((monotonic nil)
			  (default nil))
		      (loop for val in values
			    do (if (and (consp val) 
					(eq :default (first val)))
				   (push (second val) default)
				   (push val monotonic)))
		      (when monotonic
			(put-facet-values-internal
			 frame slot facet monotonic kb slot-type :known-true
			 kb-local-only-p))
		      (when default
			(if (get-behavior-values-internal :defaults kb)
			    (put-facet-values-internal
			     frame slot facet default kb slot-type
			     :default-only kb-local-only-p)
			    (warn "Cannot assert default facet values for ~S ~
                                   because defaults are not supported in KB ~S"
				  frame (name kb)))))))
  (values defined-slot-alist defined-facet-alist))

(defun add-to-slots-and-facets
    (frame kb slot-specs facet-specs slot-type kb-local-only-p test
	   &optional (defined-slot-alist nil) (defined-facet-alist nil))
  "Like initialize-slots-and-facets, only it just adds new stuff."
  (loop for slot-spec in slot-specs
	for slot = (first-if-list slot-spec)
	for values = (if (consp slot-spec) (rest slot-spec) nil)
	do (setq slot (or (second (assoc slot defined-slot-alist))
			  (let ((s (maybe-create-slot frame slot slot-type kb
						      kb-local-only-p)))
			    (push (list slot s) defined-slot-alist)
			    s)))
	when values
	do (let ((monotonic nil)
		 (default nil))
	     (loop for val in values
		   do (if (and (consp val) (eq :default (first val)))
			  (push (second val) default)
			  (push val monotonic)))
	     (loop for value in monotonic
		   do (add-slot-value-internal frame slot value kb test
					       slot-type 0 :known-true
					       kb-local-only-p))
	     (loop for value in default
		   do (if (get-behavior-values-internal :defaults kb)
			  (add-slot-value-internal frame slot value kb test
						    slot-type 0 :default-only
						    kb-local-only-p)
			  (warn "Cannot assert default slot values for ~
                                 ~S because defaults are not supported ~
                                 in KB ~S"
				frame (name kb))))))
  (loop for slot-spec in facet-specs
	for slot = (first-if-list slot-spec)
	for facet-specs = (if (consp slot-spec) (rest slot-spec) nil)
	do (setq slot (or (second (assoc slot defined-slot-alist))
			  (let ((s (maybe-create-slot frame slot slot-type kb
						      kb-local-only-p)))
			    (push (list slot s) defined-slot-alist)
			    s)))
	do (loop for facet-spec in facet-specs
		 for facet = (first-if-list facet-spec)
		 for values = (if (consp facet-spec) (rest facet-spec) nil)
		 do (setq facet (or (second (assoc facet defined-facet-alist))
				    (let ((fa (maybe-create-facet
					       frame slot facet slot-type kb
					       kb-local-only-p)))
				      (push (list facet fa)
					    defined-facet-alist)
				      fa)))
		 when values
		 do (let ((monotonic nil)
			  (default nil))
		      (loop for val in values
			    do (if (and (consp val) 
					(eq :default (first val)))
				   (push (second val) default)
				   (push val monotonic)))
		      (loop for value in monotonic
			    do (add-facet-value-internal
				frame slot facet value kb test slot-type
				:known-true kb-local-only-p))
		      (loop for value in default
			    do (if (get-behavior-values-internal :defaults kb)
				   (add-facet-value-internal
				    frame slot facet value kb test slot-type
				    :default-only kb-local-only-p)
				   (warn "Cannot assert default facet values ~
                                          for ~S because defaults are not ~
                                          supported in KB ~S"
					 frame (name kb)))))))
  (values defined-slot-alist defined-facet-alist))

(defun maybe-create-slot
    (frame slot slot-type kb kb-local-only-p &optional (handle nil))
  (when (or (not (slot-p-internal (or handle slot) kb kb-local-only-p))
	    (and (member :slot (get-behavior-values-internal :are-frames kb))
		 (not (coercible-to-frame-p-internal
		       (or handle slot) kb kb-local-only-p))))
    (if (symbolp slot)
	(setq handle
	      (create-slot-internal
	       slot kb frame slot-type nil nil nil nil handle
	       nil kb-local-only-p))
	(multiple-value-bind (sframe found-p)
	    (coerce-to-slot-internal (or handle slot) kb nil kb-local-only-p)
	  (if found-p
	      (setq handle sframe)
	      (setq handle
		    (create-slot-internal
		     (if handle
			 slot
			 (let ((name
				(if found-p
				    (get-frame-name-internal
				     sframe kb kb-local-only-p)
				    nil)))
			   (if (member nil (get-behavior-values-internal
					    :frame-names-required kb))
			       name
			       (gentemp "TEMP-SLOT-NAME-" :frame-names))))
		     kb frame slot-type nil nil nil nil
		     (or handle (if found-p sframe slot)) nil
		     kb-local-only-p))))))
  (when (and (coercible-to-frame-p-internal frame kb kb-local-only-p)
	     (not (frame-has-slot-p-internal
		   frame (or handle slot) kb
		   :taxonomic  slot-type kb-local-only-p)))
    (attach-slot-internal frame (or handle slot) kb slot-type kb-local-only-p))
  slot)

(defun maybe-create-facet
    (frame slot facet slot-type kb kb-local-only-p &optional (handle nil))
  (when (or (not (facet-p-internal (or handle facet) kb kb-local-only-p))
	    (and (member :facet (get-behavior-values-internal :are-frames kb))
		 (not (coercible-to-frame-p-internal
		       (or handle facet) kb kb-local-only-p))))
    (if (symbolp facet)
	(setq handle
	      (create-facet-internal
	       facet kb frame slot slot-type nil
	       nil nil nil handle nil kb-local-only-p))
	(multiple-value-bind (fframe found-p)
	    (coerce-to-facet-internal (or handle facet) kb nil kb-local-only-p)
	  (if found-p
	      (setq handle fframe)
	      (setq handle
		    (create-facet-internal
		     (if handle
			 facet
			 (let ((name
				(if found-p
				    (get-frame-name-internal
				     fframe kb kb-local-only-p)
				    nil)))
			   (if (member nil (get-behavior-values-internal
					    :frame-names-required kb))
			       name
			       (gentemp "TEMP-FACET-NAME-"
					:frame-names))))
		     kb frame slot slot-type nil nil nil nil
		     (or handle (if found-p fframe facet)) nil
		     kb-local-only-p))))))
  (when (and (coercible-to-frame-p-internal frame kb kb-local-only-p)
	     (not (slot-has-facet-p-internal frame slot (or handle facet) kb
					     :taxonomic  slot-type
					     kb-local-only-p)))
    (attach-facet-internal frame (or handle slot) facet kb slot-type
			   kb-local-only-p))
  facet)

;==============================================================================

;;; Base level protocol support for connections.

(defokbcgeneric ok-back:find-connection-key (connection &rest plist)
  (:method-combination append)
  (:documentation "Canonically orders the <code>plist</code> and/or slots in
   the <code>connection</code> object to make a key for
   <code>find-connection</code>"))

(defmethod ok-back:find-connection-key :around
  ((connection ok-back:connection) &rest plist)
  (declare (ignore plist))
  (let ((result (call-next-method)))
    (cons (class-name (class-of connection)) result)))

(defmethod ok-back:find-connection-key append
  ((connection ok-back:connection) &rest plist)
 (declare (ignore plist))
 nil)

(defun ok-back:default-notification-callback-function
    (arg &optional (stream *trace-output*))
  "A default implementation of the <code>notification-callback-function</code>
   on <code>connection</code>s.  It simply prints out the value of
   <code>arg</code> to the specified <code>stream</code>."
  (typecase arg
    (cons (loop for x in arg
		do (default-notification-callback-function x stream)
		(terpri stream)))
    (string (format stream "~%;;; ~A" arg))
    (otherwise (format stream "~%;;; ~S" stream))))

(defun ok-cache:cache-entry-found-p (cache key kb)
  "This function is called by the caching substrate to see whether a cache
   entry can be found for a particular <code>key</code> in the
   <code>cache</code>.  If no cache entry is found it returns false.  If a 
   cache entry is found, it returns two values: true, and the cache node for
   that key.  The current cached value(s) can be extracted from this cache node
   using <code>tries:hybrid-trie-value</code>.  Note that if this cache
   entry is for an operation returns multiple values, then the value in the
   cache will be the list of values, otherwise it will be just a singleton
   value."
  (if ok-cache:*allow-okbc-caching-p*
      (let ((allow-p (ok-cache:allow-caching-p kb)))
	(case allow-p
	  (:ephemeral
	   (if (boundp 'ok-cache:*ephemeral-cache*)
	       (let ((cache ok-cache:*ephemeral-cache*))
		 (multiple-value-bind (result found-p trie-node)
		     (get-hybrid-trie-returning-node key cache)
		   (declare (ignore result))
		   (values found-p trie-node)))
	       (let ((ok-cache:*ephemeral-cache*
		      (new-root-hybrid-trie
		       :okbc-cache nil)))
		 (let ((cache ok-cache:*ephemeral-cache*))
		   (multiple-value-bind (result found-p trie-node)
		       (get-hybrid-trie-returning-node key cache)
		     (declare (ignore result))
		     (values found-p trie-node))))))
	  ((t) (multiple-value-bind (result found-p trie-node)
		   (get-hybrid-trie-returning-node key cache)
		 (declare (ignore result))
		 (values found-p trie-node)))
	  (otherwise nil)))
      nil))

(defun encache
    (value multiple-values-p cache key kb &optional (num-expected-values nil))
  (when multiple-values-p
    (assert (and (integerp num-expected-values)
		 (> num-expected-values 1))
	    () "Wrong value for num-expected-values argument"))
  (if ok-cache:*allow-okbc-caching-p*
      (let ((allow-p (ok-cache:allow-caching-p kb))
	    (value-to-cache
	     (if multiple-values-p
		 (if (and (consp value) (eq :values (first value)))
		     (let ((values (rest value)))
		       (assert (= (length values) num-expected-values)
			       () "Encaching the wrong number of values!")
		       values)
		     (let ((list (make-list num-expected-values)))
		       (setf (first list) value)
		       list))
		 value)))
	(case allow-p
	  (:ephemeral
	   (if (boundp 'ok-cache:*ephemeral-cache*)
	       (let ((cache ok-cache:*ephemeral-cache*))
		 (multiple-value-bind (result found-p trie-node)
		     (get-hybrid-trie-returning-node key cache)
		   (declare (ignore result found-p))
		   (set-hybrid-trie-value trie-node value-to-cache)
		   trie-node))
	       (let ((ok-cache:*ephemeral-cache*
		      (new-root-hybrid-trie
		       :okbc-cache nil)))
		 (let ((cache ok-cache:*ephemeral-cache*))
		   (multiple-value-bind (result found-p trie-node)
		       (get-hybrid-trie-returning-node key cache)
		     (declare (ignore result found-p))
		     (set-hybrid-trie-value trie-node value-to-cache)
		     trie-node)))))
	  ((t) (multiple-value-bind (result found-p trie-node)
		   (get-hybrid-trie-returning-node key cache)
		 (declare (ignore result found-p))
		 (set-hybrid-trie-value trie-node value-to-cache)
		 trie-node))
	  (otherwise nil)))
      nil))

(defokbcgeneric ok-cache:cache-miss-hook
    (function key kb)
  (:documentation "This generic function is called every time a cache miss
   is detected for caching KBs such as <code>caching-mixin</code> or
   <code>caching-structure-kb</code>.  <code>Function</code> is the name of the
   OKBC operation being called, and <code>key</code> is the key built from
   the function and its arguments that will be used as the index in the
   cache to store results of the call to the function.  Methods on this
   generic function must return two values:
   <DL>
   <DT>Results<DD>- If the second value is false, the results to be used as if
       they were the results to the call to the operation.  If the second
       value is true,then this value is ignored.
   <DT>Run-operation-p<DD>- True if the system should proceed and call the
       function in question.
   </DL>
   If the operation returns multiple values, then these must all be returned as
   a list, otherwise the cache will be broken.<P>

   This generic function is useful because it allows an application to
   call a compound multi-fetching operation when a cache miss is found
   for a particular operation.  For example, by specializing this generic
   function it is possible to run a call to <code>get-frame-details</code>
   any time a call is made to, for example, <code>get-frame-name</code>.
   This can be very desirable in a networked environment."))

(defmethod ok-cache:cache-miss-hook ((function t) (key t) (kb t))
  (values nil t))

(defokbcgeneric ok-cache:cache-fill-hook
    (function key kb new-results multiple-value-p)
  (:documentation "This generic function is called every time a cache entry
   is inserted for caching KBs such as <code>caching-mixin</code> or
   <code>caching-structure-kb</code>.  <code>Function</code> is the name of the
   OKBC operation being called, and <code>key</code> is the key built from
   the function and its arguments that will be used as the index in the
   cache to store the <code>new-results</code> of the call to the function.
   <code>multiple-value-p</code> will be true when the operation is one that
   returns multiple values.  If this argument is true then the
   <code>new-results</code> are interpreted as the values list."))

(defmethod ok-cache:cache-fill-hook
    ((function t) (key t) (kb t) (new-results t) (multiple-value-p t))
  nil)

;==============================================================================

;;; Stuff for file-mixin and file-kb-locators

;; This is a hook to allow subclasses of file-mixin to instantiate their
;; own subtypes of file-kb-locator.

(defokbcgeneric ok-back:kb-locator-class-for-kb-type (kb-type)
  (:documentation "A hook in the API for <code>file-mixin</code>,
   <code>file-structure-kb</code>, and 
   <code>file-tell&ask-defaults-structure-kb</code> that tells the system
   what KB locator class to use for the back end.  By default,
   <code>file-kb-locator</code> will be used unless this generic function is
   specialized."))

(defmethods ok-back:kb-locator-class-for-kb-type
    ((kb-type (file-mixin file-structure-kb
			  file-tell&ask-defaults-structure-kb)))
  'file-kb-locator)

;; THING should be a plist with the keywords :name, :pathname
;; For example, (:name foo :pathname #p"/home/moss1/chaudhri/a.kb")

(defmethods find-kb-locator-internal
    ((thing file-kb-locator)
     (kb-type (file-mixin file-structure-kb
			  file-tell&ask-defaults-structure-kb))
     (connection t))
  thing)

(defmethods find-kb-locator-internal
    ((thing symbol)
     (kb-type (file-mixin file-structure-kb
			  file-tell&ask-defaults-structure-kb))
     (connection t))
  (let ((type (ignore-errors (get-kb-type-internal thing connection))))
    (and type (find-kb-locator-internal type kb-type connection))))

(defun find-file-kb-locator-internal
    (thing kb-type connection)
  (let ((locators (get-class-instances-internal
		   :kb-locator (meta-kb-internal connection)
		   :taxonomic :all nil)))
    (loop for locator in locators
	  when (and (typep locator 'file-kb-locator)
		    (eq (name locator) (name thing)))
	  return locator
	  finally (return (create-kb-locator-internal
			   thing kb-type connection)))))

(defmethod find-kb-locator-internal
    ((thing file-mixin) (kb-type file-mixin) (connection t))
  (find-file-kb-locator-internal thing kb-type connection))

(defmethods find-kb-locator-internal
    ((thing file-structure-kb) (kb-type file-structure-kb) (connection t))
  (find-file-kb-locator-internal thing kb-type connection))

(defmethods find-kb-locator-internal
    ((thing file-tell&ask-defaults-structure-kb)
     (kb-type file-tell&ask-defaults-structure-kb)
     (connection t))
  (find-file-kb-locator-internal thing kb-type connection))

(defmethods create-kb-locator-internal
    ((thing cons)
     (kb-type (file-mixin
	       file-structure-kb
	       file-tell&ask-defaults-structure-kb))
     (connection t))
  (let ((locator-class-name (kb-locator-class-for-kb-type kb-type)))
    (let ((creator (or (find-symbol
			(concatenate 'string "MAKE-"
				     (string locator-class-name))
			(symbol-package (class-name (class-of kb-type))))
		       (find-symbol
			(concatenate 'string "MAKE-"
				     (string locator-class-name))
			(symbol-package locator-class-name))))
	  (trimmed-args (loop for (key value) on thing by #'cddr
			      when (not (member key '(:name :pathname)))
			      append (list key value))))
      (let ((instance (apply creator
			     :name (or (getf thing :name) (name thing))
			     :kb-type kb-type
			     :pathname (getf thing :pathname)
			     trimmed-args)))
	(put-instance-types-internal instance :kb-locator
				     (meta-kb-internal connection) t)
	instance))))

(defmethods create-kb-locator-internal
    ((thing string)
     (kb-type (file-mixin file-structure-kb
			  file-tell&ask-defaults-structure-kb))
     (connection t))
  (create-kb-locator-internal (pathname thing) kb-type connection))

(defun type-of-name (thing)
  "Returns the name of the type of the <code>thing</code>.  If the
   <code>type-of</code> of <code>thing</code> is a class, it returns the class
   name of that class."
  (let ((type (type-of thing)))
    (if (symbolp type)
	type
	(class-name type))))

(defmethods create-kb-locator-internal
    ((thing pathname)
     (kb-type (file-mixin file-structure-kb
			  file-tell&ask-defaults-structure-kb))
     (connection t))
  (create-kb-locator-internal
   (list :name (intern (string-upcase (pathname-name thing))
		       (symbol-package (type-of-name kb-type)))
	 :pathname thing)
   kb-type connection))

(defmethods create-kb-locator-internal
    ((thing file-kb-locator)
     (kb-type (file-mixin file-structure-kb
			  file-tell&ask-defaults-structure-kb))
     (connection t))
  thing)

;; This hook allows different implementations to have different ways to
;; load from files other than just calling LOAD.
(defokbcgeneric ok-back:load-kb-from-file (pathname kb error-p)
  (:documentation "A piece of internal protocol used by the default methods
   for KB loading and saving defined for <code>file-mixin</code>,
   <code>file-structure-kb</code>, and 
   <code>file-tell&ask-defaults-structure-kb</code>.  Back ends using any
   of these classes that load KBs by means of a function other than
   <code>load</code> should specialize this generic function."))

(defmethods ok-back:load-kb-from-file
    ((pathname t)
     (kb (file-mixin file-structure-kb file-tell&ask-defaults-structure-kb))
     (error-p t))
  (load pathname))

(defmethods open-kb-internal
    ((kb-locator file-kb-locator)
     (kb-type (file-mixin file-structure-kb
			  file-tell&ask-defaults-structure-kb))
     (connection t)
     (error-p t))
  (let ((locator (find-kb-locator-internal kb-locator kb-type connection)))
    (let ((kb (or (find-kb-of-type-internal (name locator)
					    kb-type connection)
		  (create-kb-internal
		   (name locator) kb-type locator nil
		   (local-connection)))))
      (load-kb-from-file (file-kb-locator-pathname kb-locator) kb error-p)
      kb)))

(defmethods close-kb-internal
    ((kb (file-mixin file-structure-kb file-tell&ask-defaults-structure-kb))
     (save-p t))
  (when save-p (save-kb-internal kb t))
  (let ((locator (find-kb-locator-internal kb kb (connection kb))))
    (put-instance-types-internal
     locator nil (meta-kb-internal (connection kb)) t)
    (put-instance-types-internal
     kb nil (meta-kb-internal (connection kb)) t)
    (when (eq kb (current-kb)) (setq *current-kb* nil))))

(defmethods save-kb-as-internal
    ((new-name-or-locator t)
     (kb (file-mixin file-structure-kb file-tell&ask-defaults-structure-kb)))
  (let ((loc (create-kb-locator-internal
	      new-name-or-locator kb (connection kb))))
    (setf (name kb) (name loc))
    (put-frame-name-internal kb (name kb)
			     (meta-kb-internal (connection kb)) t)
    (put-slot-value-internal kb :locator loc
			     (meta-kb-internal (connection kb))
			     :own :known-true t)
    (save-kb-internal kb t)))

(defmethods expunge-kb-internal
    ((kb-locator file-kb-locator)
     (kb-type (file-mixin file-structure-kb
			  file-tell&ask-defaults-structure-kb))
     (connection t) (error-p t))
  (continuable-assert (typep kb-locator 'file-kb-locator) nil
                      "Locator ~S is not of the right type" kb-locator)
  (ignore-errors (delete-file (file-kb-locator-pathname kb-locator))))

(defmethods ok-cache:register-side-effect
 ((kb (kb structure-kb)) &optional (arg nil))
  (declare (ignore arg))
  (when (boundp '*ok-to-cache-p*)
    (setf *ok-to-cache-p* nil)))

;; Will generally be overridden with a read-only-p slot.
(defokbcgeneric ok-utils:read-only-p (kb)
  (:documentation "A predicate that is true if the KB is read-only."))

(defmethods ok-utils:read-only-p ((kb (structure-kb kb))) nil)

;==============================================================================

;; Define a (reasonably) general-purpose loader.

(defun ok-utils:load-okbc-kb
    (pathname &key (kb (current-kb)) 
	      (value-selector :known-true) (kb-local-only-p nil)
	      (action :load) (sentence-action :assert) (language :okbc)
	      (frame-handle-mapping-table nil)
	      (handle-to-name-mapping-table nil)
	      (delayed-sentences nil)
	      (substitute-OKBC-standard-names-p t))
  "Loads the source forms in the file identified by Pathname into the KB.
   The format of the file is a stream of forms according to the grammar
   specified for the <code>language</code>.  Languages based on the OKBC
   model may understand <code>define-okbc-frame</code>forms according to
   the grammar below.<p>

   <code>Load-okbc-kb</code> returns three values:<dl>
   <dt><code>frame-handle-mapping-table</code><dd> a mapping table that maps
   frame names to frame handles.  This is important because it helps to
   preserve EQness of the frame objects allocated from the textual
   representation in the file even if the <code>:frame-names-required</code>
   behavior is not enabled.  The frame handle mapping table returned
   can be passed back in to subsequent calls to <code>load-okbc-kb</code>
   so as to allow multi-file load units that preserve referential integrity.
   <dt><code>handle-to-name-mapping-table</code><dd> a mapping table that maps
   frame handles back to the names used in the source file.
   <dt><code>delayed-sentences</code><dd> a list of structures representing
   any top-level sentences in the load unit that have not yet been asserted
   (see the <code>:sentence-action</code> argument).  These sentences can be
   asserted at some later date by calling
   <code>assert-delayed-sentences</code>.
   </dl>

   Other arguments are as follows:<dl>
   <dt><code>pathname</code><dd> can be a string, pathname, or list of
   pathnames.  Each atom can have wildcards in the places accepted by the
   underlying Lisp for directory listing.
   <dt><code>frame-handle-mapping-table</code><dd> a mapping table of frame
   names to frame handles to be passed in then loading a KB from multiple
   files.  <dt><code>value-selector</code><dd> the value selector to use
   whenever appropriate when asserting knowledge from the source.
   <dt><code>handle-to-name-mapping-table</code><dd> a mapping table of frame
   handles to frame names to be passed in then loading a KB from multiple
   files.
   <dt><code>delayed-sentences</code><dd> a list of delayed sentences being
   passed around whilst loading multiple files
   <dt><code>value-selector</code><dd> the value selector to use
   whenever appropriate when asserting knowledge from the source.
   <dt><code>action</code><dd> a keyword used to inform the implementation of
   the purpose of the call.  Values other than <code>:load</code> are
   KB-specific.  For example, a KB-type might support the action
   <code>:untell</code>, which might allow the block untelling of knowledge
   content by looking at a source file.
   <dt><code>sentence-action</code><dd> a keyword used to control what action
   is performed when top-level sentences are found in the input stream.  In
   some implementations it may be necessary to delay the assertion of the
   sentences or, not even to attempt to assert them.  The legal values of
   this argument are:<dl>
     <dt><code>:assert</code><dd> directly asserts the sentences in the lexical
         order in which they are encountered, as they are encountered.
     <dt><code>:delay</code><dd> delays the assertion of the sentences until
         all other forms have been processed.  The sentences are then asserted
         in the lexical order in which they were found in the input stream.
     <dt><code>:return</code><dd> gathers together all of the top-level
         sentences and simply returns them as the third returned value.
     <dt><code>:ignore</code><dd> simply throws the sentences away.
     </dl>
   <dt><code>language</code><dd> the language dialect for the forms in the
   input stream.  This may be overridden by an (in-language ...) form in
   the input stream.  The default language (<code>:okbc</code>) will
   understand the full KIF 3.0 language (both defining forms and top-level
   sentences) as well as the <code>define-okbc-frame</code> form defined
   below.  The language <code>:okbc-with-ansi-kif</code> is the same as
   <code>:okbc</code> except that it uses ANSI KIF rather than KIF 3.0.
   Note: this means that in <code>:okbc-with-ansi-kif</code> <code>setof</code>
   terms are not permitted.
   </dl>

   All forms not conforming to the grammar of the specified language are
   ignored.  Literal token types are enclosed in &lt;&lt;&gt;&gt;s.  Symbols
   not naming productions are literal symbols:

   <PRE>   forms ::= form &lt;&lt;eof&gt;&gt; | form forms
   form ::= in-package-form | in-language-form | in-kb-form
            | define-okbc-frame-form | kif-language-grammar-form
   in-package-form ::= ( in-package generalized-string )
   in-language-form ::= ( in-language generalized-string )
   in-kb-form ::= ( in-kb generalized-string )
   generalized-string ::= &lt;&lt;string&gt;&gt; | &lt;&lt;symbol&gt;&gt;
   define-okbc-frame-form ::= ( ok-utils:define-okbc-frame frame-name
                              keyword-value-pairs* )
   frame-name ::= generalized-string
   keyword-value-pairs ::= keyword-value-pair |
                           keyword-value-pair keyword-value-pairs
   keyword-value-pair ::= [type-key | direct-types-key
                          | direct-superclasses-key
                          | own-slots-key | template-slots-key
                          | own-facets-key | template-facets-key
                          | sentences-key | kb-key ]
   type-key ::= :frame-type [:class | :slot | :facet | :individual]
   direct-types-key ::= :direct-types ( frame-reference* )
   frame-reference ::= generalized-string |
                       &lt;&lt;frame-handle&gt;&gt; |
                       &lt;&lt;frame-object&gt;&gt;
   direct-superclasses-key ::= :direct-superclasses ( frame-reference* )
   own-slots-key ::= :own-slots ( slot-spec* )
   template-slots-key ::= :template-slots ( slot-spec* )
   slot-spec ::= ( slot-name value-spec* )
   slot-name ::= frame-reference
   value-spec ::= constant | ( SETOF constant* )
                  | ( QUOTE &lt;&lt;lisp-s-expression&gt;&gt; )
                  | ( :DEFAULT value-spec )
   constant ::= &lt;&lt;number&gt;&gt; |
                generalized-string |
                &lt;&lt;frame-handle&gt;&gt; |
                &lt;&lt;frame-object&gt;&gt;
   own-facets-key ::= :own-facets ( own-facets-spec* )
   own-facet-spec ::= ( slot-name facet-component* )
   template-facets-key ::= :template-facets ( template-facets-spec* )
   template-facets-spec ::= ( slot-name facet-component* )
   facet-component ::= ( facet-name value-spec* )
   sentences-key ::= :sentences ( &lt;&lt;KIF-sentence&gt;&gt;* )
   kb-key ::= :kb knowledge-base-ref
   knowledge-base-ref ::= &lt;&lt;knowledge-base&gt;&gt; |
                          generalized-string</PRE>

  Note: The input is interpreted with respect to the KB IO syntax of KB.
  Thus, even if the KB of the form is overridden by the :kb argument, the
  form is still read with respect to the IO syntax of KB.<P>

  When frame-handle-mapping-table is non-null, it is a hash table mapping
  symbols to frame handles.<P>

   If <code>substitute-OKBC-standard-names-p</code> is true then
   non-keywordified versions of OKBC standard names are accepted as if they
   were keywordified.  Thus, the symbol <code>class</code> is taken to denote
   <code>:class</code>.<P>

  Returns the new frame handle mapping table augmented with any newly
  allocated frame handles."

  (let ((language (find-language language)))
    (multiple-value-setq (frame-handle-mapping-table
			  handle-to-name-mapping-table
			  delayed-sentences)
      (execute-in-load-okbc-kb-environment
       pathname kb value-selector kb-local-only-p
       frame-handle-mapping-table
       handle-to-name-mapping-table
       delayed-sentences action
       sentence-action language
       substitute-OKBC-standard-names-p
       #'(lambda ()
	   (if (and (ok-utils:read-all-forms-from-stream-p language)
		    (or (consp pathname)
			(eq :wild (pathname-name pathname))
			(eq :wild (pathname-type pathname))
			(member :wild (pathname-directory pathname))))
	       ;; When we preread all the forms we have to cat all of the files
	       ;; together and process them monolithically, otherwise the
	       ;; processing done in the prereading wouldn't be holistic enough.
	       (let ((temp-path
		      (make-pathname :name (string (gentemp "temp-path"))
				     :defaults
				     (pathname-in-temp-directory))))
		 (unwind-protect
		      (progn
			(with-open-file (str temp-path :direction :output)
			  ;; Cat all of the files together
			  (loop for pattern in (list-if-not pathname)
				do (loop for file in (directory pattern)
					 do (with-open-file
						(instr file :direction :input)
					      (loop for char =
						    (read-char instr nil :eof)
						    until (eq char :eof)
						    do (write-char
							char str))))))
			     (multiple-value-setq
				 (frame-handle-mapping-table
				  handle-to-name-mapping-table 
				  delayed-sentences)
			       (ok-back:load-okbc-kb-internal
				temp-path kb value-selector kb-local-only-p
				frame-handle-mapping-table
				handle-to-name-mapping-table
				delayed-sentences action
				sentence-action language
				substitute-OKBC-standard-names-p)))
		   (ignore-errors (delete-file temp-path))))
	       (loop for pattern in (list-if-not pathname)
		     do (loop for file in (directory pattern)
			      do (multiple-value-setq
				     (frame-handle-mapping-table
				      handle-to-name-mapping-table 
				      delayed-sentences)
				   (ok-back:load-okbc-kb-internal
				    file kb value-selector kb-local-only-p
				    frame-handle-mapping-table
				    handle-to-name-mapping-table
				    delayed-sentences action
				    sentence-action language
				    substitute-OKBC-standard-names-p)))))
	   (values frame-handle-mapping-table
		   handle-to-name-mapping-table
		   delayed-sentences)))))
  (values frame-handle-mapping-table
	  handle-to-name-mapping-table
	  delayed-sentences))

(defmethod execute-in-load-okbc-kb-environment
 ((pathname t) (kb t) (value-selector t) (kb-local-only-p t)
  (frame-handle-mapping-table t) (handle-to-name-mapping-table t)
  (delayed-sentences t) (action t) (sentence-action t) (language t)
  (substitute-OKBC-standard-names-p t) (function t))
 (funcall function))

(defvar *okbc-load-warnings* nil)

(defun maybe-okbc-load-warn (&rest args)
  (when (not (member args *okbc-load-warnings* :test #'equal))
    (push (copy-list args) *okbc-load-warnings*)
    (apply 'warn args)))

(defokbcgeneric ok-back:walk-form-for-interning-given-kb
    (form frame-handle-mapping-table kb kb-local-only-p action language
	  substitute-OKBC-standard-names-p)
  (:method-combination or)
  (:documentation "Internal protocol used by
   <code>load-okbc-kb</code>.  You can define methods for
   <code>walk-form-for-interning-given-kb</code> and for
   <code>assert-form-given-kb</code> in order to handle arbitrary definitional
   forms, such as KIF sentences.  The contract of methods specialized on this
   generic function is to return non-NIL if it successfully recognises and
   walks the form.  Whilst it walks the form it should allocate any necessary
   frame handles for any frame references it finds that are not already found
   in the frame-handle-mapping-table.  The
   <code>substitute-OKBC-standard-names-p</code> argument is passed through
   to <code>intern-frame-handles-if-necessary</code>.<P>

   Note: This generic function uses <code>OR</code> method combination."))

(defmethod ok-back:walk-form-for-interning-given-kb
 or ((form t) (frame-handle-mapping-table t) (kb t) (kb-local-only-p t)
     (action t) (language t) (substitute-OKBC-standard-names-p t))
 (walk-form
  kb
  #'(lambda (kb production known-context-type bound-vars form)
      (intern-frame-handles-if-necessary
       kb production known-context-type bound-vars form language
       frame-handle-mapping-table substitute-OKBC-standard-names-p))
  form
  :production :form
  :symbols-ok-as-non-logical-constants-p t
  :cons-switch :destructive
  :language language))

(defokbcgeneric ok-back:assert-form-given-kb
    (form frame-handle-mapping-table handle-to-name-mapping-table
	  kb value-selector kb-local-only-p action sentence-action language)
  (:documentation "Internal protocol used by
   <code>load-okbc-kb</code>.  You can define methods for
   <code>walk-form-for-interning-given-kb</code> and for
   <code>assert-form-given-kb</code> in order to handle arbitrary definitional
   forms, such as KIF sentences.  The contract of methods specialized on this
   generic function is to return non-NIL if it able successfully to recognise
   and assert the form.  It is the responsibilty of methods that handle forms
   to make any necessary frame handle substitutions by looking in the
   frame-handle-mapping-table.<P>

   Note: This generic function uses <code>OR</code> method combination.")
  (:method-combination or))

(defokbcclass ok-utils:assert-kif-definitions-as-sentences-mixin
    ()
  ()
  (:documentation "When mixed into a KB class provides methods on
 <code>ok-back:assert-form-given-kb</code> that cause KIF defining forms
 to be asserted as the obvious sentential expansion of the forms."))

(defokbcgeneric ok-back:load-okbc-kb-internal
    (pathname kb value-selector kb-local-only-p frame-handle-mapping-table
	      handle-to-name-mapping-table delayed-sentences action
	      sentence-action language substitute-OKBC-standard-names-p)
  (:documentation "Internal protocol used by <code>load-okbc-kb</code> to
   load KBs.  It is passed the pathname to a file containing
   <code>define-okbc-frame</code> forms, and the <code>kb</code> into
   which the frames are to be loaded.  <code>Frame-handle-mapping-table</code>
   is a hash table that is used to map between symbols in the input stream and
   frame handles allocated during the loading process as documented for
   <code>define-okbc-frame</code>.  Implementors may choose to specialize
   this generic function either if the KRS has its own way of handling
   <code>define-okbc-frame</code> forms, or if the file contains forms other
   than just <code>define-okbc-frame</code> forms.  The <code>language</code>
   argument is the same as for <code>walk-form</code>.  If
   <code>substitute-OKBC-standard-names-p</code> is true then non-keywordified
   versions of OKBC standard names are accepted as if they were keywordified.
   Thus, the symbol <code>class</code> is taken to denote
   <code>:class</code>."))

(defokbcgeneric ok-back:load-okbc-kb-from-stream
    (stream kb value-selector kb-local-only-p frame-handle-mapping-table
	      handle-to-name-mapping-table delayed-sentences action
	      sentence-action language substitute-OKBC-standard-names-p)
  (:documentation "Internal protocol used by <code>load-okbc-kb</code> to
   load KBs.  It is called by <code>ok-back:load-okbc-kb-internal</code>, and
   is passed a stream to the KB content rather than the pathname of a file
   containing the relevant content.  All the other arguments are the same as
   for <code>load-okbc-kb-internal</code>."))

(defmethod ok-back:load-okbc-kb-internal :around
 (pathname (kb t) (value-selector t) (kb-local-only-p t)
	   (frame-handle-mapping-table t) (handle-to-name-mapping-table t)
	   (delayed-sentences t) (action t) (sentence-action t)
	   (language t) (substitute-OKBC-standard-names-p t))
 ;; Hook into the implementation's source file recording mechanism just
 ;; in case the KB implementation calls record-source-file-name or some
 ;; such.
 (let ((#.(%pathname-being-loaded) pathname)
       (*okbc-load-warnings* nil))
   (call-next-method)))

(defstruct kb-source-spec
  pathname
  file-write-date
  load-date
  kb) ;; just to be helpful

(defmethod ok-back:load-okbc-kb-internal :after
 (pathname (kb t) (value-selector t) (kb-local-only-p t)
	   (frame-handle-mapping-table t) (handle-to-name-mapping-table t)
	   (delayed-sentences t) (action t) (sentence-action t)
	   (language t) (substitute-OKBC-standard-names-p t))
 ;; Record the source file and load dates of the KB.  Note that there
 ;; can be multiple source files for a given KB, and a given source file
 ;; can be loaded as the source for multiple KBs.
 (let ((current-source-files (getf (plist kb) :source-specs))
       (now (get-universal-time)))
   (let ((entry (or (find pathname current-source-files
			  :key 'kb-source-spec-pathname
			  :test #'equal)
		    (let ((new (make-kb-source-spec :pathname pathname
						    :kb kb)))
		      (push new current-source-files)
		      new))))
     (setf (getf (plist kb) :source-specs) current-source-files)
     (setf (kb-source-spec-file-write-date entry)
	   (file-write-date pathname))
     (setf (kb-source-spec-load-date entry) now))))

(defokbcgeneric load-okbc-kb-handle-in-package-form (form kb language)
  (:documentation "Called by the OKBC loader when it hits an
   <code>in-package</code> form.  The default is to reset *package*, but
   different languages may handle this differently."))

(defmethod load-okbc-kb-handle-in-package-form (form (kb t) (language t))
  (eval `(in-package ,@(rest form))))

(defokbcgeneric load-okbc-kb-handle-in-language-form (form kb language)
  (:documentation "Called by the OKBC loader when it hits an
   <code>in-language</code> form.  The default is to reset the current
   language*, but different languages may handle this differently."))

(defmethod load-okbc-kb-handle-in-language-form
 (form (kb t) (current-language t))
  (declare (special *current-language*))
  (setq *current-language* (find-language (second form))))

(defvar *loading-kb*)
(setf (documentation '*loading-kb* 'variable)
      "Is bound to the KB that is being loaded by the OKBC loader.  This could
       be different from <code>(current-kb)</code>.")
(defvar *current-language*)
(setf (documentation '*current-language* 'variable)
      "Is bound to current language being used by tge OKBC parser.")

(defokbcgeneric load-okbc-kb-handle-in-kb-form (form kb language)
  (:documentation "Called by the OKBC loader when it hits an
   <code>in-kb</code> form.  The default is to reset the current KB, but
   different languages may handle this differently."))

(defmethod load-okbc-kb-handle-in-kb-form (form (kb t) (language t))
  (let ((new-kb (find-kb-of-type-internal
		 (second form) kb (connection kb))))
    (when (not new-kb)
      (continuable-error "Cannot find a KB called ~S of type ~S"
			 (second form) (type-of kb)))
    (setq *loading-kb* new-kb)))

(defokbcgeneric read-form-from-stream-in-language
 (stream eof-value kb action sentence-action language)
  (:documentation "Reads a form from the stream for the parser.  This is
   typically just <code>read</code> (the default), but it may need some sort
   of language-specific reader environment like a readtable.  Note, such
   an environment would in general be different from the IO syntax of the
   KB, since it's expected to be a property of the language, not the KB."))

(defmethod read-form-from-stream-in-language
 ((stream t) (eof-value t) (kb t) (action t) (sentence-action t) (language t))
 (read stream nil eof-value))

(defokbcgeneric reorder-forms-before-asserting-them
 (forms action sentence-action language)
  (:documentation "A back-end hook to allow back ends to reorder the
   definitions in a load unit before they are asserted.  This allows the
   back end to do a topological sort on the forms if there are any
   declare-before-use constraints."))


(defmethod reorder-forms-before-asserting-them
 (forms (action t) (sentence-action t) (language t))
 forms)


(defvar *current-input-file-write-date* nil)

(defmethod ok-back:load-okbc-kb-internal
 (pathname (kb t) value-selector (kb-local-only-p t)
	   (frame-handle-mapping-table t) (handle-to-name-mapping-table t)
	   (delayed-sentences t) (action t) (sentence-action t)
	   (language t) (substitute-OKBC-standard-names-p t))
 (with-open-file (instream pathname :direction :input)
   (let ((*current-input-file-write-date* (file-write-date instream)))
     (ok-back:load-okbc-kb-from-stream
      instream kb value-selector kb-local-only-p frame-handle-mapping-table
      handle-to-name-mapping-table delayed-sentences action sentence-action
      language substitute-OKBC-standard-names-p))))

(defvar *outer-package*)
(setf (documentation '*outer-package* 'variable)
      "Similar to <code>*package*</code>.  Keeps a handle on the current
       package in the OKBC loader.  <code>*package*</code> gets rebound to the
       value of this at the beginning of each load unit.")

(defokbcgeneric read-all-forms-from-stream-p (language)
  (:documentation "Internal protocol for the parser.  This predicate is true
   for any language for which it is essential that all forms be read from the
   input stream in one lump and then processed by the language's reader,
   rather than being parcelled out piecemeal to the parser form-by-form."))

(defmethod read-all-forms-from-stream-p ((language t))
 nil)

(defokbcgeneric read-all-forms-from-stream (stream kb language)
  (:documentation "This is only called for an input stream if
   <code>read-all-forms-from-stream-p</code> is true for this language.
   It reads all of the forms from the input stream and does any
   post-processing that may be necessary before returning a list of forms
   that that is then passsed to the parser.  This is useful for languages
   for which it is not possible to produce complete frame descriptions in
   a single pass."))

(defmethod read-all-forms-from-stream ((stream t) (kb t) (language t))
 (error 'missing-method :okbcop 'read-all-forms-from-stream :kb kb))

(defvar *expression-being-walked*)
(defvar *error-messages-in-this-top-level-form*)

(defmethod ok-back:load-okbc-kb-from-stream
 (instream (kb t) value-selector (kb-local-only-p t)
	   (frame-handle-mapping-table t) (handle-to-name-mapping-table t)
	   (delayed-sentences t) (action t) (sentence-action t)
	   (language t) (substitute-OKBC-standard-names-p t))
 ;; Implement a 2-pass loader.  First go through and allocate all appropriate
 ;; frame handles, then go back over it, substituting the frame handles
 ;; and actually creating the frames.
 (let ((frame-handle-mapping-table
	(or frame-handle-mapping-table (make-hash-table :test #'equal)))
       (*current-language* (find-language language))
       (*loading-kb* kb))
   (assert *current-language* () "Cannot find a language for ~S" language)
   (let ((*package* *package*)
	 (*outer-package* *package*)
	 (*print-readably* nil)
	 (*delayed-sentences* delayed-sentences)
	 (handle-to-name-mapping-table handle-to-name-mapping-table)
	 (all-forms :dont-use-this)
	 (*error-messages-in-this-top-level-form*
	  (make-hash-table :test #'equal))
	 (read-all-forms-p (read-all-forms-from-stream-p language)))
     (declare (special *delayed-sentences*))
     ;; Set package to default for KB
     (implement-with-kb-io-syntax-internal
      #'(lambda () (setq *outer-package* *package*))
      *loading-kb* :file kb-local-only-p)
     (setq *package* *outer-package*)
     (let ((forms nil))
       (when read-all-forms-p
	 (multiple-value-setq (all-forms *loading-kb* *outer-package*
					 *current-language*)
	   (read-all-forms-from-stream instream kb language)))
       (loop
	do
	(implement-with-kb-io-syntax-internal
	 #'(lambda ()
	     (let ((*package* *outer-package*))
	       (let ((form (if read-all-forms-p
			       (if all-forms
				   (pop all-forms)
				   :eof)
			       (read-form-from-stream-in-language
				instream :eof kb action sentence-action
				language))))
		 (when (eq :eof form) (return nil))
		 (push
		  (list
		   *loading-kb*
		   *current-language*
		   (typecase form
		     (cons
		      (typecase (first form)
			(symbol
			 (cond ((string-equal 'in-package (first form))
				(load-okbc-kb-handle-in-package-form
				 form *loading-kb* *current-language*)
				(setq *outer-package* *package*)
				form)
			       ((string-equal 'in-language (first form))
				(load-okbc-kb-handle-in-language-form
				 form *loading-kb* *current-language*)
				form)
			       ((string-equal 'in-kb (first form))
				(load-okbc-kb-handle-in-kb-form
				 form *loading-kb* *current-language*)
				form)
			       (t
				(ok-back:walk-form-for-interning-given-kb
				 form frame-handle-mapping-table
				 *loading-kb* kb-local-only-p action
				 *current-language*
				 substitute-OKBC-standard-names-p))))
			(otherwise
			 (ok-back:walk-form-for-interning-given-kb
			  form frame-handle-mapping-table
			  *loading-kb* kb-local-only-p action
			  *current-language*
			  substitute-OKBC-standard-names-p))))
		     (otherwise
		      (ok-back:walk-form-for-interning-given-kb
		       form frame-handle-mapping-table *loading-kb*
		       kb-local-only-p action *current-language*
		       substitute-OKBC-standard-names-p))))
		  forms))))
	 *loading-kb* :file kb-local-only-p))
       (setq handle-to-name-mapping-table
	     (or handle-to-name-mapping-table
		 (make-hash-table
		  :size (hash-table-count
			 frame-handle-mapping-table))))
       (maphash
	#'(lambda (k v)
	    (setf (gethash v handle-to-name-mapping-table) k))
	frame-handle-mapping-table)
       (loop for (*loading-kb* *current-language* form)
	     in (reorder-forms-before-asserting-them
		 (nreverse forms) action sentence-action language)
	     do (let ((*expression-being-walked* form))
		  (typecase form
		    (cons
		     (typecase (first form)
		       (symbol
			(cond ((string-equal 'in-package (first form))
			       (load-okbc-kb-handle-in-package-form
				form *loading-kb* *current-language*))
			      ((string-equal 'in-language (first form))
			       (load-okbc-kb-handle-in-language-form
				form *loading-kb* *current-language*)
			       form)
			      ((string-equal 'in-kb (first form))
			       (load-okbc-kb-handle-in-kb-form
				form *loading-kb* *current-language*)
			       form)
			      (t (ok-back:assert-form-given-kb
				  form frame-handle-mapping-table
				  handle-to-name-mapping-table
				  *loading-kb* value-selector
				  kb-local-only-p action
				  sentence-action
				  *current-language*))))
		       (otherwise
			(ok-back:assert-form-given-kb
			 form frame-handle-mapping-table
			 handle-to-name-mapping-table *loading-kb*
			 value-selector kb-local-only-p action
			 sentence-action *current-language*))))
		    (otherwise
		     (ok-back:assert-form-given-kb
		      form frame-handle-mapping-table
		      handle-to-name-mapping-table *loading-kb*
		      value-selector kb-local-only-p action
		      sentence-action *current-language*)))))
       ;; We now have the problem that if we're not in
       ;; frame-names-required mode then we may have stubbed some
       ;; definitions without having their names available.  Now we
       ;; rename any frames with broken names.
       (when (not (ok-back:get-behavior-values-internal
		   :frame-names-required *loading-kb*))
	 (maphash #'(lambda (name handle)
		      (when (ok-back:coercible-to-frame-p-internal
			     handle *loading-kb* nil)
			(let ((actual-name
			       (ok-back:get-frame-name-internal
				handle *loading-kb* nil)))
			  (when (not (equal actual-name name))
			    (ok-back:put-frame-name-internal
			     handle name *loading-kb* nil)))))
		  frame-handle-mapping-table)))
     (case sentence-action
       (:delay (let ((sentence-structs (nreverse *delayed-sentences*)))
		 (assert-delayed-sentences sentence-structs
					   frame-handle-mapping-table
					   handle-to-name-mapping-table))
	       (values frame-handle-mapping-table handle-to-name-mapping-table
		       nil))
       (otherwise (values frame-handle-mapping-table
			  handle-to-name-mapping-table
			  (nreverse *delayed-sentences*)))))))

(defun ok-utils:assert-delayed-sentences
    (sentence-structs frame-handle-mapping-table
		      handle-to-name-mapping-table)
  "Is passed a set of delayed sentences that resulted from a call to
   <code>load-okbc-kb</code> (or some similar function, and asserts the
   sentences as appropriate."
  (loop for s in sentence-structs
	do (let ((*expression-being-walked* (delayed-sentence-sentence s)))
	     (assert-delayed-sentence
	      s
	      frame-handle-mapping-table
	      handle-to-name-mapping-table
	      (delayed-sentence-sentence s)
	      (delayed-sentence-kb s)
	      (delayed-sentence-frame s)
	      (delayed-sentence-value-selector s)
	      (delayed-sentence-kb-local-only-p s)
	      (delayed-sentence-language s)))))

(defokbcgeneric ok-back:assert-frame-definition
    (form frame-handle-mapping-table handle-to-name-mapping-table kb
	  value-selector kb-local-only-p action sentence-action language)
  (:documentation
   "Is passed a <code>define-OKBC-frame</code> <code>form</code>,
   and asserts that frame into <code>kb</code>.
   <code>Frame-handlemapping-table</code> is used to map symbols found in the
   form into frame handles, and is side-effected for any new frame handles
   allocated during the frame definition loading process.  See
   <code>ok-utils:load-okbc-kb</code> and
   <code>load-okbc-kb-internal</code>."))

(defun ensure-slots-and-facets-exist-for-frame-definition
    (form kb real-name frame-handle-mapping-table handle-to-name-mapping-table
	  kb-local-only-p)
  "Is called from the OKBC loader to make sure that all of the necessary
   slots and facets have been reified for the frame being defined."
  (let ((own-slots nil)
	(own-facets nil)
	(template-slots nil)
	(template-facets nil))
    (walk-form kb
	       #'(lambda (kb production known-context-type bound-vars form)
		   (declare (ignore kb known-context-type bound-vars))
		   (when (eq :own-slots production)
		     (loop for spec in form
			   for slot = (first spec)
			   do (pushnew slot own-slots)))
		   (when (eq :template-slots production)
		     (loop for spec in form
			   for slot = (first spec)
			   do (pushnew slot template-slots)))
		   (when (eq :own-facets production)
		     (loop for (slot . fspecs) in form
			   do (pushnew slot own-slots)
			   (let ((entry (or (assoc slot own-facets)
					    (let ((new (list slot)))
					      (push new own-facets)
					      new))))
			     (loop for spec in fspecs
				   for facet = (first spec)
				   do (setf (rest entry)
					    (cons facet (rest entry)))))))
		   (when (eq :template-facets production)
		     (loop for (slot . fspecs) in form
			   do (pushnew slot template-slots)
			   (let ((entry (or (assoc slot template-facets)
					    (let ((new (list slot)))
					      (push new template-facets)
					      new))))
			     (loop for spec in fspecs
				   for facet = (first spec)
				   do (setf (rest entry)
					    (cons facet (rest entry)))))))
		   form)
	       form :production :define-okbc-frame
	       :cons-switch :dont-cons)
    (let ((frame (gethash real-name frame-handle-mapping-table)))
      (loop for slot-type in '(:own :template)
	    for slots in (list own-slots template-slots)
	    for facet-specs in (list own-facets template-facets)
	    do (loop for slot in slots
		     for match = (gethash slot handle-to-name-mapping-table)
		     when match
		     do (maybe-create-slot frame match slot-type kb
					   kb-local-only-p slot))
	    (loop for (slot . facets) in facet-specs
		  for match = (gethash slot handle-to-name-mapping-table)
		  do
		  (when match
		    (maybe-create-slot frame match slot-type kb
				       kb-local-only-p slot))

		  (loop for facet in facets
			for facet-match =
			(gethash facet handle-to-name-mapping-table)
			when facet-match
			do (maybe-create-facet frame slot facet-match
					       slot-type
					       kb kb-local-only-p
					       facet)))))))

(defstruct delayed-sentence
  sentence
  kb
  frame
  value-selector
  kb-local-only-p
  language)

(defun shrink-form (form)
  (typecase form
    (cons (cons (shrink-form (first form))
		(shrink-form (rest  form))))
    (string
     (substitute
      #\space #\newline
      (if (> (length form) 20)
	  (concatenate 'string (subseq form 0 18) "....")
	  form)))
    (otherwise form)))

(defun brief-sentence-string (form kb)
  (flet ((doit ()
	   (let ((*print-level* 2)
		 (*print-length* 4)
		 (*print-case* :downcase)
		 (*print-readably* nil))
	     (format nil "~S"
	       (loop for element in form
		     for i from 0 to *print-length*
		     collect (shrink-form element))))))
    (if (typep kb 'network-kb)
	(doit)
	(implement-with-kb-io-syntax-internal
	 #'doit kb :user-interface nil))))

(defmethod handle-sentence-assertion
 ((frame-handle-mapping-table t) (handle-to-name-mapping-table t)
  sentence kb frame value-selector kb-local-only-p
  (sentence-action (eql :assert)) (language t))
  (let ((tellable (tellable-internal sentence kb value-selector
				     kb-local-only-p)))
    (if tellable
	(tell-internal sentence kb frame :known-true kb-local-only-p)
	(warn "Sentence ~A is untellable."
	      (brief-sentence-string sentence kb)))))

(defmethod assert-delayed-sentence
 ((s delayed-sentence) frame-handle-mapping-table handle-to-name-mapping-table
  sentence kb frame value-selector kb-local-only-p language)
 (handle-sentence-assertion frame-handle-mapping-table
			    handle-to-name-mapping-table sentence kb frame
			    value-selector kb-local-only-p
			    :assert language))

(defmethods handle-sentence-assertion
 ((frame-handle-mapping-table t) (handle-to-name-mapping-table t) sentence kb
  frame value-selector kb-local-only-p
  (sentence-action ((eql :return) (eql :delay))) (language t))
 (declare (special *delayed-sentences*))
 (push (make-delayed-sentence
	:sentence sentence
	:kb kb
	:frame frame
	:value-selector value-selector
	:kb-local-only-p kb-local-only-p
	:language language)
       *delayed-sentences*))

(defmethod handle-sentence-assertion
 ((frame-handle-mapping-table t) (handle-to-name-mapping-table t) (sentence t)
  (kb t) (frame t) (value-selector t) (kb-local-only-p t)
  (sentence-action (eql :ignore)) (language t))
 nil)

(defmethod ok-back:assert-frame-definition
 (form frame-handle-mapping-table handle-to-name-mapping-table kb
       value-selector kb-local-only-p action sentence-action language)
 (declare (ignore action))
 (let ((interned (walk-form-for-load form frame-handle-mapping-table kb)))
   (let ((real-name (or (gethash (second form) handle-to-name-mapping-table)
			(second form))))
     (let ((handle-part
	     (if (gethash real-name frame-handle-mapping-table)
		 (list :handle (gethash real-name
					frame-handle-mapping-table))
		 nil)))
       (ensure-slots-and-facets-exist-for-frame-definition
	form kb real-name frame-handle-mapping-table
	handle-to-name-mapping-table kb-local-only-p)
       (let ((frame
	      (apply
	       'okbc:create-frame
	       real-name
	       (let ((type (loop for (key value) on (rest (rest form))
				 by #'cddr
				 when (member key '(:frame-type))
				 return value)))
		 (or type
		     (let ((guess
			    (loop for (key value)
				  on (rest (rest interned)) by #'cddr
				  when (and (eq key :direct-superclasses)
					    value)
				  return :class
				  when (and (member key '(:template-facets
							  :template-slots))
					    value)
				  return :class
				  finally (return :individual))))
		       (warn "No frame type supplied in define-okbc-frame ~
                              form for ~S.  Assuming ~S"
			     real-name guess)
		       guess)))
	       :kb kb
	       (append handle-part
		       (loop for (key value)
			     on (rest (rest interned)) by #'cddr
			     when (not (member key '(:frame-type
						     :kb :sentences)))
			     ;; Fix up DOC.  Asymmetry in protocol!
			     append (list (if (eq :documentation key)
					      :doc
					      key)
					  (case key
					    ((:own-slots
					     :template-slots)
					     (ecase value-selector
					       (:known-true value)
					       (:default-only
						   (loop
						    for (s . vs) in value
						    collect
						    (cons s
						    (loop for v in vs
							  collect
							  (list :default
								v)))))))
					    ((:own-facets
					     :template-facets)
					     (ecase value-selector
					       (:known-true value)
					       (:default-only
						(loop
						 for (s . fspecs) in value
						 collect
						 (cons s
						       (loop for (f . vs)
							     in fspecs
							     collect
							     (cons
							      f
							      (loop for v in vs
								    collect
								    (list
								     :default
								     v)))))))))
					    (otherwise value))))))))
	 (loop for sentence in
	       (loop for (key value) on (rest (rest interned)) by #'cddr
		     when (eq :sentences key) return value)
	       do (handle-sentence-assertion
		   frame-handle-mapping-table handle-to-name-mapping-table
		   sentence kb frame value-selector kb-local-only-p
		   sentence-action language))
	 frame)))))

(defmethod find-or-create-frame-handle-for-intern
    (form defining-type kb mapping-table (language t))
  (or (gethash form mapping-table)
      (multiple-value-bind (frame found-p)
	(coerce-to-frame-internal form kb nil nil)
	(if found-p
	    (let ((handle (get-frame-handle-internal frame kb nil)))
	      (setf (gethash form mapping-table) handle)
	      handle)
	    (let ((new (allocate-frame-handle-internal
			form defining-type kb nil)))
	      ;; (format t "~%Allocated ~S for ~S" new form)
	      (setf (gethash form mapping-table) new)
	      new)))))

(defokbcgeneric intern-frame-handles-if-necessary
    (kb production known-context-type bound-vars form language mapping-table
	substitute-OKBC-standard-names-p)
  (:documentation
   "Internal protocol used by <code>load-okbc-kb</code>.  This is a walker
    function that is called by the code walker to intern frame handles for any
    frame references found.  When <code>substitute-OKBC-standard-names-p</code>
    is true, references that are string-equal to OKBC standard names are
    mapped into the OKBC standard keywords before the intern takes place."))

(defmethod intern-frame-handles-if-necessary
    (kb production known-context-type bound-vars form (language t)
	mapping-table substitute-OKBC-standard-names-p)
  (declare (ignore bound-vars))
  (declare (special ok-back:*okbc-standard-names*
		    ok-back:*okbc-relation-symbols*))
  (case production
    ((:constant :objconst :funconst :relconst)
     (typecase form
       ((or quasi-symbol symbol)
	(let ((real-form
	       (if substitute-OKBC-standard-names-p
		   (or (find (okbc-string form) ok-back:*okbc-standard-names*
			     :test #'string-equal)
		       (find (okbc-string form) ok-back:*okbc-relation-symbols*
			     :test #'string-equal)
		       form)
		   form)))
	  (let ((are-frames (get-behavior-values-internal :are-frames kb)))
	    (if (or (not known-context-type)
		    (member known-context-type are-frames))
		(find-or-create-frame-handle-for-intern
		 real-form known-context-type kb mapping-table language)
		real-form))))
       (otherwise form)))
    (otherwise form)))

(defun ok-utils:walk-form-for-load (form mapping-table kb)
  "Walks over the form during the load process substituting any necessary
   frame handles into the form."
  (walk-form
  kb
  #'(lambda (kb production known-context-type bound-vars form)
      (substitute-frame-handles-if-necessary
       kb production known-context-type bound-vars form mapping-table))
  form
  :production :define-okbc-frame
  :symbols-ok-as-non-logical-constants-p t
  :cons-switch :share-structure-if-possible))

(defun substitute-frame-handles-if-necessary
    (kb production known-context-type bound-vars form mapping-table)
  (declare (ignore kb known-context-type bound-vars))
  (let ((substituted
	 (case production
	   ((:constant :objconst :relconst :funconst)
	    (or (gethash form mapping-table) form))
	   (otherwise form))))
    (when (and (not (consp form)) (not (equal substituted form)))
      ;; (format t "~%Switched ~S for ~S" substituted form)
      )
    substituted))

(defun okbc-string (x)
  (etypecase x
    ((or string symbol) (string x))
    (quasi-symbol (quasi-symbol-name x))))

;==============================================================================

;;; The new KIF/OKBC parser

(defvar *cons-switch* :cons
  "Can be one of {:cons :share-structure-if-possible :dont-cons
  :destructive}.")

(defmacro loop-for-x-in-l-collect ((x l) &body body)
  `(ecase *cons-switch*
    (:cons (loop for ,x in ,l collect (locally ,@body)))
    (:destructive
     (let ((.l. ,l))
       (loop for loc on .l.
	     for ,x in .l.
	     do (setf (first loc) (locally ,@body)))
       .l.))
    (:dont-cons
     ,(if (and (= (length body) 1) (atom (first body)))
	  l;; to avoid obnoxious warning.
	  `(let ((.l. ,l))
	    (let ((.rest. .l.)
		  (,x nil))
	      (loop while .rest.
		    do (progn (setq ,x (pop .rest.))
			      (locally ,@body))))
	    .l.)))
    (:share-structure-if-possible
     (labels ((.rec. (original-list)
		(if original-list
		    (let ((head (let ((,x (first original-list)))
				  ,@body))
			  (tail (.rec. (rest original-list))))
		      (if (and (eql head (first original-list))
			       (eq tail (rest original-list)))
			  original-list
			  ;; Only introduce a new cons if either the tail
			  ;; has changed or the head changes.
			  (cons head tail)))
		    nil)))
       (.rec. ,l)))))

(defmacro loop-for-location-in-l-collect-list
    ((location l) &body body)
  `(ecase *cons-switch*
    (:cons (let ((.l. (copy-list ,l)))
	     (let ((.head. (cons :ignore .l.)))
	       (loop with .current. = .head.
		     for ,location = (rest .current.)
		     do (setf (rest .current.) (locally ,@body))
		     (pop .current.)
		     when (not (consp .current.)) return nil
		     when (not (rest .current.)) return nil)
	       (rest .head.))))
    (:destructive
     (let ((.l. ,l))
       (let ((.loc. (cons :ignore .l.)))
	 (loop with .current. = .loc.
	       for ,location = (rest .current.)
	       do (setf (rest .current.) (locally ,@body))
	       (pop .current.)
	       when (not (consp .current.)) return nil
	       when (not (rest .current.)) return nil)
	 (rest .loc.))))
    (:dont-cons
     ,(if (and (= (length body) 1) (atom (first body)))
	  l;; to avoid obnoxious warning.
	  `(let ((.l. ,l))
	    (let ((,location .l.))
	      (loop while ,location
		    do (progn (locally ,@body)
			      (pop ,location))))
	    .l.)))
    (:share-structure-if-possible
     (labels ((.rec. (,location)
		(if ,location
		    (let ((head (progn ,@body)))
		      ;; (print (list :location ,location :head head))
		      (if (consp head)
			  (let ((tail (.rec. (rest head))))
			    ;;(print (list :tail tail :head head (and (eql head ,location) (eq tail (rest ,location)))))
			    (if (and (eql head ,location)
				     (eq tail (rest ,location)))
				(progn ;; (print (list :xxxx ,location))
				       ,location)
				;; Only introduce a new cons if either the tail
				;; has changed or the head changes.
				(cons (first head) tail)))
			  head))
		    nil)))
       (.rec. ,l)))))

(defmacro loop-for-k/v-on-l-append ((key value l) key-value value-value)
  `(ecase *cons-switch*
    (:cons (loop for (,key ,value) on ,l by #'cddr
	    append (list ,key-value ,value-value)))
    (:destructive
     (let ((.l. ,l)
	   (.loc. ,l))
       (loop for (,key ,value) on ,l by #'cddr
	     do (setf (first .loc.) ,key-value)
	        (setf (second .loc.) ,value-value)
		(setq .loc. (rest (rest .loc.))))
       .l.))
    (:dont-cons
     (let ((.l. ,l))
       (let ((.rest. .l.)
	     (,key nil)
	     (,value nil))
	 (loop while .rest.
	       do (progn (setq ,key (pop .rest.))
			 (setq ,value (pop .rest.))
			 ,key-value
			 ,value-value)))
       .l.))
    (:share-structure-if-possible
     (labels ((.rec. (original-list)
		(if original-list
		    (let ((tail (.rec. (rest (rest original-list)))))
		      (multiple-value-bind (new-key new-value)
			(let ((,key (first original-list))
			      (,value (second original-list)))
			  (values ,key-value ,value-value))
			(if (and (eql new-value (second original-list))
				 (eql new-key (first original-list))
				 (eq tail (rest (rest original-list))))
			    original-list
			    ;; Only introduce a new cons if either the tail has
			    ;; changed or the head changes.
			    (cons new-key (cons new-value tail)))))
		    nil)))
       (.rec. ,l)))))

(defmacro loop-for-k/v-on-l-append-list ((key value l) list-value)
  `(ecase *cons-switch*
    (:cons (loop for (,key ,value) on ,l by #'cddr
	    append ,list-value))
    (:destructive
     (let ((.l. ,l)
	   (.loc. ,l))
       (loop for (,key ,value) on ,l by #'cddr
	     for .list-value. = ,list-value
	     do (setf (first .loc.) (first .list-value.))
	        (setf (second .loc.) (second .list-value.))
		(setq .loc. (rest (rest .loc.))))
       .l.))
    (:dont-cons
     (let ((.l. ,l))
       (let ((.rest. .l.)
	     (,key nil)
	     (,value nil))
	 (loop while .rest.
	       do (progn (setq ,key (pop .rest.))
			 (setq ,value (pop .rest.))
			 ,list-value)))
       .l.))
    (:share-structure-if-possible
     (labels ((.rec. (original-list)
		(if original-list
		    (let ((tail (.rec. (rest (rest original-list)))))
		      (let ((new-list-value
			     (let ((,key (first original-list))
				   (,value (second original-list)))
			       ,list-value)))
			(if (and (eql (first  new-list-value)
				      (first  original-list))
				 (eql (second new-list-value)
				      (second original-list))
				 (eq tail (rest (rest original-list))))
			    original-list
			    ;; Only introduce a new cons if either the tail has
			    ;; changed or the head changes.
			    (append new-list-value tail))))
		    nil)))
       (.rec. ,l)))))

(defmacro parser-list* (original-list &rest args)
  "This macro implements the equivalent of the <code>list*</code> Lisp function
   used by the code walker.  It is sensitive to the value of the
   <code>cons-switch</code> argument to <code>walk-form</code>.  The value
   returned by the form will be, depending on the value of the cons switch,
   <DL>
   <DT><code>:cons</code><DD>the equivalent of calling
       <code>(apply #'list* args)</code>.
   <DT><code>:dont-cons</code><DD>the equivalent of calling
       <code>(progn ,@args)</code>.
   <DT><code>:destructive</code><DD>the equivalent of evaluating
       <code>original-list</code> with suitable substitutions.
   <DT><code>:share-structure-if-possible</code><DD>the equivalent of
       evaluating <code>original-list</code> with as few substitutions as
       possible.
   </DL>"
  `(ecase *cons-switch*
    (:cons (list* ,@args))
    (:destructive
     (let ((.l. ,original-list)
	   (.loc. ,original-list))
       ,@(loop for arg in (butlast args)
	       for first-p = t then nil
	       for index from 0
	       append `(,@(if first-p nil '((pop .loc.)))
			(setf (first .loc.) ,arg)))
       (setf (rest .loc.) ,(first (last args)))
       .l.))
    (:dont-cons (progn ,@args ,original-list))
    (:share-structure-if-possible
     ,(labels ((.rec. (args depth)
		      (if (rest args)
			  `(multiple-value-bind (new-tail old-tail)
			    ,(.rec. (rest args) (+ 1 depth))
			    (let ((old-head (nth ,depth ,original-list))
				  (new-head ,(first args)))
			      #+ignore
			      (print (list :--------
					   :new-head new-head
					   :new-tail new-tail
					   :old-head old-head
					   :old-tail old-tail))
			      (if (and (eq new-tail old-tail)
				       (eq new-head old-head))
				  (let ((l (nthcdr ,depth ,original-list)))
				    (values l l))
				  (values (cons new-head new-tail) nil))))
			  (let ((tail-expr (first args)))
			    `(values ,tail-expr
			      (nthcdr ,depth ,original-list))))))
	      (.rec. args 0)))))

(defmacro parser-list (original-list &rest args)
  "This macro implements the equivalent of the <code>list</code> Lisp function
   used by the code walker.  It is sensitive to the value of the
   <code>cons-switch</code> argument to <code>walk-form</code>.  The value
   returned by the form will be, depending on the value of the cons switch,
   <DL>
   <DT><code>:cons</code><DD>the equivalent of calling
       <code>(apply #'list args)</code>.
   <DT><code>:dont-cons</code><DD>the equivalent of calling
       <code>(progn ,@args)</code>.
   <DT><code>:destructive</code><DD>the equivalent of evaluating
       <code>original-list</code> with suitable substitutions.
   <DT><code>:share-structure-if-possible</code><DD>the equivalent of
       evaluating <code>original-list</code> with as few substitutions
       as possible.
   </DL>"
  `(ecase *cons-switch*
    (:cons (list ,@args))
    (:destructive
     (let ((.l. ,original-list))
       ,@(loop for arg in args
	       for index from 0
	       collect `(setf (nth ,index .l.) ,arg))
       .l.))
    (:dont-cons (progn ,@args ,original-list))
    (:share-structure-if-possible
     ,(labels ((.rec. (args depth)
		      (if args
			  `(multiple-value-bind (new-tail old-tail)
			    ,(.rec. (rest args) (+ 1 depth))
			    (let ((old-head (nth ,depth ,original-list))
				  (new-head ,(first args)))
			      #+ignore
			      (print (list :--------
					   :new-head new-head
					   :new-tail new-tail
					   :old-head old-head
					   :old-tail old-tail))
			      (if (and (eq new-tail old-tail)
				       (eq new-head old-head))
				  (let ((l (nthcdr ,depth ,original-list)))
				    (values l l))
				  (values (cons new-head new-tail) nil))))
			  (values nil nil))))
	      (.rec. args 0)))))

(defmacro parser-cons (original-list x y)
  "This macro implements the equivalent of the <code>cons</code> Lisp function
   used by the code walker.  It is sensitive to the value of the
   <code>cons-switch</code> argument to <code>walk-form</code>.  The value
   returned by the form will be, depending on the value of the cons switch,
   <DL>
   <DT><code>:cons</code><DD>the equivalent of calling
       <code>(cons x y)</code>.
   <DT><code>:dont-cons</code><DD>the equivalent of calling
       <code>(progn x y)</code>.
   <DT><code>:destructive</code><DD>the equivalent of evaluating
       <code>original-list</code> with suitable substitutions.
   <DT><code>:share-structure-if-possible</code><DD>the equivalent of
       evaluating <code>original-list</code> with as few substitutions
       as possible.
   </DL>"
  `(ecase *cons-switch*
    (:cons (cons ,x ,y))
    (:destructive
     (let ((.l. ,original-list))
       (setf (first .l.) ,x)
       (setf (rest  .l.) ,y)
       .l.))
    (:dont-cons (progn ,x ,y ,original-list))
    (:share-structure-if-possible
     (let ((new-head ,x)
	   (new-tail ,y))
       (if (and (eq new-head (first ,original-list))
		(eq new-tail (rest  ,original-list)))
	   ,original-list
	   (cons new-head new-tail))))))

#+ignore
(defun test (ll s)
  (let ((*cons-switch* s))
    (loop-for-x-in-l-collect
     (thing ll) thing)))

(setf (documentation '*expression-being-walked* 'variable)
      "Is bound to the top-level expression being walked over by the OKBC
       parser.")

(defvar *symbols-ok-as-non-logical-constants-p* nil)

(defvar *replace-kif-symbols-with-keywords-p* t
  "This special is bound by the code walker to the selected value of the
  <code>replace-kif-symbols-with-keywords-p</code> argument to
  <code>walk-form</code>")

(defvar *free-vars*)



(defun walk-form 
    (kb function-to-apply expression 
	&key (bound-vars ())
	(production :sentence)
	(language :okbc)
	(known-context-type nil)
	(symbols-ok-as-non-logical-constants-p
	 *symbols-ok-as-non-logical-constants-p*)
	(cons-switch *cons-switch*)
	(replace-kif-symbols-with-keywords-p
	 *replace-kif-symbols-with-keywords-p*))
  "A function useful for parsing and analyzing KIF/OKBC expressions.
It walks a KIF expression applying <code>function-to-apply</code> to
each subexpression.
<DL>
<DT><code>expression</code><DD> is an expression of a production defined by
<code>production</code>.  By default it is a KIF sentence. 

<DT><code>function-to-apply</code><DD> is called wih five arguments:
<OL><LI><code>KB</code>, the KB with respect to which the walk is happening.
This argument allows you to specialize on the class of kb.

<LI><code>production</code>, a KIF expression production such as
<code>:sentence</code> or <code>:term</code>
that specifies the syntactic category of the expression.

<LI><code>known-context-type</code>, the OKBC context type of the expression
argument if known.

<LI><code>bound-vars</code>, the list of currently bound variables, which is
updated automatically in lexically enclosed forms inside logic binding
constructs.  For example in, <PRE>(exists (?A ?B) &lt;kif-sentence&gt;)</PRE>
<code>walk-form</code> might be called with <code>expression</code> bound
to &lt;kif-sentence&gt; and <code>bound-vars</code> bound to
<code>'(?A ?B)</code>.

<LI><code>expression</code>, the actual expression to walk.
</OL>
The value returned by <code>function-to-apply</code> replaces the
<code>expression</code> in the resulting expression tree.  Thus, if
<code>function-to-apply</code> alway returns its <code>expression</code>
argument, then the result of a top level call to <code>walk-form</code> is
equal to the input expression.  Each call to <code>function-to-apply</code>
is given the result of recursive calls on subexpressions;
in other words, this is a post-fix recursive traversal.

<DT><code>bound-vars</code><DD> is a top-level set of bound vars that can be
passed in to the walk operation.

<LI><code>language</code>, identifies the language being parsed.

<DT><code>production</code><DD> is the starting production to use.
Of particular interest are <code>:sentence</code> which parses KIF sentences,
<code>:kif</code>, which parses KIF top level forms (including sentences), and
<code>:define-okbc-frame</code> which parses complete OKBC frame
definitions.

<DT><code>known-context-type</code><DD> is the context type of the expression
argument, if known.

<DT><code>symbols-ok-as-non-logical-constants-p</code><DD> is a flag that
determines whether symbols are reasonable non-logical constants or not.  This
is important because once a form has been read in and interned by a KB we
generally expect that all non-logical constants will be frame references,
i.e., true of <code>frame-reference-p</code>.  However, when we are using the
walker to perform the interning process then obviously the frame references
are not guaranteed to be frames, and are generally symbols.

<DT><code>cons-switch</code><DD> is a switch that controls the way that the
parser conses.  It can take on one of three values:
<OL>
<LI><code>:cons</code> - cons a completely fresh structure for the form being
walked.  No structure will be shared with the original except for any shared
structure returned by the walk function.
<LI><code>:dont-cons</code> - performs the walk only for side effects, no
new structure is consed, and the value retuned by the walker is undefined.
<LI><code>:share-structure-if-possible</code> - shares as much structure as
possible with the original.  This doesn't mean that ephemeral consing won't
take place during a walk with an identity walk function, but it does mean that
the result will be EQ whenever possible.
</OL>

<DT><code>replace-kif-symbols-with-keywords-p</code><DD> is a flag that
when true causes each KIF symbol (such as AND, or <=) to be replaced
with the keywordified version of that symbol during the walk.  This
allows automatic package DWIMing of input forms.  If the value of this
argument is a package or names a package then the symbol substitutions
happen into the specified package rather than necessarily to keywords.
Note that this substitution will, in general result the input form changing,
so some consing will generally occur if <code>cons-switch</code> is set
to <code>:share-structure-if-possible</code>.

</DL>

The <code>function-to-apply</code> is usually a generic function with methods
which specialize the first (KB) andgument and <code>eql</code> specialize its
second (production) argument.  Usually, the default method will just return
its <code>expression</code> argument, and other methods will be written to
pick out specific subexpression productions for special processing."
  (assert (or (functionp function-to-apply)
	      (and (symbolp function-to-apply)
		   (functionp (symbol-function function-to-apply)))) ()
		   "The FUNCTION-TO-APPLY arg must be a funcallable ~
                    function, but ~S isn't."
		   function-to-apply)
  (let ((*symbols-ok-as-non-logical-constants-p*
	 symbols-ok-as-non-logical-constants-p)
	(*cons-switch* cons-switch)
	(*replace-kif-symbols-with-keywords-p*
	 (typecase replace-kif-symbols-with-keywords-p
	   ((or string symbol)
	    (or (find-package replace-kif-symbols-with-keywords-p)
		replace-kif-symbols-with-keywords-p))
	   (otherwise replace-kif-symbols-with-keywords-p)))
	(*free-vars* nil))
    (if (and (boundp '*expression-being-walked*)
	     (boundp '*error-messages-in-this-top-level-form*))
	(walk-subexpression kb production (find-language language)
			known-context-type bound-vars expression
			function-to-apply)
	(if (boundp '*error-messages-in-this-top-level-form*)
	    (let ((*expression-being-walked* expression))
	      (walk-subexpression kb production (find-language language)
				  known-context-type bound-vars expression
				  function-to-apply))
	    (let ((*error-messages-in-this-top-level-form*
		   (make-hash-table :test #'equal))
		  (*expression-being-walked* expression))
	      (walk-subexpression kb production (find-language language)
				  known-context-type bound-vars expression
				  function-to-apply))))))

(eval-when (compile load eval)

  (when (and #+Lucid (not lucid:*use-sfc*) t)
    (define-compiler-macro walk-subexpression
	(&whole whole &rest args)
      (declare (ignore args))
      (check-and-abort-for-sfc)
      (loop for arg-name in '(kb production language known-context-type
			      bound-vars expression function-to-apply)
	    for entry = (assoc arg-name
			       *legal-literal-slot-values-alist*)
	    when entry
	    collect (test-arg-for-legal-literal
		     arg-name arg-name 'walk-subexpression whole 
		     'walk-subexpression nil))
      whole)
  
    (defun style-check-walk-subexpression-definitions (form)
      (when (and (consp form)
		 (member (first form) '(defmethod defmethods))
		 (eq (second form) 'walk-subexpression))
	(let ((arglist (if (listp (third form))
			   (third form)
			   (fourth form))))
	  (destructuring-bind (kb production language known-context-type
				  bound-vars expression function-to-apply)
	      arglist
	    (declare (ignore kb production known-context-type bound-vars
			     expression function-to-apply))
	    (when (not (string= (first-if-list language) 'language))
	      (format *error-output*
	       "~%;;; In the definition of:~%;;; (~{~S ~}...),"
		(if (listp (third form))
		    (firstn 3 form)
		    (firstn 4 form)))
	      (format *error-output* "~%;;;     the expected ~
                                            \"language\" is called ~A"
		(first-if-list language)))))))

    (pushnew 'style-check-walk-subexpression-definitions
	     *all-okbc-compile-time-style-checkers*)))

(defokbcclass ok-utils:abstract-language ()
  ()
  (:documentation "The abstract superclass of all languages known to the OKBC
 parser."))

(defokbcclass ok-utils:abstract-kif-language (ok-utils:abstract-language)
  ()
  (:documentation "The OKBC representation of the KIF-language for the OKBC
 parser."))

(defokbcclass ok-utils:kif-3.0-language (ok-utils:abstract-kif-language)
  ()
  (:documentation "The OKBC representation of the KIF-language for the OKBC
 parser."))

(defokbcclass ok-utils:ansi-kif-language (ok-utils:abstract-kif-language)
  ()
  (:documentation "The OKBC representation of the KIF-language for the OKBC
 parser."))

(defokbcclass abstract-okbc-language (ok-utils:abstract-language) ())

(defokbcclass ok-utils:okbc-language (abstract-okbc-language kif-3.0-language)
  ()
  (:documentation "The OKBC representation of the OKBC-language for the OKBC
 parser.  All KIF-language productions are supported as well as the
 define-OKBC-frame form."))

(defokbcclass ok-utils:okbc-with-ansi-kif-language
    (abstract-okbc-language ansi-kif-language)
  ()
  (:documentation "The OKBC representation of the OKBC-language for the OKBC
 parser.  All ANSI-KIF language productions are supported as well as the
 define-OKBC-frame form."))

(defmethod ok-back:assert-form-given-kb
 or ((form t) (frame-handle-mapping-table t) (handle-to-name-mapping-table t)
     (kb t) (value-selector t) (kb-local-only-p t) (action t)
     (sentence-action t) (language abstract-okbc-language))
  (if (and (consp form)
	   (symbolp (first form))
	   (string-equal 'ok-utils::define-okbc-frame (first form)))
      (ok-back:assert-frame-definition form frame-handle-mapping-table
				       handle-to-name-mapping-table kb
				       value-selector kb-local-only-p
				       action sentence-action language)
      nil))

(defmethod ok-back:assert-form-given-kb
 or ((form t) (frame-handle-mapping-table t) (handle-to-name-mapping-table t)
     (kb t) (value-selector t) (kb-local-only-p t) (action t)
     (sentence-action t) (language ok-utils:abstract-kif-language))
  (let ((tellable (tellable-internal form kb value-selector
				     kb-local-only-p)))
    (if tellable
	(handle-sentence-assertion
	 frame-handle-mapping-table handle-to-name-mapping-table form kb
	 nil value-selector kb-local-only-p sentence-action language)
	nil)))

(defmethod sentences-for-relation-arglist ((relation t) (arglist t) (kb t)
					   (language t))
  nil)

(defmethod sentences-for-function-arglist
 ((function t) (arglist t) (result-var t) (kb t) (language t))
  nil)

(defmethod sentences-for-relation-implication
 ((relation t) (arglist t) (kb t) (language t) (implication-sentence t))
 nil)

(defmethod sentences-for-function-implication
 ((relation t) (arglist t) (result-var t) (kb t) (language t)
  (implication-sentence t))
 nil)

(defmethod ok-back:assert-form-given-kb
 or ((form t) (frame-handle-mapping-table t) (handle-to-name-mapping-table t)
     (kb assert-kif-definitions-as-sentences-mixin) (value-selector t)
     (kb-local-only-p t) (action t) (sentence-action t)
     (language ok-utils:kif-3.0-language))
  (if (and (consp form) (symbolp (first form)))
      (let ((key (find-symbol (string-upcase (first form)) :keyword))
	    (type-of-definition nil))
	(if (member key '(:deffunction :defrelation :defobject))
	    (progn
	      (when (boundp '*expression-being-walked*)
		(setq *expression-being-walked* (second form)))
	      (let ((form (walk-form
			   kb
			   #'(lambda
				 (kb production known-context-type bound-vars
				     form)
			       (declare (ignore kb known-context-type
						bound-vars))
			       (case production
				 ((:unrestricted
				   :complete
				   :conservative)
				  (setq type-of-definition production)))
			       form)
			   form
			   :production :definition
			   :symbols-ok-as-non-logical-constants-p t
			   :cons-switch :dont-cons
			   :language language)))
		(pop form)
		(let ((name (pop form)))
		  (let ((sentence
			 (case key
			   (:defobject
			       (ecase type-of-definition
				 (:complete
				  (destructuring-bind (&key =) form
				    `(:= ,name ,=)))
				 (:conservative
				  (destructuring-bind (&key conservative-axiom)
				      ;; Is this right?
				      form conservative-axiom))
				 (:unrestricted
				  (if (rest form)
				      (cons :and form)
				      (first form)))))
			   (:deffunction
			       (ecase type-of-definition
				 (:complete
				  (let ((args (pop form)))
				    (let ((arg-sentences
					   (sentences-for-function-arglist
					    name (butlast args)
					    (first (last args)) kb language)))
				      (destructuring-bind (&key =) form
					(if arg-sentences
					    `(:and (:= (,name ,@args) ,=)
					      ,@arg-sentences)
					    `(:= (,name ,@args) ,=))))))
				 (:conservative
				  (destructuring-bind (&key conservative-axiom)
				      ;; Is this right?
				      form conservative-axiom))
				 (:unrestricted
				  (let ((arg-sentences
					 (sentences-for-function-arglist
					  name :none :none kb language)))
				    (let ((conjuncts (append arg-sentences
							     form)))
				      (if (rest conjuncts)
					  (cons :and conjuncts)
					  (first conjuncts)))))))
			   (:defrelation
			       (ecase type-of-definition
				 (:complete
				  (let ((args (pop form)))
				    (destructuring-bind (&key =) form
				      (let ((arg-sentences
					     (sentences-for-relation-arglist
					      name args kb language)))
					(if arg-sentences
					    `(:and (:<=> (,name ,@args) ,=)
					      ,@arg-sentences)
					    `(:<=> (,name ,@args) ,=))))))
				 (:conservative
				  (if (and (consp (first form))
					   (kif-variable-p
					    (first (first form))))
				      (let ((args (pop form)))
					(destructuring-bind
					      (&key => conservative-axiom)
					    form
					  `(:=> (,name ,@args)
					    ;; Is this right??
					    (:and ,conservative-axiom
						 ,=>))))
				      (destructuring-bind
					    (&key conservative-axiom) form
					;; Is this right??
					conservative-axiom)))
				 (:unrestricted
				  (let ((arg-sentences
					 (sentences-for-relation-arglist
					  name :none kb language)))
				    (let ((conjuncts
					   (append
					    arg-sentences
					    (if (and (consp (first form))
						     (kif-variable-p
						      (first
						       (first form))))
						(let ((args (pop form)))
						  (destructuring-bind
							(&key => axiom)
						      form
						    `((:=> (,name ,@args)
							  (:and ,axiom
							       ,=>)))))
						form))))
				      (if (rest conjuncts)
					  (cons :and conjuncts)
					  (first conjuncts)))))))
			   (otherwise nil))))
		    (when sentence
		      (handle-sentence-assertion
		       frame-handle-mapping-table handle-to-name-mapping-table
		       sentence kb
		       (coerce-to-frame-internal name kb nil kb-local-only-p)
		       value-selector kb-local-only-p sentence-action
		       language))))
		t))
	    nil))
      nil))

(defmethod ok-back:assert-form-given-kb
 or ((form t) (frame-handle-mapping-table t) (handle-to-name-mapping-table t)
     (kb assert-kif-definitions-as-sentences-mixin) (value-selector t)
     (kb-local-only-p t) (action t) (sentence-action t)
     (language ok-utils:ansi-kif-language))
  (if (and (consp form) (symbolp (first form)))
      (let ((key (find-symbol (string-upcase (first form)) :keyword))
	    (type-of-definition nil))
	(if (member key '(:deflogical :deffunction :defrelation :defobject))
	    (progn
	      (when (boundp '*expression-being-walked*)
		(setq *expression-being-walked* (second form)))
	      (let ((form (walk-form
			   kb
			   #'(lambda
				 (kb production known-context-type bound-vars
				     form)
			       (declare (ignore kb known-context-type
						bound-vars))
			       (case production
				 ((:unrestricted :partial :complete)
				  (setq type-of-definition production)))
			       form)
			   form
			   :production :definition
			   :symbols-ok-as-non-logical-constants-p t
			   :cons-switch :dont-cons
			   :language language)))
		(pop form)
		(let ((name (pop form))
		      (doc-string nil))
		  (let ((sentence
			 (case key
			   (:defobject
			       (ecase type-of-definition
				 (:complete
				  (if (stringp (first form))
				      (setq doc-string (pop form))
				      nil)
				  (destructuring-bind (&key =) form
				    `(:= ,name ,=)))
				 (:partial
				  (if (stringp (first form))
				      (setq doc-string (pop form))
				      nil)
				  (destructuring-bind (&key -> <= =>) form
				    (cond (=> `(:=> (:= ,name ,->) ,=>))
					  (<= `(:<= (:= ,name ,->) ,<=))
					  (t nil))))
				 (:unrestricted
				  (if (stringp (first form))
				      (setq doc-string (pop form))
				      nil)
				  (if (rest form)
				      (cons :and form)
				      (first form)))))
			   (:deffunction
			       (ecase type-of-definition
				 (:complete
				  (let ((args (pop form)))
				    (if (stringp (first form))
					(setq doc-string (pop form))
					nil)
				    (destructuring-bind (&key =) form
				      (let ((arg-sentences
					     (sentences-for-function-arglist
					      name (butlast args)
					      (first (last args))
					      kb language)))
					(if arg-sentences
					    `(:and (:= (,name ,@args) ,=)
					      ,@arg-sentences)
					    `(:= (,name ,@args) ,=))))))
				 (:partial
				  (let ((args (pop form)))
				    (if (stringp (first form))
					(setq doc-string (pop form))
					nil)
				    (destructuring-bind (&key -> <= =>) form
				      (let ((extra-sentences
					     (sentences-for-function-arglist
					      name args -> kb language))
					    (s (cond
						 (=> `(:=> (:= (,name ,@args)
							    ,->)
						       ,=>))
						 (<= `(:<= (:= (,name ,@args)
							    ,->)
						       ,<=))
						 (t nil))))
					(when (or => <=)
					  (setq
					   extra-sentences
					   (append
					    extra-sentences
					    (sentences-for-function-implication
					     name args -> kb language
					     (or => <=)))))
					(if extra-sentences
					    `(:and ,s ,@extra-sentences)
					    s)))))
				 (:unrestricted
				  (let ((arg-sentences
					 (sentences-for-function-arglist
					  name :none :none kb language)))
				    (if (stringp (first form))
					(setq doc-string (pop form))
					nil)
				    (let ((conjuncts (append arg-sentences
							     form)))
				      (if (rest conjuncts)
					  (cons :and conjuncts)
					  (first conjuncts)))))))
			   (:defrelation
			       (ecase type-of-definition
				 (:complete
				  (let ((args (pop form)))
				    (if (stringp (first form))
					(setq doc-string (pop form))
					nil)
				    (destructuring-bind (&key =) form
				      (let ((arg-sentences
					     (sentences-for-relation-arglist
					      name args kb language)))
					(if arg-sentences
					    `(:and (:<=> (,name ,@args) ,=)
					      ,@arg-sentences)
					    `(:<=> (,name ,@args) ,=))))))
				 (:partial
				  (let ((args (pop form)))
				    (if (stringp (first form))
					(setq doc-string (pop form))
					nil)
				    (destructuring-bind (&key <= =>) form
				      (let ((extra-sentences
					     (sentences-for-relation-arglist
					      name args kb language))
					    (s (cond (=> `(:=> (,name ,@args)
							   ,=>))
						     (<= `(:<= (,name ,@args)
							   ,<=))
						     (t nil))))
					(when (or => <=)
					  (setq
					   extra-sentences
					   (append
					    extra-sentences
					    (sentences-for-relation-implication
					     name args kb language
					     (or => <=)))))
					(if extra-sentences
					    `(:and ,s ,@extra-sentences)
					    s)))))
				 (:unrestricted
				  (let ((arg-sentences
					 (sentences-for-relation-arglist
					  name :none kb language)))
				    (if (stringp (first form))
					(setq doc-string (pop form))
					nil)
				    (let ((conjuncts (append arg-sentences
							     form)))
				      (if (rest conjuncts)
					  (cons :and conjuncts)
					  (first conjuncts)))))))
			   (:deflogical
			       (ecase type-of-definition
				 (:complete
				  (if (stringp (first form))
				      (setq doc-string (pop form))
				      nil)
				  (destructuring-bind (&key =) form
				    `(:= ,name ,=)))
				 (:partial
				  (if (stringp (first form))
				      (setq doc-string (pop form))
				      nil)
				  (destructuring-bind (&key <= =>) form
				    (cond (=> `(:=> ,name ,=>))
					  (<= `(:<= ,name ,<=))
					  (t nil))))
				 (:unrestricted
				  (if (stringp (first form))
				      (setq doc-string (pop form))
				      nil)
				  (if (rest form)
				      (cons :and form)
				      (first form)))))
			   (otherwise nil))))
		    (when (or sentence doc-string)
		      (let ((overall-sentence
			     (cond ((and sentence doc-string)
				    `(:and ,sentence
				      (:documentation ,name ,doc-string)))
				   (doc-string
				    `(:documentation ,name ,doc-string))
				   (sentence sentence)
				   (t (error "Should never get here.")))))
			(handle-sentence-assertion
			 frame-handle-mapping-table
			 handle-to-name-mapping-table overall-sentence kb
			 (coerce-to-frame-internal name kb nil kb-local-only-p)
			 value-selector kb-local-only-p sentence-action
			 language)))))
		t))
	    nil))
      nil))

(defokbcgeneric ok-utils:find-language (language-specifier &optional error-p)
  (:documentation "Finds the representation of the language specified."))

(defmethod ok-utils:find-language
 ((language abstract-language) &optional (error-p t))
 (declare (ignore error-p))
 language)

(defmethod ok-utils:find-language ((sym symbol) &optional (error-p t))
 (or (cond ((not sym) nil)
	   ((keywordp sym)
	    (or (find-language (find-symbol (symbol-name sym) 'ok-utils) nil)
		(find-language (find-symbol (symbol-name sym) 'ok-back) nil)
		(and (not (search "-LANGUAGE" (symbol-name sym) :test #'char=))
		     (or (find-language
			  (find-symbol (concatenate 'string (symbol-name sym)
						    "-LANGUAGE")
				       'ok-utils)
			  nil)
			 (find-language
			  (find-symbol (concatenate 'string (symbol-name sym)
						    "-LANGUAGE")
				       'ok-back)
			  nil)))))
	   (t (let ((class (find-class sym)))
		(if (subtypep class 'abstract-language)
		    (class-prototype-safe class)
		    (if (search "-LANGUAGE" (symbol-name sym) :test #'char=)
			nil
			(find-language (intern (concatenate
						'string (symbol-name sym)
						"-LANGUAGE")
					       :keyword)
				       nil))))))
     (if error-p
	 (error "Cannot find the language called ~S" sym)
	 nil)))

(defokbcgeneric walk-subexpression (kb production language known-context-type
				       bound-vars expression function-to-apply)
  (:documentation 
   "The generic function used by <code>walk-form</code> for recursive
    descent of expressions as they are walked.  You should specialize this
    generic function if you want to add new productions to the grammar on
    a per-KB basis.  The arguments are the same as for
    <code>walk-form</code>."))

(defmethods walk-subexpression ((kb t)
				(production T) (language t) known-context-type
				bound-vars
				expression function-to-apply)
  "The fall-through method for walk-subexpression.  Just call the function
   on the expression and return the result."
  (funcall function-to-apply kb production known-context-type bound-vars
	   expression))

(defvar ok-utils:*parser-warn-function* 'default-parser-warn
  "The function called when a parse error or warning is issued.")

(defvar *err-on-parser-error-p* nil
  "When true causes OKBC's parser to err out whenever it hits a parse error.")

(defun default-parser-warn (kb format-string &rest args)
  (let ((*print-readably* nil))
    (let ((real-string (if *expression-being-walked*
			   (concatenate 'string "~A~%" format-string)
			   (concatenate 'string "~A" format-string)))
	  (heading (if *expression-being-walked*
		       (let ((*print-length* 4)
			     (*print-level* 3))
			 (let ((string (value-as-string-internal
					*expression-being-walked*
					kb :user-interface nil nil)))
			   (format nil "Whilst in expression ~A: "
			     string)))
		       "")))
      (if *err-on-parser-error-p*
	  (apply 'cerror "Go ahead anyway" real-string heading args)
	  (apply 'warn real-string heading args)))))

(defun parser-warn (tag kb &rest args)
  "The function called when the OKBC code walker encounters a parser error
   that it wants to warn about."
  (declare (ignore tag))
  (when *parser-warn-function*
    (if (boundp '*error-messages-in-this-top-level-form*)
	(let ((key (list kb args)))
	  (if (member key (gethash *expression-being-walked*
				   *error-messages-in-this-top-level-form*)
		      :test #'equal)
	      nil
	      (progn (push key
			   (gethash *expression-being-walked*
				    *error-messages-in-this-top-level-form*))
		     (apply *parser-warn-function* kb args))))
	(apply *parser-warn-function* kb args))))

(defmethods walk-subexpression ((kb t)
				(production (eql :form))
				(language kif-3.0-language)
				known-context-type bound-vars expression
				function-to-apply)
  (funcall
   function-to-apply kb production known-context-type bound-vars
   (cond ((consp expression)
	  (let ((op (first expression)))
	    (cond 
	      ((rule-operator-p op)
	       (walk-subexpression 
		kb :rule language known-context-type bound-vars
		(parser-cons expression (rule-operator-p op) (rest expression))
		function-to-apply))
	      ((and (definition-operator-p op language)
		    (not (non-defining-definition-operator-p op language)))
	       (walk-subexpression 
		kb :definition language known-context-type bound-vars
		(parser-cons expression (definition-operator-p op language)
			     (rest expression))
		function-to-apply))
	      ((let ((production
		      (term-type-of-operator op expression kb language nil)))
		 (and production (not (eq :funterm production))))
	       (walk-subexpression
		kb :term language known-context-type bound-vars
		(let ((canonical
		       (cl::nth-value
			1 (term-type-of-operator
			   op expression kb language nil))))
		  (if canonical
		      (parser-cons expression canonical (rest expression))
		      expression))
		function-to-apply))
	      ((or (symbolp op) (frame-reference-p op kb)
		   (sentence-op-type op expression kb language))
	       (walk-subexpression
		kb :sentence language known-context-type bound-vars expression
		function-to-apply))
	      (t (parser-warn
		  'illegal-kif-expression kb
		  "This form is not a legal KIF sentence:~%~S" expression)
		 (walk-subexpression kb :lisp-object language
				     known-context-type
				     bound-vars expression
				     function-to-apply)))))
	 ;; We know this must be a logical constant, 
	 ;; but it is playing the part of a propositional sentence...
	 ;; (which passes it through to logical constant, 
	 ;; which traps illegal symbols used as sentences.)
	 ((or (symbolp expression) (frame-reference-p expression kb))
	  (walk-subexpression
	   kb :sentence language known-context-type bound-vars expression
	   function-to-apply))
	 (t
	  (parser-warn
	   'illegal-kif-expression kb
	   "The form ~S ~% is not a legal top-level form for KIF.~%~
            It may be intended as a term." expression)
	  (walk-subexpression kb :lisp-object language
			      known-context-type
			      bound-vars expression
			      function-to-apply)))))

(defmethods walk-subexpression ((kb t)
				(production (eql :form))
				(language ansi-kif-language)
				known-context-type bound-vars expression
				function-to-apply)
  (funcall
   function-to-apply kb production known-context-type bound-vars
   (cond ((consp expression)
	  (let ((op (first expression)))
	    (cond 
	      ((and (definition-operator-p op language)
		    (not (non-defining-definition-operator-p op language)))
	       (walk-subexpression 
		kb :definition language known-context-type bound-vars
		(parser-cons expression (definition-operator-p op language)
			     (rest expression))
		function-to-apply))
	      ((or (symbolp op) (frame-reference-p op kb)
		   (sentence-op-type op expression kb language))
	       (walk-subexpression
		kb :sentence language known-context-type bound-vars expression
		function-to-apply))
	      (t (parser-warn
		  'illegal-kif-expression kb
		  "This form is not a legal KIF sentence:~%~S" expression)
		 (walk-subexpression kb :lisp-object language
				     known-context-type
				     bound-vars expression
				     function-to-apply)))))
	 ;; We know this must be a logical constant, 
	 ;; but it is playing the part of a propositional sentence...
	 ;; (which passes it through to logical constant, 
	 ;; which traps illegal symbols used as sentences.)
	 ((or (symbolp expression) (frame-reference-p expression kb))
	  (walk-subexpression
	   kb :sentence language known-context-type bound-vars expression
	   function-to-apply))
	 (t
	  (parser-warn
	   'illegal-kif-expression kb
	   "The form ~S ~% is not a legal top-level form for KIF.~%~
            It may be intended as a term." expression)
	  (walk-subexpression kb :lisp-object language
			      known-context-type
			      bound-vars expression
			      function-to-apply)))))

(defparameter *variables-ok-as-relation-expression-functors* nil)

(defokbcgeneric ok-utils:sentence-op-type
    (op expression kb language &optional warn-p)
  (:documentation
   "Returns the [KIF] syntax production name for the operator, which is the
    CAR of the expression with respect to the specified language."))

(defmethod sentence-op-type (op expression (kb t) language &optional
				(warn-p t))
  (cond ((logical-sentence-operator-p op kb language) :logsent)
	((sentence-quantification-operator-p op) :quantsent)
	((equality-operator-p op) :equation)
	((inequality-operator-p op) :inequality)
	((relation-constant-p op kb language) :relsent)
	((and *variables-ok-as-relation-expression-functors*
	      (variable? op))
	 :relsent)
	(warn-p
	 (parser-warn
	  'not-sentence-op kb
	  "The head of a KIF sentence must be an appropriate symbol.~%~
           This is not legal : ~S in KB ~S" expression (name kb))
	 nil)
	(t nil)))

(defmethods walk-subexpression ((kb t)
				(production (eql :sentence))
				(language abstract-kif-language)
				known-context-type bound-vars expression
				function-to-apply)
  "A sentence.  Dispatch on specific kind of sentence."
  (funcall function-to-apply kb production known-context-type bound-vars
	   (if (consp expression)
	       (let* ((op (first expression))
		      (op-type (sentence-op-type op expression kb language)))
		 (if op-type
		     (walk-subexpression kb op-type language known-context-type
					 bound-vars expression
					 function-to-apply)
		     (progn (parser-warn
			     'not-sentence-op kb
			     "The head of a KIF sentence must be an ~
                              appropriate symbol.~% This is not legal : ~S"
			     expression)
			    (walk-subexpression kb :lisp-object language
						known-context-type
						bound-vars expression
						function-to-apply))))
	       (etypecase language
		 (kif-3.0-language
		  (walk-subexpression 
		   kb :logconst language known-context-type bound-vars
		   expression function-to-apply))
		 (ansi-kif-language
		  (walk-subexpression 
		   kb :constant language known-context-type bound-vars
		   expression function-to-apply))))))

(defmethods walk-subexpression ((kb t)
				(production (eql :logconst))
				(language abstract-kif-language)
				known-context-type bound-vars expression
				function-to-apply)
  "A constant denoting a truth value."
  (when (not (logical-constant-p expression kb language))
    (parser-warn 'illegal-logical-constant kb
		 "~S should be a logical constant." expression))
  (funcall function-to-apply kb production known-context-type bound-vars
	   expression))


(defmethods walk-subexpression ((kb t)
				(production (eql :relsent))
				(language abstract-kif-language)
				known-context-type bound-vars expression
				function-to-apply)
  "A sentence such as (<relation> <term> <term>...)"
  (if (not (consp expression))
      (progn (parser-warn
	      'illegal-relational-sentence kb
	      "This form is not a legal relational sentence:~%~S" expression)
	     (walk-subexpression kb :lisp-object language
				 known-context-type
				 bound-vars expression
				 function-to-apply))
      (let ((relation-context-type
	     (case (length (rest expression))
	       (1 :class)
	       (2 :slot)
	       (otherwise known-context-type))))
	(funcall function-to-apply kb production known-context-type bound-vars
		 (parser-list*
		  expression
		  (if (and *variables-ok-as-relation-expression-functors*
			   (variable? (first expression)))
		      (walk-subexpression 
		       kb :variable language relation-context-type bound-vars
		       (first expression) function-to-apply)
		      (walk-subexpression 
		       kb :relconst language relation-context-type
		       bound-vars (first expression) function-to-apply))
		  (walk-subexpression
		   kb :term-list language known-context-type bound-vars
		   (rest expression) function-to-apply))))))

(defmethods walk-subexpression ((kb t)
				(production (eql :relsent))
				(language ansi-kif-language)
				known-context-type bound-vars expression
				function-to-apply)
  "A sentence such as (<relation> <term> <term>...)"
  (if (and (consp expression) (holds-operator-p (first expression)))
      (funcall function-to-apply kb production known-context-type bound-vars
	       (parser-list*
		expression
		(walk-subexpression kb :kif-operator language
				    known-context-type bound-vars
				    (holds-operator-p (first expression))
				    function-to-apply)
		(walk-subexpression
		 kb :term-list language known-context-type bound-vars
		 (rest expression) function-to-apply)))
      (call-next-method)))


(defmethods walk-subexpression ((kb t)
				(production (eql :equation))
				(language abstract-kif-language)
				known-context-type bound-vars expression
				function-to-apply)
  "A sentence of the form (= <term> <term>)."
  (if (or (not (consp expression)) (not (equal (length expression) 3))
	  (not (equality-operator-p (first expression))))
      (progn (parser-warn 'illegal-kif-equation kb
			  "~S is an illegal Equation." expression)
	     (walk-subexpression kb :lisp-object language known-context-type
				 bound-vars expression function-to-apply))
      (funcall function-to-apply kb production known-context-type bound-vars
	       (parser-list expression
			    (walk-subexpression
			     kb :kif-operator language known-context-type
			     bound-vars
			     (equality-operator-p (first expression))
			     function-to-apply)
			    (walk-subexpression
			     kb :term language known-context-type bound-vars
			     (second expression) function-to-apply)
			    (walk-subexpression
			     kb :term language known-context-type bound-vars
			     (third expression) function-to-apply)))))

(defmethods walk-subexpression ((kb t)
				(production (eql :inequality))
				(language abstract-kif-language)
				known-context-type bound-vars expression
				function-to-apply)
  "A sentence of the form (/= <term> <term>)."
  (if (or (not (consp expression)) (not (equal (length expression) 3))
	  (not (inequality-operator-p (first expression))))
      (progn (parser-warn 'illegal-kif-inequality kb
			  "~S is an illegal Inequality." expression)
	     (walk-subexpression kb :lisp-object language known-context-type
				 bound-vars expression function-to-apply))
      (funcall function-to-apply kb production known-context-type bound-vars
	       (parser-list expression
			    (walk-subexpression
			     kb :kif-operator language known-context-type
			     bound-vars
			     (inequality-operator-p (first expression))
			     function-to-apply)
			    (walk-subexpression
			     kb :term language known-context-type bound-vars
			     (second expression) function-to-apply)
			    (walk-subexpression
			     kb :term language known-context-type bound-vars
			     (third expression) function-to-apply)))))

(defmethods walk-subexpression ((kb t)
				(production (eql :logsent))
				(language abstract-kif-language)
				known-context-type bound-vars
				expression function-to-apply)
  "Sentences that start with AND, NOT, =>, etc."
  (walk-logsent kb production language known-context-type bound-vars
		expression function-to-apply))

(defun unconstrained-variable-p (x)
  (and (kif-variable-p x)
       (> (length (symbol-name x)) 1)
       (char= (char (symbol-name x) 1) #\_)))

(defmethod maybe-warn-of-unconstrained-variables
 (consequent-free-vars (antecedent-free-vars t) (kb t) (language t))
 (when consequent-free-vars
   (parser-warn
    'illegal-logical-sentence kb
    "Unconstrained free variable~p in rule consequence~%~{~S~^, ~}.~
     ~%Spell variables with leading underscore to~%~
     defeat this warning, e.g. ?_foo."
    (length consequent-free-vars) consequent-free-vars)))

(defun walk-backwards-implication (kb language known-context-type bound-vars
				      expression function-to-apply)
  (let ((consequent (second expression))
	(antecedents (rest (rest expression))))
    (flet ((doit ()
	     (let ((antecedent-results
		    (loop-for-x-in-l-collect
		     (sentence antecedents)
		     (walk-subexpression 
		      kb :sentence language known-context-type
		      (append *free-vars* bound-vars)
		      sentence function-to-apply))))
	       (let ((antecedent-vars (variables-in antecedents)))
		 (let ((consequent-result
			(walk-subexpression 
			 kb :sentence language known-context-type
			 (append *free-vars* bound-vars)
			 consequent function-to-apply)))
		   (let ((consequent-free-vars
			  (remove-if 'unconstrained-variable-p
				     (set-difference
				      (set-difference *free-vars*
						      antecedent-vars)
				      bound-vars))))
		     (maybe-warn-of-unconstrained-variables
		      consequent-free-vars antecedent-vars kb language)
		     (parser-cons (rest expression)
				  consequent-result antecedent-results)))))))
      (let ((old-free-vars *free-vars*))
	(let ((res nil))
	  (let ((*free-vars* *free-vars*))
	    (setq res (doit)))
	  (setq *free-vars* (append old-free-vars *free-vars*))
	  res)))))


(defun walk-forwards-implication (kb language known-context-type bound-vars
				      expression function-to-apply)
  (let ((consequent (first (last expression))))
    (flet ((doit ()
	     (let ((antecedent-vars nil))
	       (loop-for-x-in-l-collect
		(sentence (rest expression))
		(when (not (eq sentence consequent))
		  (setq antecedent-vars
			(variables-in sentence antecedent-vars)))
		(let ((res2 (walk-subexpression 
			    kb :sentence language known-context-type
			    (append *free-vars* bound-vars)
			    sentence function-to-apply)))
		  (when (eq sentence consequent)
		    (let ((consequent-free-vars
			   (remove-if 'unconstrained-variable-p
				      (set-difference
				       (set-difference *free-vars*
						       antecedent-vars)
				       bound-vars))))
		      (maybe-warn-of-unconstrained-variables
		       consequent-free-vars antecedent-vars kb language)
		      (setq *free-vars* consequent-free-vars)))
		  res2)))))
      (let ((old-free-vars *free-vars*))
	(let ((res nil))
	  (let ((*free-vars* *free-vars*))
	    (setq res (doit)))
	  (setq *free-vars* (append old-free-vars *free-vars*))
	  res)))))

(defmethod logsent-sentence-count-ok-p (op sentence-count (kb t) (language t))
 (case op
   ((:NOT) (= sentence-count 1))
   ((:<=>) (= sentence-count 2))
   ((:=> :<=) (> sentence-count 1))
   ((:AND :OR) (> sentence-count 0))))

(defmethod parse-logsent-as-backwards-implication-p (op (kb t) (language t))
 (member op '(:<= :<=>)))

(defmethod parse-logsent-as-forwards-implication-p (op (kb t) (language t))
 (member op '(:=>)))

(defmethod parse-logsent-as-conjunction-p (op (kb t) (language t))
 (member op '(:and)))

(defmethod parse-logsent-as-disjunction-p (op (kb t) (language t))
 (member op '(:or)))

(defmethod canonicalize-logsent-operator (op (kb t) (language t))
 (find op '(:not :<=> :=> :<= :and :or) :test #'string-equal))

(defmethod walk-logsent ((kb t)
			 (production (eql :logsent))
			 (language abstract-kif-language)
			 known-context-type bound-vars
			 expression function-to-apply)
 ;; check "arity"
 (if (not (consp expression))
     (progn (parser-warn 'illegal-logical-sentence kb
			 "~S is an illegal logical sentence." expression)
	    (walk-subexpression kb :lisp-object language known-context-type
				bound-vars expression function-to-apply))
     (let ((sentence-count (length (rest expression))))
       (let ((op (canonicalize-logsent-operator
		  (first expression) kb language)))
	 (unless (logsent-sentence-count-ok-p op sentence-count kb language)
	   (parser-warn 'illegal-logical-sentence kb
			"Wrong number of sentences after the ~A in ~%   ~A"
			(first expression) expression))
	 (funcall function-to-apply kb production known-context-type
		  bound-vars
		  (parser-cons
		   expression
		   (walk-subexpression 
		    kb :kif-operator language known-context-type bound-vars
		    (logical-sentence-operator-p
		     (first expression) kb language) function-to-apply)
		   (cond
		     ((or (parse-logsent-as-conjunction-p op kb language)
			  (parse-logsent-as-disjunction-p op kb language))
			  ;; Pick up bindings as we go through the conjuncts.
		      (flet ((doit ()
			       (loop-for-x-in-l-collect
				(sentence (rest expression))
				(walk-subexpression 
				 kb :sentence language
				 known-context-type
				 (append *free-vars*
					 bound-vars)
				 sentence function-to-apply))))
			(doit)))
		     ((parse-logsent-as-backwards-implication-p
		       op kb language)
		      (walk-backwards-implication
		       kb language known-context-type bound-vars
		       expression function-to-apply))
		     ((parse-logsent-as-forwards-implication-p
		       op kb language)
		      (walk-forwards-implication
		       kb language known-context-type bound-vars
		       expression function-to-apply))
		     (t (loop-for-x-in-l-collect
			 (sentence (rest expression))
			 (walk-subexpression 
			  kb :sentence language known-context-type
			  bound-vars sentence
			  function-to-apply))))))))))


(defmethods walk-subexpression ((kb t)
				(production (eql :variable-list))
				(language abstract-kif-language)
				known-context-type
				bound-vars expression function-to-apply)
  "Processes a binding list such as the quantified variables in 
an EXISTS sentence or the arguments in a DEFRELATION.  Enforces the
requirement that only the last argument can be a sequence variable."
  (if (consp expression)
      (funcall function-to-apply kb production known-context-type bound-vars
	       (loop-for-x-in-l-collect
		(variable expression)
		(walk-subexpression 
		 kb :variable language known-context-type bound-vars variable
		 function-to-apply)))
      (progn (parser-warn 'illegal-variable-list kb
			  "~S should be a variable list" expression)
	     (walk-subexpression kb :lisp-object language known-context-type
				 bound-vars expression function-to-apply))))


(defmethods walk-subexpression ((kb t)
				(production (eql :definition-variable-list))
				(language abstract-kif-language)
				known-context-type
				bound-vars expression function-to-apply)
  (if (consp expression)
      (if (loop for var in expression
		for rest on expression
		thereis (and (rest rest) (sequence-variable-p var)))
	  (progn (parser-warn 'illegal-variable-list kb
			      "~S cannot have a sequence variable anywhere ~
                               other than at the righthand most position."
			      expression)
		 (walk-subexpression kb :lisp-object language
				     known-context-type bound-vars expression
				     function-to-apply))
	  (funcall function-to-apply kb production known-context-type
		   bound-vars
		   (loop-for-x-in-l-collect
		    (variable expression)
		    (walk-subexpression 
		     kb :variable language known-context-type bound-vars
		     variable function-to-apply))))
      (progn (parser-warn 'illegal-variable-list kb
			  "~S should be a variable list" expression)
	     (walk-subexpression kb :lisp-object language known-context-type
				 bound-vars expression function-to-apply))))


(defun listp-or-kif-nil (x)
  (or (listp x) (nil-p x)))

(defun nil-p (x)
  (and (symbolp x) (string-equal x "NIL")))

(defun nil-symbol (x)
  (and (symbolp x)
       (string-equal x "NIL")
       (if *replace-kif-symbols-with-keywords-p*
	   nil
	   x)))

(defun list-or-kif (x)
  (if (listp x)
      x
      (if (and (symbolp x) (string-equal x "NIL"))
	  nil
	  (error "Illegal list value."))))

(defmethods walk-subexpression ((kb t)
				(production (eql :term-list))
				(language abstract-kif-language)
				known-context-type
				bound-vars expression function-to-apply)
  "Processes a list of terms that would be given as arguments
   to a relation or term."
  (if (loop for term in expression
	    for tail on expression
	    thereis (and (sequence-variable-p term) (rest tail)))
      (progn (parser-warn 'illegal-term-list kb
			  "A sequence variable appears in a position other ~
                           than the last in the term list: ~S" expression)
	     (walk-subexpression kb :lisp-object language known-context-type
				 bound-vars expression function-to-apply))
      (if (listp-or-kif-nil expression)
	  (funcall function-to-apply kb production known-context-type
		   bound-vars
		   (let ((real-list (list-or-kif expression)))
		     (if (loop for term in expression
			       thereis (sequence-variable-p term))
			 (loop-for-location-in-l-collect-list
			  (location real-list)
			  (walk-subexpression
			   kb (if (sequence-variable-p (first location))
				  :seqvar-location
				  :car)
			   language known-context-type
			   bound-vars location function-to-apply))
			 (loop-for-x-in-l-collect
			  (term real-list)
			  (walk-subexpression
			   kb :term language known-context-type
			   bound-vars term function-to-apply)))))
	  (progn (parser-warn 'illegal-term-list kb
			      "~S should be a term list" expression)
		 (walk-subexpression kb :lisp-object language
				     known-context-type bound-vars expression
				     function-to-apply)))))

(defmethods walk-subexpression ((kb t)
				(production (eql :constant-list))
				(language abstract-kif-language)
				known-context-type
				bound-vars expression function-to-apply)
  "Processes a list of constants."
  (if (listp-or-kif-nil expression)
      (funcall function-to-apply kb production known-context-type bound-vars
	       (loop-for-x-in-l-collect
		(term (list-or-kif expression))
		(walk-subexpression
		 kb :constant language known-context-type bound-vars term
		 function-to-apply)))
      (progn (parser-warn 'illegal-constant-list kb
			  "~S should be a constant list" expression)
	     (walk-subexpression kb :lisp-object language known-context-type
				 bound-vars expression function-to-apply))))

(defmethods walk-subexpression ((kb t)
				(production (eql :quantsent))
				(language kif-3.0-language)
				known-context-type
				bound-vars expression function-to-apply)
  "Sentences that start with FORALL or EXISTS."
  (if (or (not (consp expression)) (not (>= (length expression) 3))
	  (not (sentence-quantification-operator-p (first expression))))
      (progn (parser-warn 'illegal-quantified-sentence kb
			  "~S should be a legal quantified sentence"
			  expression)
	     (walk-subexpression kb :lisp-object language known-context-type
				 bound-vars expression function-to-apply))
      (let* ((arg-list (second expression))
	     (new-vars (if (and arg-list (symbolp arg-list))
			   (list arg-list)
			   arg-list)))
	(funcall function-to-apply kb production known-context-type
		 bound-vars
		 (parser-list expression
			      (walk-subexpression
			       kb :kif-operator language known-context-type
			       bound-vars (sentence-quantification-operator-p
					   (first expression))
			       function-to-apply)
			      (loop-for-x-in-l-collect
			       (variable new-vars)
			       (walk-subexpression 
				kb :variable language known-context-type
				(cons variable bound-vars) variable
				function-to-apply))
			      (walk-subexpression
			       kb :sentence language known-context-type
			       (append new-vars bound-vars) 
			       (if (> (length expression) 3)
				   (progn
				     (parser-warn
				      'obsolete-kif-syntax kb
				      "~a sentences should ~
                                         contain only a single sentence.~%~
                                         The multiple sentences in this ~
                                         quantification will be~%~
	                                 conjunctively combined:~%  ~a"
				      (first expression) expression)
				     `(:AND ,@(copy-list
					       (nthcdr 2 expression))))
				   (third expression))
			       function-to-apply))))))

(defmethods walk-subexpression ((kb t)
				(production (eql :quantsent))
				(language ansi-kif-language)
				known-context-type
				bound-vars expression function-to-apply)
  "Sentences that start with FORALL or EXISTS."
  (if (or (not (consp expression)) (not (>= (length expression) 3))
	  (not (sentence-quantification-operator-p (first expression))))
      (progn (parser-warn 'illegal-quantified-sentence kb
			  "~S should be a legal quantified sentence"
			  expression)
	     (walk-subexpression kb :lisp-object language known-context-type
				 bound-vars expression function-to-apply))
      (let* ((arg-list (second expression))
	     (new-vars (if (and arg-list (symbolp arg-list))
			   (list arg-list)
			   (loop for x in arg-list
				 collect (first-if-list x)))))
	(when (not (consp (second expression)))
	  (parser-warn
	   'illegal-varspec-list kb
	   "The variables for a quantified sentence must be a list in ~
              ANSI KIF.  ~S will be listified."
	   arg-list)
	  (setf arg-list (list arg-list)))
	(funcall function-to-apply kb production known-context-type
		 bound-vars
		 (parser-list expression
			      (walk-subexpression
			       kb :kif-operator language known-context-type
			       bound-vars (sentence-quantification-operator-p
					   (first expression))
			       function-to-apply)
			      (walk-subexpression
			       kb :varspec-list language known-context-type
			       bound-vars arg-list function-to-apply)
			      (walk-subexpression
			       kb :sentence language known-context-type
			       (append new-vars bound-vars) 
			       (if (> (length expression) 3)
				   (progn
				     (parser-warn
				      'obsolete-kif-syntax kb
				      "~a sentences should ~
                                         contain only a single sentence.~%~
                                         The multiple sentences in this ~
                                         quantification will be~%~
	                                 conjunctively combined:~%  ~a"
				      (first expression) expression)
				     `(:AND ,@(copy-list
					       (nthcdr 2 expression))))
				   (third expression))
			       function-to-apply))))))

(defmethods walk-subexpression ((kb t)
				(production (eql :varspec-list))
				(language ansi-kif-language)
				known-context-type
				bound-vars expression function-to-apply)
  (if (or (not (consp expression))
	  (loop for x in expression
		thereis (not (or (kif-variable-p x)
				 (and (consp x) (kif-variable-p (first x)))))))
      (progn (parser-warn 'illegal-varspec-list kb
			  "~S should be a list of varspecs"
			  expression)
	     (walk-subexpression kb :lisp-object language known-context-type
				 bound-vars expression function-to-apply))
      (funcall function-to-apply kb production known-context-type
	       bound-vars
	       (loop-for-x-in-l-collect
		(varspec expression)
		(walk-subexpression
		 kb :varspec language known-context-type bound-vars varspec
		 function-to-apply)))))

(defmethods walk-subexpression ((kb t)
				(production (eql :varspec))
				(language ansi-kif-language)
				known-context-type
				bound-vars expression function-to-apply)
  (cond ((kif-variable-p expression)
	 (funcall function-to-apply kb production known-context-type
		  bound-vars (walk-subexpression
			      kb :variable language known-context-type
			      ;; This will be a bound var
			      (cons expression bound-vars)
			      expression function-to-apply)))
	((and (consp expression) (kif-variable-p (first expression)))
	 (when (rest (rest expression))
	   (parser-warn 'illegal-varspec kb
			"Junk found at end of varspec: ~S"
			expression))
	 (funcall function-to-apply kb production known-context-type
		  bound-vars
		  (parser-list* expression
				(walk-subexpression
				 kb :variable language known-context-type
				 (cons (first expression) bound-vars)
				 (first expression)
				 function-to-apply)
				(walk-subexpression
				 kb :constant language known-context-type
				 bound-vars (second expression)
				 function-to-apply)
				(loop-for-x-in-l-collect
				 (thing (rest (rest expression)))
				 (walk-subexpression
				  kb :lisp-object language known-context-type
				  bound-vars thing function-to-apply)))))
	(t (parser-warn 'illegal-varspec-list kb "~S should be a varspec"
			  expression)
	     (walk-subexpression kb :lisp-object language known-context-type
				 bound-vars expression function-to-apply))))

(defmethods walk-subexpression ((kb t)
				(production (eql :rule))
				(language abstract-kif-language)
				known-context-type bound-vars expression
				function-to-apply)
  "An expression which is a KIF rule."
  (funcall
   function-to-apply kb production known-context-type bound-vars
   (if (consp expression)
       (let ((op (rule-operator-p (first expression))))
	 (cond ((string-equal op :<<=)
		(parser-list*
		 expression
		 (walk-subexpression kb :kif-operator language
				     known-context-type bound-vars op
				     function-to-apply)
		 (walk-subexpression kb :sentence language known-context-type
				     bound-vars (second expression)
				     function-to-apply)
		 (loop-for-x-in-l-collect
		  (premise (nthcdr 2 expression))
		  (walk-subexpression kb :premise language known-context-type
				      bound-vars premise function-to-apply))))
	       ((string-equal op :=>>)
		(parser-list*
		 expression
		 (walk-subexpression kb :kif-operator language
				     known-context-type bound-vars op
				     function-to-apply)
		 (loop-for-x-in-l-collect
		  (premise (butlast (rest expression)))
		  (walk-subexpression kb :premise language known-context-type
				      bound-vars premise function-to-apply))
		 (walk-subexpression kb :sentence language known-context-type
				     bound-vars (first (last expression))
				     function-to-apply)))
	       (t (parser-warn 'illegal-kif-rule kb "~a is not a KIF rule"
			       expression)
		  (walk-subexpression kb :lisp-object language
				      known-context-type bound-vars expression
				      function-to-apply))))
       (progn (parser-warn 'illegal-kif-rule kb
			   "~a is not a KIF rule" expression)
	      (walk-subexpression kb :lisp-object language known-context-type
				  bound-vars expression function-to-apply)))))


(defun with-kif-replacement (symbol with)
  "Used in the parser to replace KIF operator symbols with a similar symbol
   in a canonical package.  <code>Symbol</code> is replaced by
   a symbol with the same pname as <code>with</code> interned in the
   appropriate package."
  (if *replace-kif-symbols-with-keywords-p*
      (if (packagep *replace-kif-symbols-with-keywords-p*)
	  (intern (symbol-name with) *replace-kif-symbols-with-keywords-p*)
	  with)
      symbol))

(defmethods walk-subexpression ((kb t)
				(production (eql :premise))
				(language abstract-kif-language)
				known-context-type bound-vars expression
				function-to-apply)
  "An expression which is a premise of a KIF rule."
  (funcall function-to-apply kb production known-context-type bound-vars
	   (if (and (consp expression)
		    (symbolp (first expression))
		    (string-equal (first expression) :consis))
	       (parser-list expression
			    (walk-subexpression
			     kb :kif-operator language known-context-type
			     bound-vars
			     (with-kif-replacement (first expression) :consis)
			     function-to-apply)
			    (walk-subexpression
			     kb :sentence language known-context-type
			     bound-vars (second expression) function-to-apply))
	       (walk-subexpression
		kb :sentence language known-context-type bound-vars expression
		function-to-apply))))


(defmethods walk-subexpression ((kb t)
				(production (eql :definition))
				(language kif-3.0-language)
				known-context-type bound-vars expression
				function-to-apply)
  "An object, function or relation definition."
  (flet ((punt ()
	   (parser-warn 'illegal-kif-definition kb
			"~a is not a legal KIF 3.0 definition" expression)
	   (walk-subexpression 
	    kb :lisp-object language known-context-type bound-vars
	    expression function-to-apply)))
    (typecase expression
      (cons
       (typecase (first expression)
	 (symbol
	  (let ((production
		 (cond ((string-equal (first expression) :defobject)
			:object-definition)
		       ((string-equal (first expression) :deffunction)
			:function-definition)
		       ((string-equal (first expression) :defrelation)
			:relation-definition)
		       (t nil))))
	    (when (boundp '*expression-being-walked*)
	      (setq *expression-being-walked* (second expression)))
	    (if production
		(funcall function-to-apply kb production known-context-type
			 bound-vars
			 (walk-subexpression
			  kb
			  production
			  language known-context-type bound-vars expression
			  function-to-apply))
		(punt))))
	 (otherwise (punt))))
      (otherwise (punt)))))

(defmethods walk-subexpression ((kb t)
				(production (eql :definition))
				(language ansi-kif-language)
				known-context-type bound-vars expression
				function-to-apply)
  "An object, logical, function or relation definition."
  (flet ((punt ()
	   (parser-warn 'illegal-kif-definition kb
			"~a is not a legal ANSI KIF definition" expression)
	   (walk-subexpression 
	    kb :lisp-object language known-context-type bound-vars
	    expression function-to-apply)))
    (typecase expression
      (cons
       (typecase (first expression)
	 (symbol
	  (let ((production
		 (cond ((string-equal (first expression) :defobject)
			:object-definition)
		       ((string-equal (first expression) :deffunction)
			:function-definition)
		       ((string-equal (first expression) :defrelation)
			:relation-definition)
		       ((string-equal (first expression) :deflogical)
			:logical-definition)
		       (t nil))))
	    (when (boundp '*expression-being-walked*)
	      (setq *expression-being-walked* (second expression)))
	    (if production
		(funcall function-to-apply kb production known-context-type
			 bound-vars
			 (walk-subexpression
			  kb
			  production
			  language known-context-type bound-vars expression
			  function-to-apply))
		(punt))))
	 (otherwise (punt))))
      (otherwise (punt)))))
	      


(defmethods walk-subexpression ((kb t)
				(production (eql :object-definition))
				(language kif-3.0-language)
				known-context-type bound-vars
				expression function-to-apply)
  "An object definition."
  (funcall
   function-to-apply kb production known-context-type bound-vars
   (if (or (not (consp expression))
	   (not (and (symbolp (first expression))
		     (string-equal (first expression) :defobject))))
       (progn (parser-warn 'illegal-kif-defobject kb
			   "~a is not a KIF object definition" expression)
	      (walk-subexpression 
	       kb :lisp-object language known-context-type bound-vars
	       expression function-to-apply))
       (progn
	 (when (boundp '*expression-being-walked*)
	   (setq *expression-being-walked* (second expression)))
	 (let ((processed-constant
		(walk-subexpression 
		 kb :objconst language known-context-type bound-vars
		 (second expression) function-to-apply)))
	   (cond ((and (symbolp (third expression))
		       (string-equal (third expression) :=))
		  (funcall
		   function-to-apply kb :complete known-context-type bound-vars
		   (parser-list expression
				(walk-subexpression
				 kb :kif-operator language known-context-type
				 bound-vars (first expression)
				 function-to-apply)
				processed-constant
				(walk-subexpression
				 kb :kif-operator language known-context-type
				 bound-vars
				 (with-kif-replacement (third expression) :=)
				 function-to-apply)
				(walk-subexpression
				 kb :term language known-context-type
				 bound-vars (fourth expression)
				 function-to-apply))))
		 ((and (symbolp (third expression))
		       (string-equal (third expression) :conservative-axiom))
		  (funcall
		   function-to-apply kb :conservative known-context-type
		   bound-vars
		   (parser-list expression
				(walk-subexpression
				 kb :kif-operator language known-context-type
				 bound-vars (first expression)
				 function-to-apply)
				processed-constant
				(with-kif-replacement 
				    (third expression) :conservative-axiom)
				(walk-subexpression
				 kb :sentence language known-context-type
				 bound-vars (fourth expression)
				 function-to-apply))))
		 (t
		  (funcall
		   function-to-apply kb :unrestricted known-context-type
		   bound-vars
		   (parser-list*
		    expression
		    (first expression)
		    processed-constant
		    (loop-for-x-in-l-collect
		     (sentence (nthcdr 2 expression))
		     (walk-subexpression
		      kb :sentence language known-context-type bound-vars
		      sentence function-to-apply)))))))))))


(defmethods walk-subexpression ((kb t)
				(production (eql :object-definition))
				(language ansi-kif-language)
				known-context-type bound-vars
				expression function-to-apply)
  "An object definition.
    unrestricted ::=
      (defobject constant [string] sentence*) |
    complete ::=
      (defobject constant [string] := term) |
    partial ::=
      (defobject constant [string] :-> indvar :<= sentence) |
      (defobject constant [string] :-> indvar :=> sentence) |"
  (let ((definition-type :unrestricted))
    (let ((processed
	   (if (or (not (consp expression))
		   (not (and (symbolp (first expression))
			     (string-equal (first expression) :defobject))))
	       (progn (parser-warn 'illegal-kif-defobject kb
				   "~a is not a KIF object definition"
				   expression)
		      (walk-subexpression 
		       kb :lisp-object language known-context-type bound-vars
		       expression function-to-apply))
	       (progn
		 (when (boundp '*expression-being-walked*)
		   (setq *expression-being-walked* (second expression)))
		 (let ((processed-constant
			(walk-subexpression 
			 kb :objconst language known-context-type
			 bound-vars (second expression) function-to-apply))
		       (doc-string
			(if (stringp (third expression))
			    (walk-subexpression kb :lisp-object language
						known-context-type
						bound-vars (third expression)
						function-to-apply)
			    nil))
		       (body (if (stringp (third expression))
				 (nthcdr 3 expression)
				 (nthcdr 2 expression))))
		   (if (member (first body) '(:= :-> :<= :=>))
		       (destructuring-bind (&key -> <= = =>) body
			 (when =
			   (when (or -> <= =>)
			     (parser-warn
			      'illegal-kif-expression kb
			      "The form ~S ~% is not a legal top-level form ~
                               for ANSI KIF."
			      expression)))
			 (when (or (and => <=) (and (or <= =>) (not ->)))
			   (parser-warn
			    'illegal-kif-expression kb
			    "The form ~S ~% is not a legal top-level form for ~
                       ANSI KIF."
			    expression))
			 (cond (=;; complete form
				(setq definition-type :complete)
				(if doc-string
				    (parser-list
				     expression
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type bound-vars
				      (first expression) function-to-apply)
				     processed-constant
				     doc-string
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type bound-vars
				      (with-kif-replacement
					  (third expression) :=)
				      function-to-apply)
				     (walk-subexpression
				      kb :term language known-context-type
				      bound-vars (fourth expression)
				      function-to-apply))
				    (parser-list
				     expression
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type bound-vars
				      (first expression) function-to-apply)
				     processed-constant
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type bound-vars
				      (with-kif-replacement
					  (third expression) :=)
				      function-to-apply)
				     (walk-subexpression
				      kb :term language known-context-type
				      bound-vars (fourth expression)
				      function-to-apply))))
			       (t;; partial
				(setq definition-type :partial)
				(if doc-string
				    (parser-list
				     expression
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type bound-vars
				      (first expression) function-to-apply)
				     processed-constant
				     doc-string
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type bound-vars :->
				      function-to-apply)
				     (walk-subexpression
				      kb :indvar language known-context-type
				      bound-vars -> function-to-apply)
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type bound-vars
				      (if => :=> :<=)
				      function-to-apply)
				     (walk-subexpression
				      kb :sentence language known-context-type
				      bound-vars
				      (or => <=) function-to-apply))
				    (parser-list
				     expression
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type bound-vars
				      (first expression) function-to-apply)
				     processed-constant
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type bound-vars :->
				      function-to-apply)
				     (walk-subexpression
				      kb :indvar language known-context-type
				      bound-vars -> function-to-apply)
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type bound-vars
				      (if => :=> :<=) function-to-apply)
				     (walk-subexpression
				      kb :sentence language known-context-type
				      bound-vars (or => <=)
				      function-to-apply))))))
		       ;; Unrestricted form
		       (progn
			 (setq definition-type :unrestricted)
			 (if doc-string
			     (parser-list*
			      expression
			      (walk-subexpression
			       kb :kif-operator language known-context-type
			       bound-vars (first expression)
			       function-to-apply)
			      processed-constant
			      doc-string
			      (loop-for-x-in-l-collect
			       (sentence body)
			       (walk-subexpression
				kb :sentence language known-context-type
				bound-vars sentence function-to-apply)))
			     (parser-list*
			      expression
			      (walk-subexpression
			       kb :kif-operator language known-context-type
			       bound-vars (first expression)
			       function-to-apply)
			      processed-constant
			      (loop-for-x-in-l-collect
			       (sentence body)
			       (walk-subexpression
				kb :sentence language known-context-type
				bound-vars sentence
				function-to-apply)))))))))))
      (funcall
       function-to-apply kb production known-context-type bound-vars
       (funcall function-to-apply kb definition-type known-context-type
		bound-vars processed)))))

(defmethods walk-subexpression ((kb t)
				(production (eql :logical-definition))
				(language ansi-kif-language)
				known-context-type bound-vars
				expression function-to-apply)
  "A logical definition.
    unrestricted ::=
      (deflogical constant [string] sentence*)
    complete ::=
      (deflogical constant [string] := sentence)
    partial ::=
      (deflogical constant [string] :<= sentence)
      (deflogical constant [string] :=> sentence)"
  (let ((definition-type :unrestricted))
    (let ((processed
	   (if (or (not (consp expression))
		   (not (and (symbolp (first expression))
			     (string-equal (first expression) :deflogical))))
	       (progn (parser-warn 'illegal-kif-defobject kb
				   "~a is not a KIF object definition"
				   expression)
		      (walk-subexpression 
		       kb :lisp-object language known-context-type bound-vars
		       expression function-to-apply))
	       (progn
		 (when (boundp '*expression-being-walked*)
		   (setq *expression-being-walked* (second expression)))
		 (let ((processed-constant
			(walk-subexpression 
			 kb :objconst language known-context-type
			 bound-vars (second expression) function-to-apply))
		       (doc-string (if (stringp (third expression))
				       (walk-subexpression
					kb :lisp-object language
					known-context-type bound-vars
					(third expression) function-to-apply)
				       nil))
		       (body (if (stringp (third expression))
				 (nthcdr 3 expression)
				 (nthcdr 2 expression))))
		   (if (member (first body) '(:= :<= :=>))
		       (destructuring-bind (&key <= = =>) body
			 (when =
			   (when (or <= =>)
			     (parser-warn
			      'illegal-kif-expression kb
			      "The form ~S ~% is not a legal top-level form for ~
                       ANSI KIF."
			      expression)))
			 (when (and => <=)
			   (parser-warn
			    'illegal-kif-expression kb
			    "The form ~S ~% is not a legal top-level form for ~
                       ANSI KIF."
			    expression))
			 (cond (=;; complete form
				(setq definition-type :complete)
				(if doc-string
				    (parser-list
				     expression
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type bound-vars
				      (first expression)
				      function-to-apply)
				     processed-constant
				     doc-string
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type bound-vars
				      (with-kif-replacement
					  (third expression) :=)
				      function-to-apply)
				     (walk-subexpression
				      kb :term language known-context-type
				      bound-vars (fourth expression)
				      function-to-apply))
				    (parser-list
				     expression
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type bound-vars
				      (first expression)
				      function-to-apply)
				     processed-constant
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type bound-vars
				      (with-kif-replacement
					  (third expression) :=)
				      function-to-apply)
				     (walk-subexpression
				      kb :term language known-context-type
				      bound-vars (fourth expression)
				      function-to-apply))))
			       (t;; partial
				(setq definition-type :partial)
				(if doc-string
				    (parser-list
				     expression
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type
				      bound-vars (first expression)
				      function-to-apply)
				     processed-constant
				     doc-string
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type bound-vars
				      (if => :=> :<=) function-to-apply)
				     (walk-subexpression
				      kb :sentence language known-context-type
				      bound-vars (or => <=) function-to-apply))
				    (parser-list
				     expression
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type bound-vars
				      (first expression) function-to-apply)
				     processed-constant
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type bound-vars
				      (if => :=> :<=) function-to-apply)
				     (walk-subexpression
				      kb :sentence language known-context-type
				      bound-vars (or => <=)
				      function-to-apply))))))
		       ;; Unrestricted form
		       (progn
			 (setq definition-type :unrestricted)
			 (if doc-string
			     (parser-list*
			      expression
			      (walk-subexpression
			       kb :kif-operator language known-context-type
			       bound-vars (first expression)
			       function-to-apply)
			      processed-constant
			      doc-string
			      (loop-for-x-in-l-collect
			       (sentence body)
			       (walk-subexpression
				kb :sentence language known-context-type
				bound-vars sentence function-to-apply)))
			     (parser-list*
			      expression
			      (walk-subexpression
			       kb :kif-operator language known-context-type
			       bound-vars (first expression)
			       function-to-apply)
			      processed-constant
			      (loop-for-x-in-l-collect
			       (sentence body)
			       (walk-subexpression
				kb :sentence language known-context-type
				bound-vars sentence
				function-to-apply)))))))))))
      (funcall
       function-to-apply kb production known-context-type bound-vars
       (funcall
	function-to-apply kb definition-type known-context-type bound-vars
	processed)))))


(defmethods walk-subexpression ((kb t)
				(production (eql :function-definition))
				(language kif-3.0-language) known-context-type
				bound-vars expression function-to-apply)
  "A function definition."
  (funcall
   function-to-apply kb production known-context-type bound-vars
   (if (or (not (consp expression))
	   (not (and (symbolp (first expression))
		     (string-equal (first expression) :deffunction))))
       (progn (parser-warn 'illegal-kif-deffunction kb
			   "~a is not a KIF function definition" expression)
	      (walk-subexpression 
	       kb :lisp-object language known-context-type bound-vars
	       expression function-to-apply))
       (progn
	 (when (boundp '*expression-being-walked*)
	   (setq *expression-being-walked* (second expression)))
	 (let ((processed-constant
		(walk-subexpression
		 kb :funconst language known-context-type bound-vars
		 (second expression) function-to-apply))
	       (op (walk-subexpression
		    kb :kif-operator language known-context-type bound-vars
		    (definition-operator-p (first expression) language)
		    function-to-apply))
	       (third (third expression)))
	   (cond
	     ((and (symbolp (third expression))
		   (string-equal (third expression) :conservative-axiom))
	      (funcall
	       function-to-apply kb :conservative known-context-type bound-vars
	       (parser-list expression
			    op processed-constant
			    (with-kif-replacement (third expression)
			      :conservative-axiom)
			    (walk-subexpression
			     kb :sentence language known-context-type
			     bound-vars (fourth expression)
			     function-to-apply))))
	     ((and (listp third)
		   (kif-variable-p (first third)))
	      (funcall
	       function-to-apply kb :complete known-context-type bound-vars
	       (parser-list
		expression
		op processed-constant
		(walk-subexpression
		 kb :variable-list language known-context-type bound-vars third
		 function-to-apply)
		(walk-subexpression
		 kb :kif-operator language known-context-type bound-vars :=
		 function-to-apply);; is this right?
		(walk-subexpression
		 kb :term language known-context-type (append third bound-vars)
		 (fifth expression) function-to-apply))))
	     (t (funcall
		 function-to-apply kb :unrestricted known-context-type
		 bound-vars
		 (parser-list*
		  expression
		  op processed-constant
		  (loop-for-x-in-l-collect
		   (sentence (nthcdr 2 expression))
		   (walk-subexpression
		    kb :sentence language known-context-type bound-vars
		    sentence function-to-apply)))))))))))


(defun parse-doc-string-from-fun-or-rel
    (kb language known-context-type bound-vars expression function-to-apply)
  (if (and (consp (third expression))
	   (kif-variable-p (first (third expression))))
      (if  (stringp (fourth expression))
	   (walk-subexpression kb :lisp-object language
			       known-context-type
			       bound-vars
			       (fourth expression)
			       function-to-apply)
	   nil)
      (if  (stringp (third expression))
	   (walk-subexpression kb :lisp-object language
			       known-context-type
			       bound-vars
			       (third expression)
			       function-to-apply)
	   nil)))

(defun extract-body-from-fun-or-rel (expression)
  (if (and (consp (third expression))
	   (kif-variable-p (first (third expression))))
      (if (stringp (fourth expression))
	  (nthcdr 4 expression)
	  (nthcdr 3 expression))
      (if (stringp (third expression))
	  (nthcdr 3 expression)
	  (nthcdr 2 expression))))

(defmethods walk-subexpression ((kb t)
				(production (eql :function-definition))
				(language ansi-kif-language)
				known-context-type bound-vars
				expression function-to-apply)
  "A function definition.
    unrestricted ::=
      (deffunction constant [string] sentence*) |

    complete ::=
      (deffunction constant (indvar* [seqvar]) [string] := term) |

    partial ::=
      (deffunction constant (indvar* [seqvar]) [string]
        :-> indvar :<= sentence) |
      (deffunction constant (indvar* [seqvar]) [string]
        :-> indvar :=> sentence)"
  (let ((definition-type :unrestricted))
    (let ((processed
	   (if (or (not (consp expression))
		   (not (and (symbolp (first expression))
			     (string-equal (first expression) :deffunction))))
	       (progn (parser-warn 'illegal-kif-deffunction kb
				   "~a is not a KIF function definition"
				   expression)
		      (walk-subexpression 
		       kb :lisp-object language known-context-type bound-vars
		       expression function-to-apply))
	       (progn
		 (when (boundp '*expression-being-walked*)
		   (setq *expression-being-walked* (second expression)))
		 (let ((processed-constant
			(walk-subexpression 
			 kb :objconst language known-context-type
			 bound-vars (second expression) function-to-apply))
		       (arglist
			(if (and (consp (third expression))
				 (kif-variable-p (first (third expression))))
			    (walk-subexpression kb :definition-variable-list
						language known-context-type
						bound-vars (third expression)
						function-to-apply)
			    nil))
		       (doc-string
			(parse-doc-string-from-fun-or-rel
			 kb language known-context-type bound-vars expression
			 function-to-apply))
		       (body (extract-body-from-fun-or-rel expression)))
		   (if (member (first body) '(:= :-> :<= :=>))
		       (destructuring-bind (&key -> <= = =>) body
			 (when =
			   (when (or -> <= =>)
			     (parser-warn
			      'illegal-kif-expression kb
			      "The form ~S ~% is not a legal top-level form ~
                               for ANSI KIF."
			      expression)))
			 (when (or (and => <=) (and (or <= =>) (not ->)))
			   (parser-warn
			    'illegal-kif-expression kb
			    "The form ~S ~% is not a legal top-level form for ~
                             ANSI KIF."
			    expression))
			 (cond (=;; complete form
				(setq definition-type :complete)
				(if doc-string
				    (parser-list
				     expression
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type bound-vars
				      (first expression)
				      function-to-apply)
				     processed-constant
				     arglist
				     doc-string
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type bound-vars
				      (with-kif-replacement
					  (third expression) :=)
				      function-to-apply)
				     (walk-subexpression
				      kb :term language known-context-type
				      bound-vars
				      (fourth expression) function-to-apply))
				    (parser-list
				     expression
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type bound-vars
				      (first expression)
				      function-to-apply)
				     processed-constant
				     arglist
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type bound-vars
				      (with-kif-replacement
					  (third expression) :=)
				      function-to-apply)
				     (walk-subexpression
				      kb :term language known-context-type
				      bound-vars
				      (fourth expression) function-to-apply))))
			       (t;; partial
				(setq definition-type :partial)
				(if doc-string
				    (parser-list
				     expression
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type
				      bound-vars (first expression)
				      function-to-apply)
				     processed-constant
				     arglist
				     doc-string
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type bound-vars
				      :-> function-to-apply)
				     (walk-subexpression
				      kb :indvar language known-context-type
				      bound-vars -> function-to-apply)
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type
				      bound-vars (if => :=> :<=)
				      function-to-apply)
				     (walk-subexpression
				      kb :sentence language known-context-type
				      bound-vars (or => <=) function-to-apply))
				    (parser-list
				     expression
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type bound-vars
				      (first expression) function-to-apply)
				     processed-constant
				     arglist
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type bound-vars :->
				      function-to-apply)
				     (walk-subexpression
				      kb :indvar language
				      known-context-type bound-vars ->
				      function-to-apply)
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type bound-vars
				      (if => :=> :<=) function-to-apply)
				     (walk-subexpression
				      kb :sentence language known-context-type
				      bound-vars (or => <=)
				      function-to-apply))))))
		       ;; Unrestricted form
		       (progn
			 (setq definition-type :unrestricted)
			 (if doc-string
			     (parser-list*
			      expression
			      (walk-subexpression
			       kb :kif-operator language known-context-type
			       bound-vars (first expression)
			       function-to-apply)
			      processed-constant
			      doc-string
			      (loop-for-x-in-l-collect
			       (sentence body)
			       (walk-subexpression
				kb :sentence language known-context-type
				bound-vars sentence function-to-apply)))
			     (parser-list*
			      expression
			      (walk-subexpression
			       kb :kif-operator language known-context-type
			       bound-vars (first expression)
			       function-to-apply)
			      processed-constant
			      (loop-for-x-in-l-collect
			       (sentence body)
			       (walk-subexpression
				kb :sentence language known-context-type
				bound-vars sentence
				function-to-apply)))))))))))
      (funcall
       function-to-apply kb production known-context-type bound-vars
       (funcall
	function-to-apply kb definition-type known-context-type bound-vars
	processed)))))


(defmethods walk-subexpression ((kb t)
				(production (eql :relation-definition))
				(language kif-3.0-language) known-context-type
				bound-vars expression function-to-apply)
  "A relation definition."
  (funcall
   function-to-apply kb production known-context-type bound-vars
   (if (or (not (consp expression))
	   (not (and (symbolp (first expression))
		     (string-equal (first expression) :defrelation))))
       (progn (parser-warn 'illegal-kif-deffunction kb
			   "~a is not a KIF relation definition" expression)
	      (walk-subexpression 
	       kb :lisp-object language known-context-type bound-vars
	       expression function-to-apply))
       (progn
	 (when (boundp '*expression-being-walked*)
	   (setq *expression-being-walked* (second expression)))
	 (let ((processed-constant
		(walk-subexpression
		 kb :relconst language known-context-type bound-vars
		 (second expression) function-to-apply))
	       (op (walk-subexpression
		    kb :kif-operator language known-context-type bound-vars
		    (definition-operator-p (first expression) language)
		    function-to-apply))
	       (third (third expression)))
	   (cond
	     ((and (symbolp (third expression))
		   (string-equal (third expression) :conservative-axiom))
	      (funcall
	       function-to-apply kb :conservative known-context-type bound-vars
	       (parser-list expression
			    op processed-constant
			    (with-kif-replacement (third expression)
			      :conservative-axiom)
			    (walk-subexpression
			     kb :sentence language known-context-type
			     bound-vars (fourth expression)
			     function-to-apply))))
	     ((and (listp third)
		   (kif-variable-p (first third)))
	      (unless (and (symbolp (fourth expression))
			   (member (fourth expression) '(:= :=>)
				   :test #'string-equal))
		(parser-warn 'bad-keyword-in-defrelation kb
			     "Illegal syntax in defrelation: ~S" expression))
	      (funcall
	       function-to-apply kb
	       (cond ((member := expression) :complete)
		     ((member :conservative-axiom expression) :conservative)
		     (t :unrestricted))
	       known-context-type bound-vars
	       (parser-list*
		expression
		op processed-constant
		(walk-subexpression
		 kb :variable-list language known-context-type bound-vars third
		 function-to-apply)
		(walk-subexpression
		 kb :kif-operator language known-context-type bound-vars
		 (with-kif-replacement (fourth expression)
		   (find (fourth expression) '(:= :=>) :test #'string-equal))
		 function-to-apply)		 
		(walk-subexpression
		 kb :sentence language known-context-type
		 (append third bound-vars)
		 (fifth expression) function-to-apply)
		(when (sixth expression)
		  (list 
		   (if (and (symbolp (sixth expression))
			    (string-equal (sixth expression) :axiom))
		       (with-kif-replacement (sixth expression) :axiom)
		       (progn (parser-warn 'bad-keyword-in-defrelation kb
					   "Illegal syntax in defrelation: ~S"
					   expression)
			      (walk-subexpression
			       kb :lisp-object language known-context-type
			       bound-vars (sixth expression)
			       function-to-apply)))
		   (walk-subexpression
		    kb :sentence language known-context-type
		    (append third bound-vars) (seventh expression)
		    function-to-apply))))))
	     (t (funcall
		 function-to-apply kb :unrestricted known-context-type
		 bound-vars
		 (parser-list*
		  expression
		  op processed-constant
		  (loop-for-x-in-l-collect
		   (sentence (nthcdr 2 expression))
		   (walk-subexpression
		    kb :sentence language known-context-type bound-vars
		    sentence function-to-apply)))))))))))


(defmethods walk-subexpression ((kb t)
				(production (eql :relation-definition))
				(language ansi-kif-language)
				known-context-type bound-vars
				expression function-to-apply)
  "A relation definition.
    unrestricted ::=
      (defrelation constant [string] sentence*) |

    complete ::=
      (defrelation constant (indvar* [seqvar]) [string] := sentence) |

    partial ::=
      (defrelation constant (indvar* [seqvar]) [string]
        :<= sentence) |
      (defrelation constant (indvar* [seqvar]) [string]
        :=> sentence)"
  (let ((definition-type :unrestricted))
    (let ((processed
	   (if (or (not (consp expression))
		   (not (and (symbolp (first expression))
			     (string-equal (first expression) :defrelation))))
	       (progn (parser-warn 'illegal-kif-defrelation kb
				   "~a is not an ANSI KIF relation definition"
				   expression)
		      (walk-subexpression 
		       kb :lisp-object language known-context-type bound-vars
		       expression function-to-apply))
	       (progn
		 (when (boundp '*expression-being-walked*)
		   (setq *expression-being-walked* (second expression)))
		 (let ((processed-constant
			(walk-subexpression 
			 kb :objconst language known-context-type
			 bound-vars
			 (second expression) function-to-apply))
		       (arglist
			(if (and (consp (third expression))
				 (kif-variable-p (first (third expression))))
			    (walk-subexpression kb :definition-variable-list
						language known-context-type
						bound-vars (third expression)
						function-to-apply)
			    nil))
		       (doc-string
			(parse-doc-string-from-fun-or-rel
			 kb language known-context-type bound-vars expression
			 function-to-apply))
		       (body (extract-body-from-fun-or-rel expression)))
		   (if (member (first body) '(:= :<= :=>))
		       (destructuring-bind (&key <= = =>) body
			 (when =
			   (when (or <= =>)
			     (parser-warn
			      'illegal-kif-expression kb
			      "The form ~S ~% is not a legal top-level form ~
                               for ANSI KIF."
			      expression)))
			 (when (and => <=)
			   (parser-warn
			    'illegal-kif-expression kb
			    "The form ~S ~% is not a legal top-level form for ~
                             ANSI KIF."
			    expression))
			 (cond (=;; complete form
				(setq definition-type :complete)
				(if doc-string
				    (parser-list
				     expression
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type
				      bound-vars (first expression)
				      function-to-apply)
				     processed-constant
				     arglist
				     doc-string
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type
				      bound-vars
				      (with-kif-replacement
					  (third expression) :=)
				      function-to-apply)
				     (walk-subexpression
				      kb :term language known-context-type
				      bound-vars (fourth expression)
				      function-to-apply))
				    (parser-list
				     expression
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type
				      bound-vars (first expression)
				      function-to-apply)
				     processed-constant
				     arglist
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type
				      bound-vars
				      (with-kif-replacement
					  (third expression) :=)
				      function-to-apply)
				     (walk-subexpression
				      kb :term language known-context-type
				      bound-vars (fourth expression)
				      function-to-apply))))
			       (t;; partial
				(setq definition-type :partial)
				(if doc-string
				    (parser-list
				     expression
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type
				      bound-vars (first expression)
				      function-to-apply)
				     processed-constant
				     arglist
				     doc-string
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type
				      bound-vars (if => :=> :<=)
				      function-to-apply)
				     (walk-subexpression
				      kb :sentence language known-context-type
				      bound-vars (or => <=) function-to-apply))
				    (parser-list
				     expression
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type bound-vars
				      (first expression) function-to-apply)
				     processed-constant
				     arglist
				     (walk-subexpression
				      kb :kif-operator language
				      known-context-type bound-vars
				      (if => :=> :<=) function-to-apply)
				     (walk-subexpression
				      kb :sentence language known-context-type
				      bound-vars (or => <=)
				      function-to-apply))))))
		       ;; Unrestricted form
		       (progn
			 (setq definition-type :unrestricted)
			 (if doc-string
			     (parser-list*
			      expression
			      (walk-subexpression
			       kb :kif-operator language known-context-type
			       bound-vars (first expression)
			       function-to-apply)
			      processed-constant
			      doc-string
			      (loop-for-x-in-l-collect
			       (sentence body)
			       (walk-subexpression
				kb :sentence language known-context-type
				bound-vars sentence function-to-apply)))
			     (parser-list*
			      expression
			      (walk-subexpression
			       kb :kif-operator language known-context-type
			       bound-vars (first expression)
			       function-to-apply)
			      processed-constant
			      (loop-for-x-in-l-collect
			       (sentence body)
			       (walk-subexpression
				kb :sentence language known-context-type
				bound-vars sentence
				function-to-apply)))))))))))
      (funcall
       function-to-apply kb production known-context-type bound-vars
       (funcall
	function-to-apply kb definition-type known-context-type bound-vars
	processed)))))


(defmethod term-type-of-operator (operator expression kb language
					   &optional (barf-p t))
  (cond ((logical-term-operator-p operator)
	 (values :logterm (logical-term-operator-p operator)))
	((quotation-operator-p operator)
	 (values :quoterm (quotation-operator-p operator)))
	((list-operator-p operator)
	 (values :listterm (list-operator-p operator)))
	((function-constant-p operator kb language)
	 (values :funterm (function-constant-p operator kb language)))
	(barf-p
	 (parser-warn
	  'illegal-term-operator-expression kb
	  "The form ~S ~% is not a legal term." expression)
	 (values :funterm operator))
	(t nil)))

(defmethod term-type-of-operator (operator (expression t) (kb t)
					   (language kif-3.0-language)
					   &optional (barf-p t))
 (declare (ignore barf-p))
  (cond ((quantified-term-operator-p operator)
	 (values :quanterm (quantified-term-operator-p operator)))
	((set-operator-p operator)
	 (values :setterm (set-operator-p operator)))
	(t (call-next-method))))

(defmethod term-type-of-operator (operator (expression t) (kb t)
					   (language ansi-kif-language)
					   &optional (barf-p t))
 (declare (ignore barf-p))
  (cond ((value-operator-p operator)
	 (values :funterm (value-operator-p operator)))
	(t (call-next-method))))

(defmethods walk-subexpression ((kb t)
				(production (eql :term))
				(language abstract-kif-language)
				known-context-type bound-vars (expression cons)
				function-to-apply)
  "A term is an expression that denotes some thing, as distinct from a 
   sentence which has a truth value."
  (funcall function-to-apply kb production known-context-type bound-vars
	   (let ((operator (first expression)))
	     (walk-subexpression kb
				 (term-type-of-operator operator expression kb
							language)
				 language known-context-type bound-vars
				 expression function-to-apply))))

(defmethods walk-subexpression ((kb t)
				(production (eql :term))
				(language abstract-kif-language)
				known-context-type bound-vars
				(expression symbol) function-to-apply)
  "A term is an expression that denotes some thing, as distinct from a 
   sentence which has a truth value."
  (funcall function-to-apply kb production known-context-type bound-vars
	   (walk-subexpression
	    kb
	    (cond ((member expression bound-vars) :bound-variable)
		  ((kif-variable-p expression) :free-variable)
		  (t :constant))
	    language known-context-type bound-vars expression
	    function-to-apply)))

(defmethods walk-subexpression ((kb t)
				(production (eql :term))
				(language abstract-kif-language)
				known-context-type bound-vars
				(expression frame-handle) function-to-apply)
  "A term is an expression that denotes some thing, as distinct from a 
   sentence which has a truth value."
  (funcall function-to-apply kb production known-context-type bound-vars
	   (walk-subexpression
	    kb :constant language known-context-type bound-vars expression
	    function-to-apply)))

(defmethods walk-subexpression ((kb t)
				(production (eql :term))
				(language abstract-kif-language)
				known-context-type bound-vars expression
				function-to-apply)
  "A term is an expression that denotes some thing, as distinct from a 
sentence which has a truth value."
  (funcall function-to-apply kb production known-context-type bound-vars
	   (walk-subexpression
	    kb :constant language known-context-type bound-vars expression
	    function-to-apply)))

(defmethods walk-subexpression ((kb t)
				(production (eql :optional-term))
				(language abstract-kif-language)
				known-context-type bound-vars expression
				function-to-apply)
  (funcall function-to-apply kb production known-context-type bound-vars
	   (walk-subexpression kb
			       (if (member expression '(nil :nil) :test #'eq)
				   :lisp-object
				   :term)
			       language known-context-type bound-vars
			       expression function-to-apply)))

(defmethods walk-subexpression ((kb t)
				(production (eql :constant))
				(language abstract-kif-language)
				known-context-type bound-vars expression
				function-to-apply)
  "A constant of unknown production (object, function, or relation.)"
  (when (not (or (object-constant-p expression kb language)
		 (function-constant-p expression kb language)
		 (relation-constant-p expression kb language)
		 (logical-constant-p expression kb language)))
    (parser-warn 'illegal-constant kb "~S should be a constant" expression))
  (funcall function-to-apply kb production known-context-type bound-vars
	   expression))

(defmethods walk-subexpression ((kb t)
				(production (eql :operator))
				(language kif-3.0-language)
				known-context-type bound-vars expression
				function-to-apply)
  (cond ((rule-operator-p expression)
	 (let ((op (walk-subexpression
		    kb :ruleop language known-context-type bound-vars
		    expression function-to-apply)))
	   (funcall function-to-apply kb production known-context-type
		    bound-vars op)))
	(t (call-next-method))))

(defmethods walk-subexpression ((kb t)
				(production (eql :operator))
				(language abstract-kif-language)
				known-context-type bound-vars expression
				function-to-apply)
  (let ((op (cond ((rule-operator-p expression)
		   (walk-subexpression
		    kb :ruleop language known-context-type bound-vars
		    expression function-to-apply))
		  ((definition-operator-p expression language)
		   (walk-subexpression
		    kb :defop language known-context-type bound-vars
		    expression function-to-apply))
		  ((term-operator-p expression language)
		   (walk-subexpression
		    kb :termop language known-context-type bound-vars
		    expression function-to-apply))
		  ((sentence-operator-p expression kb language)
		   (walk-subexpression
		    kb :sentop language known-context-type bound-vars
		    expression function-to-apply))
		  (t (parser-warn 'illegal-operator kb
				  "~S should be an operator" expression)
		     (walk-subexpression
		      kb :lisp-object language known-context-type bound-vars
		      expression function-to-apply)))))
    (funcall function-to-apply kb production known-context-type bound-vars
	     op)))

(defmethods walk-subexpression ((kb t)
				(production (eql :termop))
				(language kif-3.0-language)
				known-context-type bound-vars expression
				function-to-apply)
  (let ((op (term-operator-p expression language)))
    (when (not op)
      (parser-warn 'illegal-termop kb
		   "Illegal KIF 3.0 termop token: ~S" expression))
    (walk-subexpression
     kb :lisp-object language known-context-type bound-vars
     (or op expression) function-to-apply)))

(defmethods walk-subexpression ((kb t)
				(production (eql :termop))
				(language ansi-kif-language)
				known-context-type bound-vars expression
				function-to-apply)
  (let ((op (term-operator-p expression language)))
    (when (not op)
      (parser-warn 'illegal-termop kb
		   "Illegal ANSI KIF termop token: ~S" expression))
    (walk-subexpression
     kb :lisp-object language known-context-type bound-vars
     (or op expression) function-to-apply)))

(defmethods walk-subexpression ((kb t)
				(production (eql :sentop))
				(language kif-3.0-language)
				known-context-type bound-vars expression
				function-to-apply)
  (let ((op (sentence-operator-p expression kb language)))
    (when (not op)
      (parser-warn 'illegal-sentop kb
		   "Illegal KIF 3.0 sentop token: ~S" expression))
    (walk-subexpression
     kb :lisp-object language known-context-type bound-vars
     (or op expression) function-to-apply)))

(defmethods walk-subexpression ((kb t)
				(production (eql :sentop))
				(language ansi-kif-language)
				known-context-type bound-vars expression
				function-to-apply)
  (let ((op (or (sentence-operator-p expression kb language)
		(holds-operator-p expression))))
    (when (not op)
      (parser-warn 'illegal-sentop kb
		   "Illegal ANSI KIF sentop token: ~S" expression))
    (walk-subexpression
     kb :lisp-object language known-context-type bound-vars
     (or op expression) function-to-apply)))

(defmethods walk-subexpression ((kb t)
				(production (eql :defop))
				(language abstract-kif-language)
				known-context-type bound-vars expression
				function-to-apply)
  (let ((op (definition-operator-p expression language)))
    (when (not op)
      (parser-warn 'illegal-defop kb
		   "Illegal KIF defop token: ~S" expression))
    (walk-subexpression
     kb :lisp-object language known-context-type bound-vars
     (or op expression) function-to-apply)))

(defmethods walk-subexpression ((kb t)
				(production (eql :variable)) (language t)
				known-context-type bound-vars expression
				function-to-apply)
  (if (not (kif-variable-p expression))
      (progn (parser-warn 'illegal-variable kb
			  "~S should be a variable" expression)
	     (walk-subexpression
	      kb :lisp-object language known-context-type bound-vars expression
	      function-to-apply))
      (funcall function-to-apply kb production known-context-type bound-vars
	       (walk-subexpression
		kb (if (sequence-variable-p expression) :seqvar :indvar)
		language known-context-type bound-vars expression
		function-to-apply))))

(defmethods walk-subexpression ((kb t)
				(production (eql :indvar)) (language t)
				known-context-type bound-vars expression
				function-to-apply)
  (if (not (variable? expression))
      (progn (parser-warn 'illegal-variable kb
			  "~S should be an individual variable" expression)
	     (walk-subexpression
	      kb :lisp-object language known-context-type bound-vars expression
	      function-to-apply))
      (funcall function-to-apply kb production known-context-type bound-vars
	       expression)))

(defmethods walk-subexpression ((kb t)
				(production (eql :seqvar)) (language t)
				known-context-type bound-vars expression
				function-to-apply)
  (if (not (sequence-variable-p expression))
      (progn (parser-warn 'illegal-variable kb
			  "~S should be an sequence variable" expression)
	     (walk-subexpression
	      kb :lisp-object language known-context-type bound-vars expression
	      function-to-apply))
      (funcall function-to-apply kb production known-context-type bound-vars
	       expression)))

(defmethods walk-subexpression
    ((kb t)
     (production (eql :seqvar-location)) (language t)
     known-context-type bound-vars expression
     function-to-apply)
  ;; Called on a list of the form (@foo).  It is useful for implementations
  ;; that want to be able to rewrite seqvars into dotted lists, e.g.
  ;; (?a ?b @c) -> (?a ?b . ?c)
  (if (not (and (consp expression)
		(not (rest expression))
		(sequence-variable-p (first expression))))
      (progn (parser-warn 'illegal-seqvar-location kb
			  "~S should be an sequence variable location"
			  expression)
	     (walk-subexpression
	      kb :lisp-object language known-context-type bound-vars expression
	      function-to-apply))
      (funcall function-to-apply kb production known-context-type bound-vars
	       (parser-list expression
			    (walk-subexpression
			     kb :seqvar language known-context-type
			     bound-vars (first expression)
			     function-to-apply)))))

(defmethods walk-subexpression ((kb t)
				(production (eql :car)) (language t)
				known-context-type bound-vars expression
				function-to-apply)
  ;; Called on a list of the form (a b @foo).  It's contract is to parse
  ;; the car of the list as a :term and return a list
  (if (not (consp expression))
      (progn (parser-warn 'illegal-cons kb
			  "~S should be a list of terms"
			  expression)
	     (walk-subexpression
	      kb :lisp-object language known-context-type bound-vars expression
	      function-to-apply))
      (let ((new-car (walk-subexpression
		      kb :term language known-context-type
		      bound-vars (first expression)
		      function-to-apply)))
	(funcall function-to-apply kb production known-context-type bound-vars
		 (parser-cons expression
			      new-car
			      (rest expression))))))

(defmethods walk-subexpression ((kb t)
				(production (eql :bound-variable)) (language t)
				known-context-type bound-vars expression
				function-to-apply)
  "A bound individual variable.  This method is called on references
   to the variable both in the binding list and as a term."
  (if (or (not (kif-variable-p expression))
	  (not (member expression bound-vars)))
      (parser-warn 'illegal-bound-variable kb
		   "~S should be a bound variable" expression)
      (funcall function-to-apply kb production known-context-type bound-vars
	       (walk-subexpression
		kb (if (sequence-variable-p expression) :seqvar :indvar)
		language known-context-type bound-vars expression
		function-to-apply))))

(defmethods walk-subexpression ((kb t)
				(production (eql :free-variable)) (language t)
				known-context-type bound-vars expression
				function-to-apply)
  "Reference to an unbound individual or sequence variable."
  (if (or (not (kif-variable-p expression))
	  (member expression bound-vars))
      (parser-warn 'illegal-free-variable kb
		   "~S should be a free variable" expression)
      (funcall function-to-apply kb production known-context-type bound-vars
	       (walk-subexpression
		kb (if (sequence-variable-p expression) :seqvar :indvar)
		language known-context-type bound-vars expression
		function-to-apply))))

(defmethods walk-subexpression :around
  ((kb t) (production (eql :free-variable)) (language t)
   known-context-type bound-vars expression
   function-to-apply)
  (notice-free-variable kb language known-context-type bound-vars expression
   function-to-apply)
  (call-next-method))

(defmethod notice-free-variable (kb language known-context-type bound-vars
				    expression function-to-apply)
 (declare (ignore kb language known-context-type function-to-apply))
 (declare (special *free-vars*))
 (when (and (boundp '*free-vars*)
	    (kif-variable-p expression)
	    (not (member expression bound-vars))
	    (not (member expression *free-vars*)))
   (push expression *free-vars*)))

(defmethods walk-subexpression ((kb t)
				(production (eql :funterm))
				(language abstract-kif-language)
				known-context-type bound-vars expression
				function-to-apply)
  "Expression is a function-constant applied to terms."
  (if (not (consp expression))
      (progn
	(parser-warn 'illegal-functional-term kb
		     "The form ~S ~% is not a legal functional term."
		     expression)
	(walk-subexpression kb :lisp-object language known-context-type
			    bound-vars expression function-to-apply))
      (progn
	(when (not (function-constant-p (first expression) kb language))
	  (parser-warn 'illegal-functional-term kb
		       "The form ~S ~% is not a legal functional term."
		       expression))
	(let ((function-context-type
	       (case (length (rest expression))
		 (1 :slot)
		 (otherwise known-context-type))))
	  (funcall function-to-apply kb production known-context-type
		   bound-vars
		   (destructuring-bind (function-constant &rest args)
		       expression
		     (parser-list*
		      expression
		      (walk-subexpression
		       kb :funconst language function-context-type
		       bound-vars function-constant function-to-apply)
		      (walk-subexpression kb :term-list language
					  known-context-type bound-vars args
					  function-to-apply))))))))

(defmethods walk-subexpression ((kb t)
				(production (eql :funterm))
				(language ansi-kif-language)
				known-context-type bound-vars expression
				function-to-apply)
  (if (and (consp expression) (value-operator-p (first expression)))
      (funcall function-to-apply kb production known-context-type
	       bound-vars
	       (destructuring-bind (value &rest args)
		   expression
		 (parser-list*
		  expression
		  (walk-subexpression
		   kb :kif-operator language known-context-type
		   bound-vars value function-to-apply)
		  (walk-subexpression kb :term-list language
				      known-context-type bound-vars args
				      function-to-apply))))
      (call-next-method)))

(defmethods walk-subexpression ((kb t)
				(production (eql :quoterm))
				(language kif-3.0-language)
				known-context-type bound-vars expression
				function-to-apply)
  "A quoted expression, including the quote."
  (if (not (consp expression))
      (progn
	(parser-warn 'illegal-quotation-term kb
		     "The form ~S ~% is not a legal quotation term."
		     expression)
	(walk-subexpression kb :lisp-object language known-context-type
			    bound-vars expression function-to-apply))
      (progn
	(when (not (quotation-operator-p (first expression)))
	  (parser-warn 'illegal-quotation-term kb
		       "The form ~S ~% is not a legal quotation term."
		       expression))
	(funcall function-to-apply kb production known-context-type bound-vars
		 (parser-list expression
			      (walk-subexpression
			       kb :kif-operator language known-context-type
			       bound-vars
			       (quotation-operator-p (first expression))
			       function-to-apply)
			      (walk-subexpression
			       kb :lisp-object language known-context-type
			       bound-vars (second expression)
			       function-to-apply))))))

(defmethods walk-subexpression ((kb t)
				(production (eql :quoterm))
				(language ansi-kif-language)
				known-context-type bound-vars expression
				function-to-apply)
  "A quoted expression, including the quote."
  (if (not (consp expression))
      (progn
	(parser-warn 'illegal-quotation-term kb
		     "The form ~S ~% is not a legal quotation term."
		     expression)
	(walk-subexpression kb :lisp-object language known-context-type
			    bound-vars expression function-to-apply))
      (progn
	(when (not (quotation-operator-p (first expression)))
	  (parser-warn 'illegal-quotation-term kb
		       "The form ~S ~% is not a legal quotation term."
		       expression))
	(funcall function-to-apply kb production known-context-type bound-vars
		 (parser-list expression
			      (walk-subexpression
			       kb :kif-operator language known-context-type
			       bound-vars
			       (quotation-operator-p (first expression))
			       function-to-apply)
			      (walk-subexpression
			       kb :listexpr language known-context-type
			       bound-vars (second expression)
			       function-to-apply))))))

(defmethods walk-subexpression ((kb t)
				(production (eql :listexpr))
				(language ansi-kif-language)
				known-context-type bound-vars expression
				function-to-apply)
  "A quoted expression, including the quote."
  (if (listp expression)
      (funcall function-to-apply kb production known-context-type bound-vars
	       (loop-for-x-in-l-collect
		(subexpression expression)
		(walk-subexpression 
		 kb :listexpr language known-context-type bound-vars
		 subexpression function-to-apply)))
      (funcall function-to-apply kb production known-context-type bound-vars
	       (walk-subexpression
		kb :atom language known-context-type
		bound-vars expression
		function-to-apply))))

(defmethods walk-subexpression ((kb t)
				(production (eql :atom))
				(language ansi-kif-language)
				known-context-type bound-vars expression
				function-to-apply)
  "A quoted expression, including the quote."
  (if (consp expression)
      (progn
	(parser-warn 'illegal-atom kb
		     "The form ~S ~% is not an atom." expression)
	(walk-subexpression kb :lisp-object language known-context-type
			    bound-vars expression function-to-apply))
      (funcall function-to-apply kb production known-context-type bound-vars
	       (walk-subexpression
		kb :lisp-object language known-context-type
		bound-vars expression
		function-to-apply))))


(defmethods walk-subexpression ((kb t)
				(production (eql :listterm))
				(language abstract-kif-language)
				known-context-type bound-vars expression
				function-to-apply)
  "A term which denotes a literal list."
  (if (not (consp expression))
      (progn
	(parser-warn 'illegal-list-term kb
		     "The form ~S ~% is not a legal list term." expression)
	(walk-subexpression kb :lisp-object language known-context-type
			    bound-vars expression function-to-apply))
      (progn
	(when (not (list-operator-p (first expression)))
	  (parser-warn 'illegal-list-term kb
		       "The form ~S ~% is not a legal list term." expression))
	(funcall function-to-apply kb production known-context-type bound-vars
		 (parser-cons expression
			      (list-operator-p (first expression))
			      (walk-subexpression
			       kb :term-list language known-context-type
			       bound-vars (rest expression)
			       function-to-apply))))))
	  

(defmethods walk-subexpression ((kb t)
				(production (eql :setterm))
				(language abstract-kif-language)
				known-context-type bound-vars expression
				function-to-apply)
  "A term which denotes a literal set."
  (if (not (consp expression))
      (progn
	(parser-warn 'illegal-list-term kb
		     "The form ~S ~% is not a legal set term." expression)
	(walk-subexpression kb :lisp-object language known-context-type
			    bound-vars expression function-to-apply))
      (progn
	(when (not (set-operator-p (first expression)))
	  (parser-warn 'illegal-set-term kb
		       "The form ~S ~% is not a legal set term." expression))
	(funcall function-to-apply kb production known-context-type bound-vars
		 (parser-cons expression
			      (walk-subexpression
			       kb :kif-operator language known-context-type
			       bound-vars (set-operator-p (first expression))
			       function-to-apply)
			      (walk-subexpression
			       kb :term-list language known-context-type
			       bound-vars (rest expression)
			       function-to-apply))))))
	  

(defmethod walk-kif-if-logterm (kb (language kif-3.0-language)
				   known-context-type bound-vars expression
				   function-to-apply)
 (parser-list*
  expression
  (walk-subexpression 
   kb :kif-operator language known-context-type
   bound-vars
   (with-kif-replacement (first expression) :if) function-to-apply)
  (walk-subexpression kb :sentence language known-context-type bound-vars
		      (second expression) function-to-apply)
  (if (third expression)
      (walk-subexpression kb :term language known-context-type bound-vars
			  (third expression) function-to-apply)
      (progn
	(parser-warn
	 'missing-term kb
	 "The syntax of KIF's IF statement is ~
          (if <sentence> <term1> [<term2>]).~%~
          This sentence is missing <term1>:~%~S"
	 (walk-subexpression kb :lisp-object language known-context-type
			     bound-vars (third expression)
			     function-to-apply))))
  (if (fourth expression)
      (list (walk-subexpression kb :term language known-context-type
				bound-vars (fourth expression)
				function-to-apply))
      '())))

(defmethod walk-kif-if-logterm (kb (language ansi-kif-language)
				   known-context-type bound-vars expression
				   function-to-apply)
 (let ((logpairs nil))
   (loop with tail = (rest expression)
	 for car = (pop tail)
	 do (if (rest tail)
		(progn (push (pop tail) logpairs)
		       (push car logpairs))
		(progn (push :---end logpairs)
		       (push car logpairs)
		       (return nil)))
	 when (not tail) return nil)
   (setq logpairs (nreverse logpairs))
   (parser-list*
    expression
    (walk-subexpression 
     kb :kif-operator language known-context-type
     bound-vars
     (with-kif-replacement (first expression) :if) function-to-apply)
    (loop-for-k/v-on-l-append-list
     (sentence term logpairs)
     (if (eq term :---end)
	 (list (walk-subexpression 
		kb :term language known-context-type bound-vars
		sentence function-to-apply)
	       (walk-subexpression 
		kb :logpair language known-context-type bound-vars
		(list sentence term) function-to-apply)))))))

(defmethods walk-subexpression ((kb t)
				(production (eql :logpair))
				(language ansi-kif-language)
				known-context-type bound-vars expression
				function-to-apply)
  (if (or (not (consp expression)) (not (= (length expression) 2)))
      (progn
	(parser-warn 'illegal-logpair kb
		     "The form ~S ~% is not a legal logpair." expression)
	(walk-subexpression kb :lisp-object language known-context-type
			    bound-vars expression function-to-apply))
      (funcall function-to-apply kb production known-context-type bound-vars
	       (parser-list expression
			    (walk-subexpression
			     kb :sentence language known-context-type
			     bound-vars (first expression) function-to-apply)
			    (walk-subexpression
			     kb :term language known-context-type
			     bound-vars (second expression)
			     function-to-apply)))))

(defmethods walk-subexpression ((kb t)
				(production (eql :logterm))
				(language abstract-kif-language)
				known-context-type bound-vars expression
				function-to-apply)
  "An expression that starts with IF or COND."
  (if (not (consp expression))
      (progn
	(parser-warn 'illegal-logical-term kb
		     "The form ~S ~% is not a legal logical term."
		     expression)
	(walk-subexpression kb :lisp-object language known-context-type
			    bound-vars expression function-to-apply))
      (progn
	(when (not (logical-term-operator-p (first expression)))
	  (parser-warn 'illegal-logical-term kb
		       "The form ~S ~% is not a legal logical term."
		       expression))
	(funcall function-to-apply kb production known-context-type bound-vars
		 (cond ((and (symbolp (first expression))
			     (string-equal (first expression) :if))
			(walk-kif-if-logterm
			 kb language known-context-type bound-vars expression
			 function-to-apply))
		       ((and (symbolp (first expression))
			     (string-equal (first expression) :cond))
			(parser-cons
			 expression
			 (walk-subexpression 
			  kb :kif-operator language known-context-type
			  bound-vars
			  (with-kif-replacement (first expression) :cond)
			  function-to-apply)
			 (loop-for-x-in-l-collect
			  (sentence.term (rest expression))
			  (if (and (consp sentence.term)
				   (= (length sentence.term) 2))
			      (let* ((sentence (first sentence.term))
				     (term (second sentence.term))
				     (new-sentence
				      (walk-subexpression 
				       kb :sentence language known-context-type
				       bound-vars sentence function-to-apply))
				     (new-term 
				      (walk-subexpression
				       kb :term language known-context-type
				       bound-vars (or term nil)
				       function-to-apply)))
				(parser-list sentence.term new-sentence
					     new-term))
			      (progn (parser-warn
				      'bad-cond-syntax kb
				      "The syntax of KIF's COND is~%~
                       (cond (<sentence> <term>) ... (<sentence> <term>))~%~
                       The following is illegal syntax:~%~S"
				      expression)
				     (walk-subexpression
				      kb :lisp-object language
				      known-context-type bound-vars expression
				      function-to-apply))))))
		       (t (parser-warn
			   'illegal-op kb "~S if an illegal logical ~
                                        term operator."
			   (first expression))
			  (walk-subexpression
			   kb :lisp-object language known-context-type
			   bound-vars expression function-to-apply)))))))


(defmethods walk-subexpression ((kb t)
				(production (eql :quanterm))
				(language abstract-kif-language)
				known-context-type bound-vars expression
				function-to-apply)
  "Expression is one that start with operators like setofall, kappa, lambda..."
  (if (or (not (consp expression)) (not (= (length expression) 3)))
      (progn
	(parser-warn 'illegal-quantified-term kb
		     "The form ~S ~% is not a legal quantified term."
		     expression)
	(walk-subexpression kb :lisp-object language known-context-type
			    bound-vars expression function-to-apply))
      (progn
	(when (not (quantified-term-operator-p (first expression)))
	  (parser-warn 'illegal-quantified-term kb
		       "The form ~S ~% is not a legal quantified term."
		       expression))
	
	(funcall
	 function-to-apply kb production known-context-type bound-vars
	 (destructuring-bind (operator arg1 arg2)
	     expression
	   (case operator
	     ((:the :setofall)
	      (parser-list expression
			   (walk-subexpression kb :kif-operator language
					       known-context-type
					       bound-vars
					       (quantified-term-operator-p
						operator)
					       function-to-apply)
			   (walk-subexpression kb :term language
					       known-context-type bound-vars
					       arg1 function-to-apply)
			   (walk-subexpression kb :sentence language
					       known-context-type bound-vars
					       arg2 function-to-apply)))
	     ((:setof)
	      (parser-list expression
			   (walk-subexpression kb :kif-operator language
					       known-context-type
					       bound-vars
					       (set-operator-p
						operator)
					       function-to-apply)
			   (walk-subexpression
			    kb :term-list language known-context-type
			    bound-vars (rest expression) function-to-apply)))
	     ((:lambda :kappa)
	      (parser-list expression
			   (walk-subexpression kb :kif-operator language
					       known-context-type
					       bound-vars
					       (quantified-term-operator-p
						operator)
					       function-to-apply)
			   (walk-subexpression
			    kb :variable-list language known-context-type
			    bound-vars arg1 function-to-apply)
			   (walk-subexpression 
			    kb
			    (if (string-equal operator :lambda)
				:term
				:sentence)
			    language known-context-type
			    (append arg1 bound-vars)
			    arg2 function-to-apply)))
	     (otherwise expression)))))))

(defmethods walk-subexpression ((kb t)
				(production (eql :funconst))
				(language abstract-kif-language)
				known-context-type
				bound-vars expression function-to-apply)
  "A constant denoting a function."
  (when (not (function-constant-p expression kb language))
    (parser-warn 'illegal-function-constant kb
		 "~S should be a function constant." expression))
  (funcall function-to-apply kb production known-context-type bound-vars
	   expression))


(defmethods walk-subexpression ((kb t)
				(production (eql :relconst))
				(language abstract-kif-language)
				known-context-type
				bound-vars expression function-to-apply)
  "A constant denoting a relation."
  (when (not (relation-constant-p expression kb language))
    (parser-warn 'illegal-relation-constant kb
		 "~S should be a relation constant." expression))
  (funcall function-to-apply kb production known-context-type bound-vars
	   expression))

(defokbcgeneric frame-reference-p (thing kb)
  (:documentation "A predicate that is true of a frame reference when running
    in the OKBC walker.  You may want to specialize this for your KB if you
    want to walk over expressions that contain embedded frame references."))

(defmethod frame-reference-p ((thing t) (kb t))
 (coercible-to-frame-p-internal thing kb nil))

(defmethod frame-reference-p ((thing frame-handle) (kb t)) thing)

(defokbcgeneric object-constant-p (thing kb language)
  (:documentation "A predicate in the walker that is true for object
   constants."))

(defmethod object-constant-p (thing (kb t) (language t))
 (and (atom thing)
      (or (numberp thing)
	  (characterp thing)
	  (stringp thing)
	  (if *symbols-ok-as-non-logical-constants-p*
	      (or (and (symbolp thing)
		       ;; Changed by JPR on 14-Oct-98.  It seems reasonable
		       ;; to have frames/object constants named by keywords.
		       ;; It even seems reasonable that they be uninterned,
		       ;; though presumably such frames cannot be written out.
		       ;;   (or (not (keywordp thing))
		       ;;       ;; Special case for this one.  It's in the
		       ;;       ;; knowledge model.
		       ;;        (member thing '(:union)))
		       ;;	 (symbol-package thing)
		       )
		  (frame-reference-p thing kb))
	      (frame-reference-p thing kb))
	  (not (kif-variable-p thing))
	  (not (kif-operator-p thing kb language)))))

(defokbcgeneric function-constant-p (thing kb language)
  (:documentation "A predicate in the walker that is true for function
   constants."))

(defmethod function-constant-p (thing kb language)
 (object-constant-p thing kb language))

(defokbcgeneric relation-constant-p (thing kb language)
  (:documentation "A predicate in the walker that is true for relation
   constants."))

(defmethod relation-constant-p (thing kb language)
 (declare (special *okbc-relation-symbols*
		   ok-back:*okbc-standard-class-names*
		   ok-back:*okbc-standard-slot-names*
		   ok-back:*okbc-standard-facet-names*))
 (or (member thing *okbc-relation-symbols*)
     (member thing ok-back:*okbc-standard-class-names*)
     (member thing ok-back:*okbc-standard-slot-names*)
     (member thing ok-back:*okbc-standard-facet-names*)
     (object-constant-p thing kb language)))

(defmethod logical-constant-p (thing kb language)
 (or (or (and (symbolp thing)
	      (find thing '(:true :false) :test #'string-equal)))
     (object-constant-p thing kb language)))

(defmethods walk-subexpression ((kb t)
				(production (eql :objconst))
				(language abstract-kif-language)
				known-context-type bound-vars expression
				function-to-apply)
  "A constant denoting a truth value."
  (when (not (object-constant-p expression kb language))
    (parser-warn 'illegal-object-constant kb
		 "~S should be an object constant" expression))
  (funcall function-to-apply kb production known-context-type bound-vars
	   expression))

(defmethods walk-subexpression ((kb t)
				(production (eql :kif-operator))
				(language abstract-kif-language)
				known-context-type bound-vars
				expression function-to-apply)
  (funcall function-to-apply kb production known-context-type bound-vars
	   (walk-subexpression kb :lisp-object language known-context-type
			       bound-vars expression function-to-apply)))

(defmethods walk-subexpression ((kb t)
				(production (eql :lisp-object)) (language t)
				known-context-type bound-vars
				(expression number) function-to-apply)
  "A lisp object; non-symbol atomic terms or the inside of a quotation term."
  (funcall function-to-apply kb production known-context-type bound-vars
	   (walk-subexpression kb :number language known-context-type
			       bound-vars expression function-to-apply)))

(defmethods walk-subexpression ((kb t)
				(production (eql :lisp-object)) (language t)
				known-context-type bound-vars (expression cons)
				function-to-apply)
  "A lisp object; non-symbol atomic terms or the inside of a quotation term."
  (funcall function-to-apply kb production known-context-type bound-vars
	   (walk-subexpression kb :cons-as-lisp-object language
			       known-context-type bound-vars expression
			       function-to-apply)))

(defmethods walk-subexpression ((kb t)
				(production (eql :lisp-object)) (language t)
				known-context-type bound-vars
				(expression string) function-to-apply)
  "A lisp object; non-symbol atomic terms or the inside of a quotation term."
  (funcall function-to-apply kb production known-context-type bound-vars
	   (walk-subexpression kb :string language known-context-type
			       bound-vars expression function-to-apply)))

(defmethods walk-subexpression ((kb t)
				(production (eql :lisp-object)) (language t)
				known-context-type bound-vars
				(expression vector) function-to-apply)
  "A lisp object; non-symbol atomic terms or the inside of a quotation term."
  (funcall function-to-apply kb production known-context-type bound-vars
	   (walk-subexpression kb :vector language known-context-type
			       bound-vars expression function-to-apply)))

(defmethods walk-subexpression ((kb t)
				(production (eql :lisp-object)) (language t)
				known-context-type bound-vars
				(expression symbol) function-to-apply)
  "A lisp object; non-symbol atomic terms or the inside of a quotation term."
  (funcall function-to-apply kb production known-context-type bound-vars
	   (walk-subexpression kb :symbol language known-context-type
			       bound-vars expression function-to-apply)))

(defmethods walk-subexpression ((kb t)
				(production (eql :lisp-object)) (language t)
				known-context-type bound-vars (expression t)
				function-to-apply)
  "A lisp object; non-symbol atomic terms or the inside of a quotation term."
  (funcall function-to-apply kb production known-context-type bound-vars
	   (walk-subexpression kb :primitive-lisp-object language
			       known-context-type bound-vars expression
			       function-to-apply)))

(defmethods walk-subexpression ((kb t)
				(production (eql :number)) (language t)
				known-context-type bound-vars expression
				function-to-apply)
  (if (numberp expression)
      (funcall function-to-apply kb production known-context-type bound-vars
	       (walk-subexpression kb :primitive-lisp-object language
				   known-context-type bound-vars expression
				   function-to-apply))
      (progn (parser-warn 'illegal-number kb
			  "~S should be a number." expression)
	     expression)))

(defvar *vector-element-syntactic-type* :term)

(defmethods walk-subexpression ((kb t)
				(production (eql :vector)) (language t)
				known-context-type bound-vars expression
				function-to-apply)
  (if (vectorp expression)
      (funcall function-to-apply kb production known-context-type bound-vars
	       (let ((primitive-walked
		      (walk-subexpression kb :primitive-lisp-object language
					  known-context-type bound-vars
					  expression function-to-apply)))
		 (let ((new (make-array (length primitive-walked)
					:element-type
					(array-element-type
					 primitive-walked)))
		       (same-p t))
		   (loop for i from 0 below (length primitive-walked)
			 for value = (aref primitive-walked i)
			 ;; The values in vectors are terms.
			 for new-val = (walk-subexpression
					kb
					*vector-element-syntactic-type*
					language known-context-type bound-vars
					value function-to-apply)
			 do (setf (svref new i) new-val)
			 when (not (equal new-val value)) do (setq same-p nil))
		   (if same-p primitive-walked new))))
      (progn (parser-warn 'illegal-number kb
			  "~S should be a vector." expression)
	     expression)))

(defmethods walk-subexpression ((kb t)
				(production (eql :cons-as-lisp-object))
				(language t) known-context-type bound-vars
				expression function-to-apply)
  (if (consp expression)
      (funcall function-to-apply kb production known-context-type bound-vars
	       (walk-subexpression kb :primitive-lisp-object language
				   known-context-type bound-vars expression
				   function-to-apply))
      (progn (parser-warn 'illegal-cons-as-lisp-object kb
			  "~S should be a cons (list)." expression)
	     expression)))

(defmethods walk-subexpression ((kb t)
				(production (eql :generalized-string))
				(language t) known-context-type bound-vars
				(expression string) function-to-apply)
  (funcall function-to-apply kb production known-context-type bound-vars
	   (walk-subexpression kb :string language known-context-type
			       bound-vars expression function-to-apply)))

(defmethods walk-subexpression ((kb t)
				(production (eql :generalized-string))
				(language t) known-context-type bound-vars
				(expression symbol) function-to-apply)
  (funcall function-to-apply kb production known-context-type bound-vars
	   (walk-subexpression kb :symbol language known-context-type
			       bound-vars expression function-to-apply)))

(defmethods walk-subexpression ((kb t)
				(production (eql :generalized-string))
				(language t) (known-context-type t)
				(bound-vars t) (expression t)
				(function-to-apply t))
  (parser-warn 'illegal-generalized-string kb
	       "~S should be a generalized string." expression)
  expression)

(defmethods walk-subexpression ((kb t)
				(production (eql :string)) (language t)
				known-context-type bound-vars expression
				function-to-apply)
  (if (stringp expression)
      (funcall function-to-apply kb production known-context-type bound-vars
	       (walk-subexpression kb :primitive-lisp-object language
				   known-context-type bound-vars expression
				   function-to-apply))
      (progn (parser-warn 'illegal-string kb "~S should be a string."
			  expression)
	     expression)))

(defmethods walk-subexpression ((kb t)
				(production (eql :symbol)) (language t)
				known-context-type bound-vars expression
				function-to-apply)
  (if (symbolp expression)
      (funcall function-to-apply kb production known-context-type bound-vars
	       (walk-subexpression kb :primitive-lisp-object language
				   known-context-type bound-vars expression
				   function-to-apply))
      (progn (parser-warn 'illegal-string kb "~S should be a symbol."
			  expression)
	     expression)))

(defmethods walk-subexpression ((kb t)
				(production (eql :in-package)) (language t)
				known-context-type bound-vars expression
				function-to-apply)
  (funcall function-to-apply kb production known-context-type bound-vars
	   (if (consp expression)
	       (if (= (length expression) 2)
		   (walk-subexpression 
		    kb :lisp-object language known-context-type bound-vars
		    expression function-to-apply)
		   (progn (parser-warn
			   'illegal-okbc-expression kb
			   "The form ~S ~% is a malformed in-package form."
			   expression)
			  expression))
	       (progn
		 (parser-warn
		  'illegal-okbc-expression kb
		  "The form ~S~% is not a legal in-package form for OKBC."
		  expression)
		 expression))))

(defmethods walk-subexpression ((kb t)
				(production (eql :let)) (language t)
				known-context-type bound-vars expression
				function-to-apply)
  (funcall function-to-apply kb production known-context-type bound-vars
	   (parser-list*
	    expression
	    (walk-subexpression 
	     kb :lisp-object language known-context-type bound-vars
	     (first expression) function-to-apply)
	    (walk-subexpression 
	     kb :lisp-object language known-context-type bound-vars
	     (second expression) function-to-apply)
	    (loop-for-x-in-l-collect
	     (form (rest (rest expression)))
	     (walk-subexpression 
	      kb :form language known-context-type bound-vars form
	      function-to-apply)))))

(defmethods walk-subexpression ((kb t)
				(production (eql :form))
				(language abstract-okbc-language)
				known-context-type bound-vars expression
				function-to-apply)
  (if (and (consp expression)
	   (symbolp (first expression))
	   (string-equal (first expression) :define-okbc-frame))
  
      (funcall
       function-to-apply kb production known-context-type bound-vars
       (walk-subexpression 
	kb :define-okbc-frame language known-context-type bound-vars
	expression function-to-apply))
      (call-next-method)))

(defmethods walk-subexpression ((kb t)
				(production (eql :define-okbc-frame))
				(language abstract-okbc-language)
				known-context-type
				bound-vars expression function-to-apply)
  (if (and (consp expression)
	   (symbolp (first expression))
	   (string-equal (first expression) :define-okbc-frame))
      (funcall
       function-to-apply kb production known-context-type bound-vars
       (destructuring-bind (name &body body) (rest expression)
	 (destructuring-bind (&key type frame-type direct-types
				   direct-superclasses template-slot-specs
				   template-facet-specs template-slots
				   template-facets &allow-other-keys)
	     body
	   (when (boundp '*expression-being-walked*)
	     (setq *expression-being-walked* name))
	   (parser-list*
	    expression
	    (walk-subexpression 
	     kb :lisp-object language known-context-type bound-vars
	     (with-kif-replacement (first expression) :define-okbc-frame)
	     function-to-apply)
	    (walk-subexpression
	     kb
	     (cond ((or (member (or frame-type type) '(:slot :class :facet))
			direct-superclasses template-slot-specs
			template-facet-specs template-slots
			template-facets
			(member :class direct-types))
		    :relconst)
		   (t :objconst))
	     language (or frame-type type) bound-vars name function-to-apply)
	    (walk-key/value-plist kb language known-context-type bound-vars
				  body function-to-apply)))))
      (progn (parser-warn
	      'illegal-define-okbc-frame-expression kb
	      "The form ~S~% is not a legal define-okbc-frame form."
	      expression)
	     expression)))

(defokbcgeneric walk-key/value-plist
    (kb language known-context-type bound-vars key-arg-pairs function-to-apply)
  (:documentation "Internal protocol in the OKBC code walker that walks
   over a list of key/value pairs."))

(defmethods walk-key/value-plist
    (kb language known-context-type bound-vars key-arg-pairs function-to-apply)
  (loop-for-k/v-on-l-append
   (key value key-arg-pairs)
   (let ((key (walk-subexpression 
	       kb :lisp-object language known-context-type bound-vars key
	       function-to-apply)))
     ;; For backwards compatibility with the old format.
     (case key
       (:subclass-of :direct-superclasses)
       (:instance-of :direct-types)
       (otherwise key)))
   (walk-key/value-plist-pair
    kb key language known-context-type bound-vars value function-to-apply)))

(defmethods walk-maybe-defaulted-values
    ((kb t) (language abstract-okbc-language)
     (known-context-type t) (bound-vars t) (values t) (function-to-apply t))
  (loop-for-x-in-l-collect
   (val values)
   (if (and (consp val) (eq :default (first val)))
       (parser-list
	val
	(walk-subexpression 
	 kb :lisp-object language known-context-type bound-vars (first val)
	 function-to-apply)
	(walk-subexpression
	 kb :term language known-context-type bound-vars (second val)
	 function-to-apply))
       (walk-subexpression
	kb :term language known-context-type bound-vars val
	function-to-apply))))

(defmethods walk-subexpression ((kb t)
				(key (eql :okbc-slot-spec))
				(language abstract-okbc-language)
				(known-context-type t) (bound-vars t)
				(value t) (function-to-apply t))
  (funcall function-to-apply kb :okbc-slot-spec known-context-type
	   bound-vars
	   (cond ((consp value)
		  (destructuring-bind (slot . values) value
		    (parser-cons
		     value
		     (walk-subexpression 
		      kb :relconst language :slot bound-vars slot
		      function-to-apply)
		     (walk-maybe-defaulted-values
		      kb language known-context-type bound-vars values
		      function-to-apply))))
		 (t (parser-warn
		     'illegal-okbc-sentence kb
		     "The form ~S ~% is not a legal OKBC slot spec."
		     value)
		    value))))

(defokbcgeneric walk-key/value-plist-pair
    (kb key language known-context-type bound-vars value function-to-apply)
  (:documentation
   "An extension hook for the code walker that walks over the key/value pairs
    in a plist.  This is usually called to walk over the &key arguments to
    top-level forms such as <code>define-okbc-frame</code>."))

(defmethods walk-key/value-plist-pair
    ((kb t) (key (eql :slot-specs))
     (language abstract-okbc-language) (known-context-type t) (bound-vars t)
     (value t) (function-to-apply t))
  (cond ((consp value)
	 (funcall function-to-apply kb :slot-specs known-context-type
		  bound-vars
		  (loop-for-x-in-l-collect
		   (spec value)
		   (walk-subexpression
		    kb :okbc-slot-spec language known-context-type bound-vars
		    spec function-to-apply))))
	((null value) nil)
	((and (symbolp value) (string-equal :nil value)) nil)
	(t (parser-warn
	    'illegal-okbc-slot-specs kb
	    "The form ~S ~% is not a legal list of OKBC slot specs."
	    value)
	   value)))

(defmethods walk-key/value-plist-pair
    ((kb t) (key t) (language t)
     (known-context-type t) (bound-vars t) (value t) (function-to-apply t))
  (parser-warn
   'illegal-okbc-key/value-pair kb "Unknown key/value pair ~S = ~S."
   key value))

(defmethods walk-key/value-plist-pair
    ((kb t) (key (eql :sentences))
     (language abstract-okbc-language) (known-context-type t) (bound-vars t)
     (value t) (function-to-apply t))
  (funcall function-to-apply kb :sentences known-context-type bound-vars
	   (walk-list-of-sentences kb language known-context-type bound-vars
				   value function-to-apply)))

(defun walk-list-of-sentences (kb language known-context-type bound-vars value
				  function-to-apply)
  "Invokes the code walker to walk over a list of KIF sentences.  This function
   is useful then writing walker methods for languages that layer on top of
   KIF."
  (if (consp value)
      (if (consp (first value))
	  (loop-for-x-in-l-collect
	   (x value)
	   (walk-subexpression kb :sentence language known-context-type
			       bound-vars x function-to-apply))
	  (walk-subexpression kb :sentence language known-context-type
			      bound-vars value function-to-apply))
      (if value
	  (progn (parser-warn
		  'illegal-KIF-sentence kb
		  "The form ~S ~% is not a legal list of sentences."
		  value)
		 value)
	  (walk-subexpression kb :lisp-object language known-context-type
			      bound-vars value function-to-apply))))

(defmethods walk-key/value-plist-pair
 ((kb t) (key (eql :documentation))
  (language abstract-okbc-language) known-context-type (bound-vars t) (value t)
  (function-to-apply t))
  (when (not (or (not value) (stringp value)))
    (parser-warn 'illegal-doc-string kb "~S should be a doc string." value))
  (walk-subexpression kb :lis-object language known-context-type
		      bound-vars value function-to-apply))

(defmethods walk-key/value-plist-pair
    ((kb t) (key (eql :own-slots))
     (language abstract-okbc-language) (known-context-type t) (bound-vars t)
     (value t) (function-to-apply t))
  (funcall function-to-apply kb :own-slots known-context-type bound-vars
	   (walk-key/value-plist-pair kb :slot-specs language
				      known-context-type bound-vars value
				      function-to-apply)))

(defmethods walk-key/value-plist-pair
    ((kb t) (key (eql :template-slots))
     (language abstract-okbc-language) known-context-type (bound-vars t)
     (value t) (function-to-apply t))
  (funcall function-to-apply kb :template-slots known-context-type
	   bound-vars
	   (walk-key/value-plist-pair kb :slot-specs language
				      known-context-type bound-vars value
				      function-to-apply)))

(defmethods walk-subexpression
    ((kb t) (key (eql :fspec)) (language abstract-okbc-language)
     (known-context-type t) (bound-vars t) (value t) (function-to-apply t))
  (cond ((consp value)
	 (funcall function-to-apply kb :fspec known-context-type bound-vars
		  (destructuring-bind (facet . values) value
		    (parser-cons
		     value
		     (walk-subexpression 
		      kb :relconst language :facet bound-vars facet
		      function-to-apply)
		     (walk-maybe-defaulted-values
		      kb language known-context-type bound-vars values
		      function-to-apply)))))
	(t (parser-warn
	    'illegal-okbc-sentence kb
	    "The form ~S ~% is not a legal OKBC facet spec."
	    value)
	   value)))

(defmethods walk-subexpression
    ((kb t) (key (eql :okbc-facet-spec))
     (language abstract-okbc-language) (known-context-type t) (bound-vars t)
     (value t) (function-to-apply t))
  (cond ((consp value)
	 (funcall function-to-apply kb :okbc-slot-spec known-context-type
		  bound-vars
		  (destructuring-bind (slot . fspecs) value
		    (parser-cons
		     value
		     (walk-subexpression 
		      kb :relconst language :slot bound-vars slot
		      function-to-apply)
		     (loop-for-x-in-l-collect
		      (fspec fspecs)
		      (walk-subexpression 
		       kb :fspec language known-context-type bound-vars fspec
		       function-to-apply))))))
	(t (parser-warn
	    'illegal-okbc-sentence kb
	    "The form ~S ~% is not a legal OKBC facet spec."
	    value)
	   value)))

(defmethods walk-key/value-plist-pair
    ((kb t) (key (eql :facet-specs))
     (language abstract-okbc-language) (known-context-type t) (bound-vars t)
     (value t) (function-to-apply t))
  (cond ((consp value)
	 (funcall function-to-apply kb :facet-specs known-context-type
		  bound-vars
		  (loop-for-x-in-l-collect
		   (spec value)
		   (walk-subexpression
		    kb :okbc-facet-spec language known-context-type bound-vars
		    spec function-to-apply))))
	((null value) nil)
	((eq :nil value) nil)
	(t (parser-warn
	    'illegal-okbc-sentence kb
	    "The form ~S ~% is not a legal list of OKBC facet specs."
	    value)
	   value)))

(defmethods walk-key/value-plist-pair
    ((kb t) (key (eql :own-facets))
     (language abstract-okbc-language) (known-context-type t) (bound-vars t)
     (value t) (function-to-apply t))
  (funcall function-to-apply kb key known-context-type bound-vars
	   (walk-key/value-plist-pair kb :facet-specs language
				      known-context-type bound-vars value
				      function-to-apply)))

(defmethods walk-key/value-plist-pair
    ((kb t) (key (eql :template-facets))
     (language abstract-okbc-language) (known-context-type t) (bound-vars t)
     (value t) (function-to-apply t))
  (funcall function-to-apply kb key known-context-type bound-vars
	   (walk-key/value-plist-pair kb :facet-specs language
				      known-context-type bound-vars value
				      function-to-apply)))

(defmethods walk-key/value-plist-pair;; the OKBC context type arg.
    ((kb t) (key (eql :frame-type))
     (language abstract-okbc-language) (known-context-type t) (bound-vars t)
     (value t) (function-to-apply t))
  (if (member value '(nil :class :slot :facet :individual))
      (funcall function-to-apply kb :frame-type known-context-type bound-vars
	       (walk-subexpression kb :lisp-object language known-context-type
				   bound-vars value function-to-apply))
      (progn (parser-warn
	      'illegal-OKBC-context-type kb
	      "The form ~S ~% is not a legal OKBC context type."
	      value)
	     value)))

(defmethods walk-key/value-plist-pair
    ((kb t)
     (key ((eql :pretty-name) (eql :handle) (eql :primitive-p)))
     (language abstract-okbc-language) (known-context-type t) (bound-vars t)
     (value t) (function-to-apply t))
  (funcall function-to-apply kb key known-context-type bound-vars
	   (walk-subexpression kb :lisp-object language known-context-type
			       bound-vars value function-to-apply)))

(defmethods walk-key/value-plist-pair
    ((kb t) (key ((eql :direct-superclasses)
				  ;; For compatibility
				  (eql :subclass-of)))
     (language abstract-okbc-language) (known-context-type t) (bound-vars t)
     (value t) (function-to-apply t))
  (funcall function-to-apply kb :direct-superclasses known-context-type
	   bound-vars
	   (walk-key/value-plist-pair kb :class-list language
				      known-context-type bound-vars value
				      function-to-apply)))

(defmethods walk-key/value-plist-pair
    ((kb t) (key ((eql :direct-types)
				  (eql :instance-of)))
     (language abstract-okbc-language) (known-context-type t) (bound-vars t)
     (value t) (function-to-apply t))
  (funcall function-to-apply kb :direct-types known-context-type bound-vars
	   (walk-key/value-plist-pair kb :class-list language
				      known-context-type bound-vars
				      value function-to-apply)))

(defmethods walk-key/value-plist-pair
    ((kb t) (key (eql :class-list))
     (language abstract-okbc-language) (known-context-type t) (bound-vars t)
     (value t) (function-to-apply t))
  (if (or (eq value :nil) (not value))
      nil
      (if (consp value)
	  (loop-for-x-in-l-collect
	   (class value)
	   (walk-subexpression 
	    kb :relconst language :class bound-vars class
	    function-to-apply))
	  (parser-warn 'illegal-class-list kb
		       "~S should be a list of classes." value))))

(defun quantified-term-operator-p (thing)
  "Non NIL iff THING is an operator that heads a KIF quantified term."
  (and (symbolp thing)
       (let ((match (find thing '(:the :setofall :lambda :kappa)
			  :test #'string-equal)))
	 (and match (with-kif-replacement thing match)))))


(defun quotation-operator-p (thing)
  "Non NIL iff THING is an operator that heads a KIF quotation term."
  (and (symbolp thing) (string-equal thing :quote)
       (with-kif-replacement thing :quote)))


(defun list-operator-p (thing)
  "Non NIL iff THING is an operator that heads a KIF list term."
  (and (symbolp thing) (string-equal thing :listof)
       (with-kif-replacement thing :listof)))


(defun set-operator-p (thing)
  "Non NIL iff THING is an operator that heads a KIF set term."
  (and (symbolp thing) (string-equal thing :setof)
       (with-kif-replacement thing :setof)))

(defmethod term-operator-p (op (language kif-3.0-language))
; (or (quantified-term-operator-p thing)
;      (quotation-operator-p thing)
;      (list-operator-p thing)
;      (set-operator-p thing))
 (and (symbolp op)
       (let ((match (find op '(:listof :setof :quote :if :cond :the :setofall
			       :kappa :lambda)
			  :test #'string-equal)))
	 (if match (with-kif-replacement op match) nil))))

(defmethod term-operator-p (op (language ansi-kif-language))
  (and (symbolp op)
       (let ((match (find op '(:value :listof :quote :if)
			  :test #'string-equal)))
	 (if match (with-kif-replacement op match) nil))))

(defvar *kif-logical-sentence-operators*
  '(:not :and :or :=> :<= :<=>))

(defmethod logical-sentence-operator-p (thing (kb t) (language t))
  "Non NIL iff THING is an operator that heads a KIF logical sentence."
  (and (symbolp thing)
       (let ((match (find thing *kif-logical-sentence-operators*
			  :test #'string-equal)))
	 (and match (with-kif-replacement thing match)))))

(defun negation-operator-p (thing)
  (and (symbolp thing)
       (let ((match (find thing '(:not) :test #'string-equal)))
	 (and match (with-kif-replacement thing match)))))

(defun conjunction-operator-p (thing)
  (and (symbolp thing)
       (let ((match (find thing '(:and) :test #'string-equal)))
	 (and match (with-kif-replacement thing match)))))

(defun holds-operator-p (thing)
  (and (symbolp thing)
       (let ((match (find thing '(:holds) :test #'string-equal)))
	 (and match (with-kif-replacement thing match)))))

(defun value-operator-p (thing)
  (and (symbolp thing)
       (let ((match (find thing '(:value) :test #'string-equal)))
	 (and match (with-kif-replacement thing match)))))

(defun sentence-quantification-operator-p (thing)
  "Non NIL iff THING is an operator that heads a KIF quantified sentence."
  (and (symbolp thing)
       (let ((match (find thing '(:exists :forall) :test #'string-equal)))
	 (and match (with-kif-replacement thing match)))))

(defvar *equality-operators* '(:=))

(defun equality-operator-p (thing)
  "Non NIL iff THING is an operator that heads a KIF equation."
  (and (symbolp thing)
       (let ((match (find thing *equality-operators* :test #'string-equal)))
	 (and match (with-kif-replacement thing match)))))

(defun inequality-operator-p (thing)
  "Non NIL iff THING is an operator that heads a KIF inequality."
  (and (symbolp thing) (string-equal thing :/=)
       (with-kif-replacement thing :/=)))

(defmethod sentence-operator-p (thing (kb t) (language abstract-kif-language))
  (or (logical-sentence-operator-p thing kb language)
      (sentence-quantification-operator-p thing)
      (equality-operator-p thing)
      (inequality-operator-p thing)))

(defmethod sentence-operator-p (thing (kb t) (language ansi-kif-language))
  (or (holds-operator-p thing)
      (call-next-method)))

(defun rule-operator-p (thing)
  "Non NIL iff THING is an operator that heads a KIF rule."
  (and (symbolp thing)
       (let ((match (find thing '(:<<= :=>>) :test #'string-equal)))
	 (and match (with-kif-replacement thing match)))))

(defun logical-term-operator-p (thing)
  "Non NIL iff THING is an operator that heads a KIF logical term."
  (and (symbolp thing)
       (let ((match (find thing '(:if :cond) :test #'string-equal)))
	 (and match (with-kif-replacement thing match)))))

(defmethod non-defining-definition-operator-p (thing (language t))
 (and (symbolp thing)
      (let ((match (find thing '(:= :=>) :test #'string-equal)))
	(and match (with-kif-replacement thing match)))))

(defmethod non-defining-definition-operator-p
 (thing (language kif-3.0-language))
 (or (call-next-method)
     (and (symbolp thing)
	  (let ((match (find thing '(:&) :test #'string-equal)))
	    (and match (with-kif-replacement thing match))))))

(defmethod non-defining-definition-operator-p
 (thing (language ansi-kif-language))
 (or (call-next-method)
     (and (symbolp thing)
	  (let ((match (find thing '(:<= :->) :test #'string-equal)))
	    (and match (with-kif-replacement thing match))))))

(defmethod definition-operator-p (thing (language t))
  "Non NIL iff THING is an operator that heads a KIF definition."
  (and (symbolp thing)
       (let ((match (find thing '(:defobject :deffunction :defrelation := :=>)
			  :test #'string-equal)))
	 (and match (with-kif-replacement thing match)))))

(defmethod definition-operator-p (thing (language kif-3.0-language))
  "Non NIL iff THING is an operator that heads a KIF definition."
 (or (call-next-method)
     (and (symbolp thing)
	   (let ((match (find thing '(:&) :test #'string-equal)))
	     (and match (with-kif-replacement thing match))))))

(defmethod definition-operator-p (thing (language ansi-kif-language))
  "Non NIL iff THING is an operator that heads a KIF definition."
  (or (call-next-method)
      (and (symbolp thing)
	   (let ((match (find thing '(:<= :->) :test #'string-equal)))
	     (and match (with-kif-replacement thing match))))))

(defun kif-operator-p (thing kb language)
  "Any sort of KIF operator token."
  (or (term-operator-p thing language)
      (sentence-operator-p thing kb language)
      (rule-operator-p thing)
      (definition-operator-p thing language)))

;=============================================================================

;;; Now define a CML parser

(defokbcclass ok-utils:cml-language (ok-utils:okbc-language)
  ()
  (:documentation "The OKBC representation of the CML-language for the OKBC
 parser.  All OKBC language productions are supported as well as the
 CML language forms.  Note that the KIF-3.0 language form DEFRELATION is
 shadowed by the CML form of the same name."))

(defmethod number-or-vector-p ((x number)) t)
(defmethod number-or-vector-p ((x vector)) t)
(defmethod number-or-vector-p ((x t)) nil)

(defvar *slot-type-being-walked*)
(defvar *allowed-variables-in-literals* :all)
(defparameter *cml-source-level-substitutions*
  '((:= . :==)
    (:<= . :=<)))

(defparameter *cml-source-substituted-symbols*
  '(:= :<=))

(defparameter *cml-top-level-expression-types*
  '(:domain-theory
    :defrelation
    :defQuantityFunction
    :defModelFragment
    :defEntity
    :defScenario
    :defdimension
    :defunit
    :defConstantQuantity))

(defmethods walk-subexpression ((kb t) (type (eql :cml))
				(language cml-language) known-context-type
				bound-vars expression function-to-apply)
  (funcall function-to-apply kb type known-context-type bound-vars
	   (typecase expression
	     (cons (let ((key (and (symbolp (first expression))
				   (find (first expression)
					 *cml-top-level-expression-types*
					 :test #'string-equal))))
		     (if key
			 (walk-subexpression 
			  kb key language known-context-type bound-vars
			  expression function-to-apply) 
			 (progn
			   (parser-warn
			    'illegal-ontolingua-expression kb
			    "The form ~S ~% is a malformed top-level ~
                             CML form."
			    expression)
			   expression))))
	     (otherwise
	      (parser-warn
	       'illegal-cml-expression kb
	       "The form ~S~% is not a legal top-level form for CML."
	       expression)
	      expression))))

(defmethods walk-subexpression ((kb t) (type (eql :form))
				(language cml-language) known-context-type
				bound-vars expression function-to-apply)
  (let ((key (and (symbolp (first expression))
		  (find (first expression)
			*cml-top-level-expression-types*
			:test #'string-equal))))
    (if key
	(progn
	  (when (boundp '*expression-being-walked*)
	    (setq *expression-being-walked* (second expression)))
	  (funcall function-to-apply kb type known-context-type bound-vars
		   (typecase expression
		     (cons (walk-subexpression 
			    kb key language known-context-type bound-vars
			    expression function-to-apply))
		     (otherwise
		      (parser-warn
		       'illegal-cml-expression kb
		       "The form ~S~% is not a legal top-level form for CML."
		       expression)
		      (walk-subexpression 
		       kb :lisp-object language known-context-type bound-vars
		       expression function-to-apply)))))
	(call-next-method))))

(defmethods walk-subexpression ((kb t)
				(type (eql :defrelation))
				(language cml-language)
				known-context-type bound-vars expression
				function-to-apply)
  (funcall function-to-apply kb type known-context-type bound-vars
	   (destructuring-bind (name free-variables &key => <=> documentation
				     function time-dependent
				     &allow-other-keys)
	       (rest expression)
	     (declare (ignore => <=> documentation function time-dependent))
	     (when (boundp '*expression-being-walked*)
	       (setq *expression-being-walked* name))
	     (let ((body (rest (rest (rest expression)))))
	       `(,(walk-subexpression 
		   kb :lisp-object language known-context-type bound-vars
		   (first expression) function-to-apply)
		 ,(walk-subexpression 
		   kb :relconst language known-context-type bound-vars
		   name function-to-apply)
		 ,(walk-subexpression kb :variable-list language
				      known-context-type bound-vars
				      free-variables function-to-apply)
		 ,@(walk-key/value-plist
		    kb language known-context-type bound-vars body
		    function-to-apply))))))

(defmethods walk-subexpression ((kb t)
				(type (eql :defquantityfunction))
				(language cml-language) known-context-type
				bound-vars expression function-to-apply)
  (funcall function-to-apply kb type known-context-type bound-vars
	   (destructuring-bind (name free-variables &key => 
				     documentation dimension non-numeric
				     piecewise-continuous step-quantity
				     count-quantity &allow-other-keys)
	       (rest expression)
	     (declare (ignore => documentation dimension non-numeric
			      piecewise-continuous step-quantity
			      count-quantity))
	     (when (boundp '*expression-being-walked*)
	       (setq *expression-being-walked* name))
	     (let ((body (rest (rest (rest expression)))))
	       `(,(walk-subexpression 
		   kb :lisp-object language known-context-type bound-vars
		   (first expression)
		   function-to-apply)
		 ,(walk-subexpression 
		   kb :funconst language known-context-type bound-vars
		   name function-to-apply)
		 ,(walk-subexpression kb :variable-list language
				      known-context-type bound-vars
				      free-variables function-to-apply)
		 ,@(walk-key/value-plist
		    kb language known-context-type bound-vars body
		    function-to-apply))))))

(defmethods walk-subexpression ((kb t)
				(type (eql :defmodelfragment))
				(language cml-language) known-context-type
				bound-vars expression function-to-apply)
  (when (boundp '*expression-being-walked*)
    (setq *expression-being-walked* (second expression)))
  (parse-model-fragment-type-cml-form
   kb type language known-context-type bound-vars expression
   function-to-apply))

(defun parse-model-fragment-type-cml-form
    (kb type language known-context-type bound-vars expression
	function-to-apply)
  (funcall function-to-apply kb type known-context-type bound-vars
	   (destructuring-bind (name &key subclass-of participants conditions
				     quantities attributes consequences
				     substitutions documentation
				     &allow-other-keys)
	       (rest expression)
	     (declare (ignore subclass-of participants conditions
			      quantities attributes consequences
			      substitutions documentation))
	     (let ((body (rest (rest expression))))
	       `(,(walk-subexpression 
		   kb :lisp-object language known-context-type bound-vars
		   (first expression)
		   function-to-apply)
		 ,(walk-subexpression 
		   kb :objconst language known-context-type bound-vars
		   name function-to-apply)
		 ,@(walk-key/value-plist
		    kb language known-context-type bound-vars body
		    function-to-apply))))))

(defmethods walk-subexpression ((kb t) (type (eql :defentity))
				(language cml-language) known-context-type
				bound-vars expression function-to-apply)
  (funcall function-to-apply kb type known-context-type bound-vars
	   (destructuring-bind (name &key subclass-of 
				     quantities attributes
				     consequences substitutions documentation
				     &allow-other-keys)
	       (rest expression)
	     (declare (ignore subclass-of 
			      quantities attributes
			      consequences substitutions documentation))
	     (when (boundp '*expression-being-walked*)
	       (setq *expression-being-walked* name))
	     (let ((body (rest (rest expression))))
	       `(,(walk-subexpression 
		   kb :lisp-object language known-context-type bound-vars
		   (first expression) function-to-apply)
		 ,(walk-subexpression 
		   kb :objconst language known-context-type bound-vars
		   name function-to-apply)
		 ,@(walk-key/value-plist
		    kb language known-context-type bound-vars body
		    function-to-apply))))))

(defmethods walk-subexpression ((kb t)
				(type (eql :consequence))
				(language cml-language)
				known-context-type bound-vars expression
				function-to-apply)
  (let ((*allowed-variables-in-literals* :all))
    (funcall function-to-apply kb type known-context-type bound-vars
	     (walk-subexpression
	      kb :literal language known-context-type bound-vars expression
	      function-to-apply))))

(defmethods walk-subexpression ((kb t)
				(type (eql :condition)) (language cml-language)
				known-context-type bound-vars expression
				function-to-apply)
  (let ((*allowed-variables-in-literals* :all))
    (funcall function-to-apply kb type known-context-type bound-vars
	     (walk-subexpression
	      kb :literal language known-context-type bound-vars expression
	      function-to-apply))))

(defmethods walk-subexpression ((kb t)
				(type (eql :defscenario))
				(language cml-language)
				known-context-type bound-vars expression
				function-to-apply)
  (funcall function-to-apply kb type known-context-type bound-vars
	   (destructuring-bind (name &key individuals initially throughout
				     boundary documentation &allow-other-keys)
	       (rest expression)
	     (declare (ignore individuals initially throughout boundary
			      documentation))
	     (when (boundp '*expression-being-walked*)
	       (setq *expression-being-walked* name))
	     (let ((body (rest (rest expression))))
	       `(,(walk-subexpression 
		   kb :lisp-object language known-context-type bound-vars
		   (first expression) function-to-apply)
		 ,(walk-subexpression 
		   kb :objconst language known-context-type bound-vars
		   name function-to-apply)
		 ,@(walk-key/value-plist
		    kb language known-context-type bound-vars body
		    function-to-apply))))))

(defmethods walk-subexpression
    ((kb t) (key (eql :individual-spec))
     (language cml-language) known-context-type (bound-vars t) (value t)
     (function-to-apply t))
  (cond ((and (consp value) (oddp (length value))
	      (getf (rest value) :frame-type));; type is mandatory
	 (funcall function-to-apply kb key known-context-type bound-vars
		  (cons (walk-subexpression kb :objconst language
					    known-context-type bound-vars
					    (first value) function-to-apply)
			(loop for (key val) on (rest value) by #'cddr
			      append
			      (list (walk-subexpression
				     kb :lisp-object language
				     known-context-type bound-vars
				     key function-to-apply)
				    (if (member key '(:frame-type))
					(walk-subexpression
					 kb :relconst language
					 known-context-type bound-vars
					 val function-to-apply)
					(walk-subexpression
					 kb :lisp-object language
					 known-context-type bound-vars val
					 function-to-apply)))))))
	(t (parser-warn 'illegal-individual-spec kb
			"~S should be a CML individual spec." value)
	   value)))

(defmethod cml-constant-p (x kb language)
  (or (numberp x)
      (vectorp x) ;; extension
      (object-constant-p x kb language)))

(defmethods walk-subexpression
    ((kb t) (key (eql :quantity-expression))
     (language cml-language) known-context-type (bound-vars t) (value t)
     (function-to-apply t))
  (cond ((cml-constant-p value kb language)
	 (funcall function-to-apply kb key known-context-type bound-vars
		  (if (number-or-vector-p value)
		      (walk-subexpression kb :lisp-object language
					  known-context-type bound-vars value
					  function-to-apply)
		      (walk-subexpression kb :objconst language
					  known-context-type bound-vars
					  value function-to-apply))))
	((consp value)
	 (funcall function-to-apply kb key known-context-type bound-vars
		  (cons (walk-subexpression kb :funconst language
					    known-context-type bound-vars
					    (first value) function-to-apply)
			(loop for arg in (rest value)
			      collect (walk-subexpression
				       kb :quantity-expression language
				       known-context-type bound-vars arg
				       function-to-apply)))))
	(t (parser-warn 'illegal-quantity-expression kb
			"~S should be a CML quantity expression." value)
	   value)))

(defmethods walk-subexpression
    ((kb t) (key (eql :literal)) (language cml-language)
     known-context-type (bound-vars t) (value t) (function-to-apply t))
  (cond ((consp value)
	 (funcall function-to-apply kb key known-context-type bound-vars
		  (if (negation-operator-p (first value))
		      (walk-subexpression kb :negative-literal language
					  known-context-type bound-vars
					  value
					  function-to-apply)
		      (walk-subexpression kb :positive-literal language
					  known-context-type bound-vars value
					  function-to-apply))))
	((symbolp value)
	 (funcall function-to-apply kb key known-context-type bound-vars
		  (walk-subexpression kb :positive-literal language
				      known-context-type bound-vars value
				      function-to-apply)))
	(t (parser-warn 'illegal-literal kb
			"~S should be a CML literal." value)
	   value)))

(defmethods walk-subexpression
    ((kb t) (key (eql :negative-literal))
     (language cml-language) known-context-type (bound-vars t) (value t)
     (function-to-apply t))
  (if (and (consp value) (= (length value) 2)
	   (negation-operator-p (first value)))
      (funcall function-to-apply kb key known-context-type bound-vars
	       (list (walk-subexpression kb :kif-operator language
					 known-context-type bound-vars
					 (negation-operator-p (first value))
					 function-to-apply)
		     (walk-subexpression kb :positive-literal language
					 known-context-type bound-vars
					 (second value) function-to-apply)))

      (progn (parser-warn 'illegal-negative-literal kb
			  "~S should be a CML negative literal." value)
	     value)))

(defmethods walk-subexpression
    ((kb t) (key (eql :positive-literal))
     (language cml-language) known-context-type (bound-vars t) (value t)
     (function-to-apply t))
  (cond ((consp value)
	 (funcall function-to-apply kb key known-context-type bound-vars
		  (cons (if (and *cml-source-level-substitutions*
				 (symbolp (first value))
				 (assoc (first value)
					*cml-source-level-substitutions*))
			    (walk-subexpression
			     kb :relconst language known-context-type
			     bound-vars
			     (rest (assoc (first value)
					  *cml-source-level-substitutions*))
			     function-to-apply)
			    (if (and (symbolp (first value))
				     (member (first value)
					     *cml-source-substituted-symbols*
					     :test #'string-equal))
				(walk-subexpression
				 kb :lisp-object language known-context-type
				 bound-vars (first value) function-to-apply)
				(walk-subexpression
				 kb :relconst language
				 known-context-type bound-vars (first value)
				 function-to-apply)))
			(loop for arg in (rest value)
			      collect (walk-subexpression
				       kb :cml-term language known-context-type
				       bound-vars arg function-to-apply)))))
	((symbolp value)
	 (walk-relation-type-qualifier
	  kb key language known-context-type bound-vars value
	  function-to-apply))
	(t (parser-warn 'illegal-positive-literal kb
			"~S should be a CML positive literal." value)
	   value)))

(defmethods walk-subexpression
    ((kb t) (key (eql :atomic-sentence))
     (language cml-language) known-context-type (bound-vars t) (value t)
     (function-to-apply t))
  (if (and (consp value) (conjunction-operator-p (first value)))
      (funcall function-to-apply kb key known-context-type bound-vars
	       (cons (walk-subexpression
		      kb :kif-operator language known-context-type
		      bound-vars (conjunction-operator-p (first value))
		      function-to-apply)
		     (loop for arg in (rest value)
			   collect (walk-subexpression
				    kb :atomic-sentence language
				    known-context-type bound-vars arg
				    function-to-apply))))
      (funcall function-to-apply kb key known-context-type bound-vars
	       (walk-subexpression
		kb :literal language known-context-type bound-vars value
		function-to-apply))))

(defmethods walk-subexpression
    ((kb t) (key (eql :cml-term)) language known-context-type
     (bound-vars t) (value t) (function-to-apply t))
  (cond ((number-or-vector-p value);; patch to grammar
	 (funcall function-to-apply kb key known-context-type bound-vars
		  (walk-subexpression kb :lisp-object language
				      known-context-type bound-vars value
				      function-to-apply)))
	((eq value :self)
	 (walk-subexpression kb :self language known-context-type bound-vars
			     value function-to-apply))
	((variable? value)
	 (if (or (eq :all *allowed-variables-in-literals*)
		 (member value *allowed-variables-in-literals*))
	     (funcall function-to-apply kb key known-context-type bound-vars
		      (walk-subexpression kb :variable language
					  known-context-type bound-vars value
					  function-to-apply))
	     (parser-warn 'illegal-variable-in-term kb
			  "The variable ~S is not legal here." value)))
	((object-constant-p value kb language)
	 (funcall function-to-apply kb key known-context-type bound-vars
		  (walk-subexpression kb :objconst language
				      known-context-type bound-vars value
				      function-to-apply)))
	((and (consp value) (quotation-operator-p (first value)))
	 (funcall function-to-apply kb key known-context-type bound-vars
		  (walk-subexpression kb :quoterm language
				      known-context-type bound-vars value
				      function-to-apply)))
	((consp value)
	 (funcall function-to-apply kb key known-context-type bound-vars
		  (cons (walk-subexpression kb :funconst language
					    known-context-type bound-vars
					    (first value) function-to-apply)
			(loop for arg in (rest value)
			      collect (walk-subexpression
				       kb :cml-term language known-context-type
				       bound-vars arg function-to-apply)))))
	(t (parser-warn 'illegal-term kb "~S should be a CML term." value)
	   value)))

(defmethods walk-subexpression ((kb t)
				(type (eql :defdimension))
				(language cml-language)
				known-context-type bound-vars expression
				function-to-apply)
  (funcall function-to-apply kb type known-context-type bound-vars
	   (destructuring-bind (name &key = documentation &allow-other-keys)
	       (rest expression)
	     (declare (ignore = documentation))
	     (when (boundp '*expression-being-walked*)
	       (setq *expression-being-walked* name))
	     (let ((body (rest (rest expression))))
	       `(,(walk-subexpression 
		   kb :lisp-object language known-context-type bound-vars
		   (first expression) function-to-apply)
		 ,(walk-subexpression 
		   kb :objconst language known-context-type bound-vars
		   name function-to-apply)
		 ,@(walk-key/value-plist
		    kb language known-context-type bound-vars body
		    function-to-apply))))))

(defmethods walk-subexpression ((kb t) (type (eql :defunit))
				(language cml-language) known-context-type
				bound-vars expression function-to-apply)
  (funcall function-to-apply kb type known-context-type bound-vars
	   (destructuring-bind (name &key = documentation pname dimension
				     &allow-other-keys)
	       (rest expression)
	     (declare (ignore = documentation pname dimension))
	     (when (boundp '*expression-being-walked*)
	       (setq *expression-being-walked* name))
	     (let ((body (rest (rest expression))))
	       `(,(walk-subexpression 
		   kb :lisp-object language known-context-type bound-vars
		   (first expression) function-to-apply)
		 ,(walk-subexpression 
		   kb :objconst language known-context-type bound-vars
		   name function-to-apply)
		 ,@(walk-key/value-plist
		    kb language known-context-type bound-vars body
		    function-to-apply))))))

(defmethods dimension-expression-operator-p (op (kb t))
  (or (and *symbols-ok-as-non-logical-constants-p*
	   (symbolp op)
	   (let ((match (find op '(:/ :* :expt) :test #'string-equal)))
	     (and match (with-kif-replacement op match))))
      (multiple-value-bind (frame found-p)
	(coerce-to-frame-internal op kb nil nil)
	(if found-p
	    (let ((name (get-frame-name-internal frame kb nil)))
	      (and name (symbolp name)
		   (let ((match (find name '(:/ :* :expt)
				      :test #'string-equal)))
		     (and match (with-kif-replacement op match)))))
	    nil))))
	  
(defmethods walk-subexpression
    ((kb t) (key (eql :dimension-expression))
     (language cml-language) known-context-type (bound-vars t) (value t)
     (function-to-apply t))
  (cond ((cml-constant-p value kb language)
	 (funcall function-to-apply kb key known-context-type bound-vars
		  (if (number-or-vector-p value)
		      (walk-subexpression kb :lisp-object language
					  known-context-type bound-vars value
					  function-to-apply)
		      (walk-subexpression kb :objconst language
					  known-context-type bound-vars value
					  function-to-apply))))
	((consp value)
	 (cond ((dimension-expression-operator-p (first value) kb)
		(funcall function-to-apply kb key known-context-type
			 bound-vars
			 (cons (walk-subexpression
				kb :funconst language
				known-context-type bound-vars
				(dimension-expression-operator-p
				 (first value) kb)
				function-to-apply)
			       (loop for arg in (rest value)
				     collect (walk-subexpression
					      kb :dimension-expression language
					      known-context-type bound-vars
					      arg function-to-apply)))))
	       (t (parser-warn
		   'illegal-dimension-expression kb
		   "~S is an illegal function in a CML dimension expression."
		   (first value))
		  value)))
	(t (parser-warn 'illegal-dimension-expression kb
			"~S should be a CML dimension expression." value)
	   value)))

(defmethods walk-subexpression ((kb t)
				(type (eql :defconstantquantity))
				(language cml-language)
				known-context-type bound-vars expression
				function-to-apply)
  (funcall function-to-apply kb type known-context-type bound-vars
	   (destructuring-bind (name &key = documentation pname dimension
				     &allow-other-keys)
	       (rest expression)
	     (declare (ignore = documentation pname dimension))
	     (when (boundp '*expression-being-walked*)
	       (setq *expression-being-walked* name))
	     (let ((body (rest (rest expression))))
	       `(,(walk-subexpression 
		   kb :lisp-object language known-context-type bound-vars
		   (first expression) function-to-apply)
		 ,(walk-subexpression 
		   kb :objconst language known-context-type bound-vars
		   name function-to-apply)
		 ,@(walk-key/value-plist
		    kb language known-context-type bound-vars body
		    function-to-apply))))))

(defmethods walk-key/value-plist-pair
 ((kb t) (key (eql :=>)) (language cml-language)
  known-context-type (bound-vars t) (value t) (function-to-apply t))
 (if (nil-p value)
     (funcall function-to-apply kb key known-context-type bound-vars
	      (walk-subexpression kb :lisp-object language known-context-type
				  bound-vars (nil-symbol value)
				  function-to-apply))
     (funcall function-to-apply kb key known-context-type bound-vars
	      (walk-subexpression 
	       kb :sentence language known-context-type bound-vars value
	       function-to-apply))))

(defmethods walk-key/value-plist-pair
 ((kb t) (key (eql :<=>)) (language cml-language)
  known-context-type (bound-vars t) (value t) (function-to-apply t))
 (if (nil-p value)
     (funcall function-to-apply kb key known-context-type bound-vars
	      (walk-subexpression kb :lisp-object language known-context-type
				  bound-vars (nil-symbol value)
				  function-to-apply))
     (funcall function-to-apply kb key known-context-type bound-vars
	      (walk-subexpression kb :sentence language known-context-type
				  bound-vars value function-to-apply))))

(defun true-keyword-p (thing)
  (and (symbolp thing)
       (let ((match (find thing '(:true)
			  :test #'string-equal)))
	 (and match (with-kif-replacement thing match)))))

(defun false-keyword-p (thing)
  (and (symbolp thing)
       (let ((match (find thing '(:false)
			  :test #'string-equal)))
	 (and match (with-kif-replacement thing match)))))

(defun walk-relation-type-qualifier
    (kb key language known-context-type bound-vars value function-to-apply)
  (cond ((false-keyword-p value)
	 (funcall function-to-apply kb key known-context-type bound-vars
		  (walk-subexpression kb :lisp-object language
				      known-context-type bound-vars
				      (false-keyword-p value)
				      function-to-apply)))
	((true-keyword-p value)
	 (funcall function-to-apply kb key bound-vars
		  (walk-subexpression kb :lisp-object language
				      known-context-type bound-vars
				      (true-keyword-p value)
				      function-to-apply)))
	(t (parser-warn 'illegal-qualifier kb "~S should be TRUE or FALSE."
			value)
	   value)))

(defmethods walk-key/value-plist-pair
 ((kb t) (key (eql :function)) (language cml-language)
  known-context-type (bound-vars t) (value t) (function-to-apply t))
 (walk-relation-type-qualifier kb key language known-context-type bound-vars
			       value function-to-apply))

(defmethods walk-key/value-plist-pair
 ((kb t) (key (eql :attribute-function))
  (language cml-language) known-context-type (bound-vars t) (value t)
  (function-to-apply t))
 (walk-relation-type-qualifier kb key language known-context-type bound-vars
			       value function-to-apply))

(defmethods walk-key/value-plist-pair
 ((kb t) (key (eql :participant-function))
  (language cml-language) known-context-type (bound-vars t) (value t)
  (function-to-apply t))
 (walk-relation-type-qualifier kb key language known-context-type bound-vars
			       value function-to-apply))

(defmethods walk-key/value-plist-pair
 ((kb t) (key (eql :time-dependent)) (language cml-language)
  known-context-type (bound-vars t) (value t) (function-to-apply t))
 (walk-relation-type-qualifier kb key language known-context-type bound-vars
			       value function-to-apply))

(defmethods walk-key/value-plist-pair
 ((kb t) (key (eql :attach-to)) (language cml-language)
  known-context-type (bound-vars t) (value t) (function-to-apply t))
 (walk-subexpression kb :constant language known-context-type bound-vars value
		     function-to-apply))

(defmethods walk-key/value-plist-pair
 ((kb t) (key (eql :non-numeric)) (language cml-language)
  known-context-type (bound-vars t) (value t) (function-to-apply t))
 (walk-relation-type-qualifier kb key language known-context-type bound-vars
			       value function-to-apply))

(defmethods walk-key/value-plist-pair
 ((kb t) (key (eql :piecewise-continuous))
  (language cml-language) known-context-type (bound-vars t) (value t)
  (function-to-apply t))
 (walk-relation-type-qualifier kb key language known-context-type bound-vars
			       value function-to-apply))

(defmethods walk-key/value-plist-pair
 ((kb t) (key (eql :step-quantity)) (language cml-language)
  known-context-type (bound-vars t) (value t) (function-to-apply t))
 (walk-relation-type-qualifier kb key language known-context-type bound-vars
			       value function-to-apply))

(defmethods walk-key/value-plist-pair
 ((kb t) (key (eql :count-quantity)) (language cml-language)
  known-context-type (bound-vars t) (value t) (function-to-apply t))
 (walk-relation-type-qualifier kb key language known-context-type bound-vars
			       value function-to-apply))

(defmethods walk-key/value-plist-pair
 ((kb t) (key (eql :type)) (language cml-language)
  known-context-type (bound-vars t) (value t) (function-to-apply t))
 (if (object-constant-p value kb language)
     (funcall function-to-apply kb key known-context-type bound-vars
	      (walk-subexpression kb :relconst language
				  known-context-type bound-vars value
				  function-to-apply))
     (parser-warn 'illegal-type kb "~S should be a type." value)))

(defun walk-cml-slot-descriptors
    (kb key language known-context-type bound-vars value function-to-apply
	class)
  (if (listp-or-kif-nil value)
      (funcall function-to-apply kb key bound-vars
	       (loop for s in (list-or-kif value)
		     collect (walk-cml-slot-descriptor
			      kb language known-context-type bound-vars s
			      function-to-apply class)))
      (progn (parser-warn 'illegal-slot-list kb
			  "~S should be a slot list." value)
	     value)))

(defun walk-cml-slot-descriptor
    (kb language known-context-type bound-vars s function-to-apply class)
  (declare (ignore class))
  (if (consp s)
      `(,(walk-subexpression 
	  kb :relconst language :slot bound-vars (first s)
	  function-to-apply)
	,@(walk-key/value-plist
	   kb language known-context-type bound-vars (rest s)
	   function-to-apply))
      (progn (parser-warn 'illegal-slot-spec kb
			  "~S should be a slot descriptor" s)
	     s)))

(defmethods walk-key/value-plist-pair
 ((kb t) (key (eql :attributes)) (language cml-language)
  known-context-type (bound-vars t) (value t) (function-to-apply t))
 (let ((*slot-type-being-walked* :attributes))
   (walk-cml-slot-descriptors
    kb key language known-context-type bound-vars value function-to-apply
    'attribute-function-definition)))

(defmethods walk-key/value-plist-pair
 ((kb t) (key (eql :participants)) (language cml-language)
  known-context-type (bound-vars t) (value t) (function-to-apply t))
 (let ((*slot-type-being-walked* :participants))
   (walk-cml-slot-descriptors
    kb key language known-context-type bound-vars value function-to-apply
    'participant-function-definition)))

(defmethods walk-key/value-plist-pair
 ((kb t) (key (eql :quantities)) (language cml-language)
  known-context-type (bound-vars t) (value t) (function-to-apply t))
 (let ((*slot-type-being-walked* :quantities))
   (walk-cml-slot-descriptors
    kb key language known-context-type bound-vars value function-to-apply
    'quantity-function-slot-definition)))

(defmethods walk-key/value-plist-pair
 ((kb t) (key (eql :consequences)) (language cml-language)
  known-context-type (bound-vars t) (value t) (function-to-apply t))
 (if (listp-or-kif-nil value)
     (funcall function-to-apply kb key known-context-type bound-vars
	      (loop for term in (list-or-kif value)
		    collect (walk-subexpression
			     kb :consequence language known-context-type
			     bound-vars term function-to-apply)))
     (parser-warn 'illegal-slot-list kb
		  "~S should be a list of consequences." value)))

(defmethods walk-key/value-plist-pair
 ((kb t) (key (eql :conditions)) (language cml-language)
  known-context-type (bound-vars t) (value t) (function-to-apply t))
 (if (listp-or-kif-nil value)
     (funcall function-to-apply kb key known-context-type bound-vars
	      (loop for term in (list-or-kif value)
		    collect (walk-subexpression
			     kb :condition language known-context-type
			     bound-vars term function-to-apply)))
     (parser-warn 'illegal-slot-list kb
		  "~S should be a list of conditions." value)))

(defmethods walk-key/value-plist-pair
 ((kb t) (key (eql :subclass-of)) (language cml-language)
  known-context-type (bound-vars t) (value t) (function-to-apply t))
 (if (listp-or-kif-nil value)
     (funcall function-to-apply kb key known-context-type bound-vars
	      (loop for term in (list-or-kif value)
		    when (not (object-constant-p term kb language))
		    do (parser-warn 'illegal-subclass kb
				    "~S should be a subclass-name list" value)
		    collect (walk-subexpression
			     kb :term language known-context-type bound-vars
			     term function-to-apply)))
     (progn (parser-warn 'illegal-subclases kb
			 "~S should be a list of subclasses" value)
	    value)))

(defmethods walk-key/value-plist-pair
 ((kb t) (key (eql :individuals)) (language cml-language)
  known-context-type (bound-vars t) (value t) (function-to-apply t))
 (if (listp-or-kif-nil value)
     (funcall function-to-apply kb key known-context-type bound-vars
	      (loop for v in (list-or-kif value)
		    collect (walk-subexpression kb :individual-spec language
						known-context-type bound-vars
						v function-to-apply)))
     (progn (parser-warn 'illegal-individuals kb
			 "~S should be a list of individual specs." value)
	    value)))

(defmethods walk-key/value-plist-pair
 ((kb t) (key (eql :time-step-size)) (language cml-language)
  known-context-type (bound-vars t) (value t) (function-to-apply t))
 (funcall function-to-apply kb key known-context-type bound-vars
	  (walk-subexpression kb :quantity-expression language
			      known-context-type bound-vars value
			      function-to-apply)))

(defmethods walk-key/value-plist-pair
 ((kb t) (key (eql :initial-time)) (language cml-language)
  known-context-type (bound-vars t) (value t) (function-to-apply t))
 (funcall function-to-apply kb key known-context-type bound-vars
	  (walk-subexpression kb :number language known-context-type bound-vars
			      value function-to-apply)))

(defmethods walk-key/value-plist-pair
 ((kb t) (key (eql :final-time)) (language cml-language)
  known-context-type (bound-vars t) (value t) (function-to-apply t))
 (funcall function-to-apply kb key known-context-type bound-vars
	  (walk-subexpression kb :number language known-context-type bound-vars
			      value function-to-apply)))

(defmethods walk-key/value-plist-pair
 ((kb t) (key (eql :initially)) (language cml-language)
  known-context-type (bound-vars t) (value t) (function-to-apply t))
 (if (listp-or-kif-nil value)
     (let ((*allowed-variables-in-literals* nil))
       (funcall function-to-apply kb key known-context-type bound-vars
		(loop for v in (list-or-kif value)
		      collect (walk-subexpression kb :literal language
						  known-context-type
						  bound-vars v
						  function-to-apply))))
     (progn (parser-warn 'illegal-initially kb
			 "~S should be a list of literals." value)
	    value)))

(defmethods walk-key/value-plist-pair
 ((kb t) (key (eql :throughout)) (language cml-language)
  known-context-type (bound-vars t) (value t) (function-to-apply t))
 (if (listp-or-kif-nil value)
     (let ((*allowed-variables-in-literals* nil))
       (funcall function-to-apply kb key known-context-type bound-vars
		(loop for v in (list-or-kif value)
		      collect (walk-subexpression kb :literal language
						  known-context-type
						  bound-vars v
						  function-to-apply))))
     (progn (parser-warn 'illegal-throughout kb
			 "~S should be a list of literals." value)
	    value)))

(defmethods walk-key/value-plist-pair
 ((kb t) (key (eql :boundary)) (language cml-language)
  known-context-type (bound-vars t) (value t) (function-to-apply t))
 (if (listp-or-kif-nil value)
     (funcall function-to-apply kb key known-context-type bound-vars
	      (loop for v in (list-or-kif value)
		    collect (walk-subexpression kb :quantity-expression
						language known-context-type
						bound-vars v
						function-to-apply)))
     (progn (parser-warn 'illegal-boundary kb
			 "~S should be a list of quantity expressions." value)
	    value)))

(defmethods walk-key/value-plist-pair
 ((kb t) (key (eql :dimension)) (language cml-language)
  known-context-type (bound-vars t) (value t) (function-to-apply t))
 (walk-subexpression kb :dimension-expression language known-context-type
		     bound-vars value function-to-apply))

(defmethods walk-key/value-plist-pair
 ((kb t) (key (eql :documentation)) (language cml-language)
  known-context-type (bound-vars t) (value t) (function-to-apply t))
  (when (not (or (not value) (stringp value)))
    (parser-warn 'illegal-doc-string kb "~S should be a doc string." value))
  (walk-subexpression kb :lisp-object language known-context-type
		      bound-vars value function-to-apply))

;=============================================================================

;;; Extra language support.

(defokbcgeneric explain-language (stream language)
  (:method-combination or)
  (:documentation
   "Generates an HTML string explaining the language in question."))

(defun trimmed-language-name (class)
  (let ((name (if (typep class 'standard-class)
		  (class-name class)
		  (class-name (class-of class)))))
    (let ((language-index (search "-LANGUAGE" (symbol-name name)
				  :test #'char-equal)))
      (substitute #\space #\-
		  (string-upcase
		   (if language-index
		       (subseq (symbol-name name) 0
			       language-index)
		       (symbol-name name)))))))

(defvar *html-replacements-list*
	'((#\< "&lt;") (#\> "&gt;") (#\" "&quot;") (#\& "&amp;"))
  "List of characters that have to be escaped in html")

(defvar *html-replacements-table*
  (let ((table (make-array 256 :initial-element nil)))
    (loop for (char mapping) in *html-replacements-list*
	  do (setf (aref table (char-code char)) mapping))
    table))

(defun format-html-char (stream char)
  (let ((entry (aref (the #+lucid simple-vector #-lucid array
			  *html-replacements-table*)
		     (char-code char))))
    (if entry
	(write-string entry stream)
	(write-char char stream))))

(defun format-html-string
    (stream string &optional (from 0 supplied-p)
	    (to (length (the #+Lucid simple-string #-lucid string string))))
  (if stream
      (progn 
	(loop for index from from below to
	      for x = (aref (the #+Lucid simple-string
				 #-lucid string string)
			    (the fixnum index))
	      for entry = (aref (the #+lucid simple-vector #-lucid array
				     *html-replacements-table*)
				(char-code x))
	      do (if entry
		     (write-string entry stream)
		     (write-char x stream)))
	string)
      (with-output-to-string (str)
	(if supplied-p
	    (format-html-string str string from to)
	    (format-html-string str string)))))

(defun format-html (stream format-string &rest l)
  (let ((string (or (if format-string
			(if (find #\~ format-string :test #'char=)
			    (ignore-errors
			     (apply #'format nil format-string l))
			    format-string)
			nil)
			
		    "????")))
    (declare (type #+Lucid simple-string #-lucid string string))
    (length (format-html-string stream string))))

(defmethod explain-language :around ((stream t) (language abstract-language))
 (format stream "<TITLE>")
 (format-html stream "Documentation for language ~A"
	      (trimmed-language-name language))
 (format stream "</TITLE>")
 (format stream "<H2>")
 (format-html stream "Documentation for language ~A"
	      (trimmed-language-name language))
 (format stream "</H2>")
 (format stream "The following constructs are allowed:")
 (format stream "<UL>")
 (call-next-method)
 (format stream "</UL>"))

(defmethod explain-language or ((stream t) (language t))
 (format stream "<LI>")
 (format stream "<code>(in-language lll)</code>, where <code>lll</code> is
      the name of a language.")
 (format stream "<LI>")
 (format stream "<code>(in-kb kkk)</code>, where <code>kkk</code> is
      the name of a KB of the same type as the current KB.")
 (format stream "<LI>")
 (format stream "<code>(in-package ppp)</code>, where <code>ppp</code> is
      the name of a package.")
 t)

(defmethod explain-language or ((stream t) (language ansi-kif-language))
 (format stream "<LI>")
 (format
  stream "Any ANSI KIF <i>form</i> is permitted.  This includes any ANSI KIF
            definition form such as <code>defrelation</code> and any top-level
            ANSI KIF sentence.  The KIF specification can be found
            <a href=http://logic.stanford.edu/kif/kif.html><b>here</b></a>.")
 nil)

(defmethod explain-language or ((stream t) (language kif-3.0-language))
 (format stream "<LI>")
 (format
  stream "Any KIF 3.0 <i>form</i> is permitted.  This includes any KIF 3.0
            definition form such as <code>defrelation</code> and any top-level
            KIF 3.0 sentence.")
 nil)

(defvar *define-okbc-frame-grammar*
  "<pre>
   define-okbc-frame-form ::= ( define-okbc-frame frame-name
                              keyword-value-pairs* )
   frame-name ::= generalized-string
   keyword-value-pairs ::= keyword-value-pair |
                           keyword-value-pair keyword-value-pairs
   keyword-value-pair ::= [type-key | direct-types-key
                          | direct-superclasses-key
                          | own-slots-key | template-slots-key
                          | own-facets-key | template-facets-key
                          | sentences-key | kb-key ]
   type-key ::= :frame-type [:class | :slot | :facet | :individual]
   direct-types-key ::= :direct-types ( frame-reference* )
   frame-reference ::= generalized-string |
                       &lt;&lt;frame-handle&gt;&gt; |
                       &lt;&lt;frame-object&gt;&gt;
   direct-superclasses-key ::= :direct-superclasses ( frame-reference* )
   own-slots-key ::= :own-slots ( slot-spec* )
   template-slots-key ::= :template-slots ( slot-spec* )
   slot-spec ::= ( slot-name value-spec* )
   slot-name ::= frame-reference
   value-spec ::= constant | ( SETOF constant* )
                  | ( QUOTE &lt;&lt;lisp-s-expression&gt;&gt; )
                  | ( :DEFAULT value-spec )
   constant ::= &lt;&lt;number&gt;&gt; |
                generalized-string |
                &lt;&lt;frame-handle&gt;&gt; |
                &lt;&lt;frame-object&gt;&gt;
   own-facets-key ::= :own-facets ( own-facets-spec* )
   own-facet-spec ::= ( slot-name facet-component* )
   template-facets-key ::= :template-facets ( template-facets-spec* )
   template-facets-spec ::= ( slot-name facet-component* )
   facet-component ::= ( facet-name value-spec* )
   sentences-key ::= :sentences ( &lt;&lt;KIF-sentence&gt;&gt;* )
   kb-key ::= :kb knowledge-base-ref
   knowledge-base-ref ::= &lt;&lt;knowledge-base&gt;&gt; |
                          generalized-string</PRE>")

(defmethod explain-language or ((stream t) (language okbc-language))
 (format stream "<LI>")
 (format
  stream "Any OKBC <code>define-okbc-frame</code> form is permitted.  The
            grammar of these forms is defined as follows:~A"
   *define-okbc-frame-grammar*)
 nil)

(defmethod explain-language or ((stream t) (language standard-class))
 (explain-language stream (class-prototype-safe language)))

(defmethod explain-language or ((stream t) (language symbol))
 (explain-language stream (find-language language)))


