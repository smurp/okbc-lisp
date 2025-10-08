(in-package :tuple-kb)

;;; The following are magic symbols that should be stripped out before
;;; we return anything from the tuple-kb back end.

;;;  __template-facet-value         ;; looks like a quat
;;;  __default-template-facet-value ;; looks like a quat
;;;  __default-facet-value          ;; looks like a quat
;;;  __template-slot-value          ;; looks like a facet
;;;  __default-template-slot-value  ;; looks like a facet
;;;  __default-slot-value           ;; looks like a facet
;;;  __template-facet-of            ;; looks like a facet
;;;  __facet-of                     ;; looks like a facet
;;;  __template-slot-of             ;; looks like a slot
;;;  __slot-of                      ;; looks like a slot
;;;  __subclass-of                  ;; looks like a slot
;;;  __instance-of                  ;; looks like a slot
;;;  __name                         ;; looks like a slot
;;;  __pretty-name                  ;; looks like a slot
;;;  __has-sentence                 ;; looks like a slot
;;;  __individual                   ;; looks like a class
;;;  __class                        ;; looks like a class
;;;  __facet                        ;; looks like a class
;;;  __slot                         ;; looks like a class
;;;  __primitive                    ;; looks like a class

(defparameter *tuplekb-file-format* :lisp)

(defun hash-table-reader (stream char arg)
  (declare (ignore char arg))
  (let ((spec (read stream t nil t)))
    (let ((test (pop spec))
	  (size (pop spec)))
      (let ((ht (make-hash-table :test test :size size)))
	(loop for key = (pop spec)
	      for value = (pop spec)
	      do (setf (gethash key ht) value))
	ht))))

#+allegro
(defmacro fixnump (x) (excl:fixnump x))

(defun stashed-symbol-reader (stream char arg)
  (declare (ignore char arg))
  (declare (special *symbol-stash-index-table*))
  (let ((number (read stream t nil t)))
    (assert (fixnump number) ()
	    "Expected a fixnum after the #@ reader macro, but got: ~S"
	    number)
    (or (aref *symbol-stash-index-table* (the fixnum number))
	(error "No symbol matching ~S found." number))))

(defparameter *tuplekb-readtable*
  (let ((rt (copy-readtable)))
    ;;; (setf (readtable-case rt) :preserve) ;; if we want to be case-sensitive
    (set-dispatch-macro-character #\# #\$ 'ok-back:frame-handle-reader rt)
    (set-dispatch-macro-character #\# #\H 'hash-table-reader rt)
    (set-dispatch-macro-character #\# #\@ 'stashed-symbol-reader rt)
    (set-dispatch-macro-character #\# #\Q 'ok-back:quasi-symbol-reader rt)
    rt))

(defmethod frs-name-internal
    ((kb-type tuple-kb) (connection local-connection))
  "Tuple KB")

(defmethod frs-name-internal
    ((kb-type structure-tuple-kb) (connection local-connection))
  "Structure Tuple KB")

(defmethods print-quasi-symbol-in-kb
    (instance (kb (tuple-kb structure-tuple-kb)) stream)
  (if (eq :file *current-purpose-for-io-syntax*)
      (format stream "#Q~S|~S"
	(name (quasi-symbol-package instance))
	(name instance))
      (call-next-method)))

(defmethod print-fact ((fact t) (kb t) (stream t))
  (error "Unhandled data type: ~S" fact))

(defmethod print-fact ((fact integer) (kb t) (stream t))
  (if (fixnump fact)
      (fast-write-fixnum fact stream)
      (prin1 fact stream)))

(defmethods print-fact ((fact (float string)) (kb t) (stream t))
  (prin1 fact stream))

(defun allocate-symbol-stash-indices (tree)
  (declare (special *symbol-stash-counter* *symbol-stash-table*))
  (typecase tree
    (cons (allocate-symbol-stash-indices (first tree))
	  (allocate-symbol-stash-indices (rest tree)))
    (symbol (or (fast-gethash-for-symbol tree *symbol-stash-table*)
		(let ((num (incf *symbol-stash-counter*)))
		  (setf (gethash (the symbol tree)
				 *symbol-stash-table*)
			num))))
    (otherwise nil)))

(defmethod print-fact ((fact symbol) (kb t) (stream t))
  (declare (special *symbol-stash-table*))
  (let ((entry (or (fast-gethash-for-symbol fact *symbol-stash-table*)
		   (error "Symbol index not found for ~S" fact))))
    (fast-write-string "#@" stream)
    (fast-write-fixnum entry stream)))

(defmethod print-fact ((fact cons) (kb t) (stream t))
  (fast-write-string "(" stream)
  (loop with remaining = fact
	for first-p = t then nil
	when (not remaining) return nil
	when (not first-p) do (fast-write-string " " stream)
	do (let ((element (pop remaining)))
	     (print-fact element kb stream))
	when (not (listp remaining))
	do (fast-write-string " . " stream)
	   (print-fact remaining kb stream)
	   (return nil))
   (fast-write-string ")" stream))

(defmethod print-fact ((fact frame-handle) (kb t) (stream t))
  (fast-write-string "#$(" stream)
  (print-fact (ok-back:frame-handle-id fact) kb stream)
  (fast-write-string " " stream)
  (if (eq (unique-id kb) (ok-back:frame-handle-kb-id fact))
      (fast-write-string "!" stream)
      (print-fact (ok-back:frame-handle-kb-id fact) kb stream))
  (fast-write-string ")" stream))

(defmethod print-fact ((fact hash-table) (kb t) (stream t))
  (fast-write-string "#H(" stream)
  (print-fact (hash-table-test fact) kb stream)
  (fast-write-string " " stream)
  (print-fact (hash-table-size fact) kb stream)
  (maphash #'(lambda (k v)
	       (fast-write-string " " stream)
	       (print-fact k kb stream)
	       (fast-write-string " " stream)
	       (print-fact v kb stream))
	   fact)
  (fast-write-string ")" stream))

(defparameter *tuplekb-internal-quatlike-relations*
  '(__template-facet-value __default-template-facet-value
    __default-facet-value))

(defparameter *tuplekb-internal-facetlike-relations*
  '(__template-slot-value __default-template-slot-value
    __default-slot-value __template-facet-of
    __facet-of))

(defparameter *tuplekb-internal-slotlike-relations*
  '(__name __pretty-name __subclass-of __template-slot-of __slot-of
    __has-sentence __instance-of))

(defparameter *tuplekb-internal-classlike-relations*
  '(__primitive __slot __facet __class __individual))

(defparameter *tuplekb-internal-relations*
  (append *tuplekb-internal-quatlike-relations*
	  *tuplekb-internal-facetlike-relations*
	  *tuplekb-internal-slotlike-relations*
	  *tuplekb-internal-classlike-relations*))

(defparameter *tuplekb-backtranslation-alist*
  (loop for sym in *tuplekb-internal-relations*
	collect (cons sym (intern (subseq (symbol-name sym) 2) :keyword))))

(defparameter *tuplekb-translation-alist*
  (loop for sym in *tuplekb-internal-relations*
	collect (cons (intern (subseq (symbol-name sym) 2) :keyword) sym)))

(defparameter *non-okbc-mapping-internal-relations*
  (loop for sym in *tuplekb-internal-relations*
	for key = (rest (assoc sym *tuplekb-backtranslation-alist*))
	unless (or (member key *okbc-relation-symbols*)
		   (and (member key *okbc-standard-names*)
			(not (member key ok-back:*kif-meta-extension-symbols*)))
		   (member key *kif-operator-symbols*)
		   (member key *evaluable-predicate-symbols*))
	collect sym))

(defparameter *tuplekb-defaulting-relations-alist*
  (loop for sym in *tuplekb-internal-relations*
	when (search "__DEFAULT" (symbol-name sym) :test #'char=)
	collect (list sym (or (second (assoc sym
					     '((__default-template-facet-value
						__template-facet-value)
					       (__default-facet-value
						:none)
					       (__default-template-slot-value
						__template-slot-value)
					       (__default-slot-value
						:none))))
			      (error "Missing non-default-entry for ~S"
				     sym)))))

;;; For structure-tuple-kb only/define only once

(defun specific-type-from-frame-type (frame-type kb kb-local-only-p
						 &optional (recursive-p nil))
  (or (ecase frame-type
	(:individual (individual-frame kb nil))
	(:facet      (facet-frame kb nil))
	(:slot       (slot-frame kb nil)))
      (if recursive-p
	  (error "Recursive error in finding kernel class ~S!" frame-type)
	  (progn (warn "Kernel class ~S is missing.  ~%~
                        Reasserting kernel ontology" frame-type)
		 (initialize-tuple--kb kb)
		 (specific-type-from-frame-type
		  frame-type kb kb-local-only-p t)))))

(defun create-reified-standard-non-class (name frame-type kb kb-local-only-p)
  (with-read-only-checking 
      (kb)
    (let ((frame (allocate-frame-handle-internal name frame-type kb nil))
	  (frame-frame (frame-frame kb nil))
	  (specific-type
	   (specific-type-from-frame-type frame-type kb kb-local-only-p)))
      (insert `(__name ,frame ,name) (tuple-kb-tuple-store kb) t)
      (insert `(__instance-of ,frame ,frame-frame) (tuple-kb-tuple-store kb) t)
      (insert `(__instance-of ,frame ,specific-type)
	      (tuple-kb-tuple-store kb) t)
      frame)))

(defun create-reified-non-class
    (name frame-type direct-types kb doc own-slots own-facets handle
	  pretty-name kb-local-only-p)
  (declare (special *okbc-standard-names*))
  (if (and (member name *okbc-standard-names*)
	   (not (member name ok-back:*kif-meta-extension-symbols*)))
      (progn
	(continuable-assert (not (direct-coercible-to-frame-p
				  name kb kb-local-only-p))
			    frame-already-exists :frame name :kb kb)
	(create-reified-standard-non-class name frame-type kb kb-local-only-p))
      (let ((names-required-p (not (member nil (internal-get-behavior-values
						:frame-names-required kb)))))
	(continuable-assert (or name (not names-required-p)))
	(with-read-only-checking 
	    (kb)
	  (let ((frame (or handle
			   (if names-required-p
			       (multiple-value-bind (existing found-p)
				   (coerce-to-frame-internal name kb nil
							     kb-local-only-p)
				 (if found-p
				     (get-frame-handle-internal
				      existing kb kb-local-only-p)
				     (allocate-frame-handle-internal
				      name frame-type kb nil)))
			       (allocate-frame-handle-internal
				name frame-type kb nil))))
		(specific-type (specific-type-from-frame-type
				frame-type kb kb-local-only-p)))
	    (when name (put-frame-name-internal frame name kb kb-local-only-p))
	    (insert `(__instance-of ,frame ,(frame-frame kb nil))
		    (tuple-kb-tuple-store kb) t)
	    (loop for type in (remove-duplicates
			       (cons specific-type (list-if-not direct-types)))
		  do (add-instance-type-internal
		      frame type kb kb-local-only-p))
	    (when doc
	      (add-slot-value-internal
	       frame :documentation doc kb :equal :own
	       nil :known-true kb-local-only-p))
	    (initialize-slots-and-facets frame kb own-slots own-facets :own
					 kb-local-only-p)
	    (when pretty-name
	      (put-frame-pretty-name-internal
	       frame pretty-name kb kb-local-only-p))
	    frame)))))

(defmethod parent-kbs ((instance structure-tuple-kb))
  (structure-tuple-kb-parent-kbs instance))

(defmethod parent-kbs ((instance tuple-kb))
  (tuple-kb-parent-kbs instance))

;------------------------------------------------------------------------------

(defun coerce-literal-to-tuplekb-frame (frame kb error-p kb-local-only-p)
  (if frame
      (if (member nil (internal-get-behavior-values :frame-names-required kb))
      ;;; frame names are not unique
	  (if error-p
	      (error 'not-coercible-to-frame :frame frame :kb kb)
	      (values nil nil))
	  (let ((frame? (get-simple-frame-with-slot-value
			 '__name frame kb kb-local-only-p)))
	    (if (and frame? (not (eq frame frame?)))
		(coerce-to-frame-internal frame? kb error-p kb-local-only-p)
		(if error-p
		    (error 'not-coercible-to-frame :frame frame :kb kb)
		    (values nil nil)))))
      (if error-p
	  (error 'not-coercible-to-frame :frame frame :kb kb)
	  (values nil nil))))

(defun slot-attachment-fact (frame slot kb slot-type kb-local-only-p)
  (let ((frame-obj
	 (or (coerce-to-frame-internal frame kb nil kb-local-only-p) frame))
	(slot  (coerce-to-slot-internal   slot kb t kb-local-only-p)))
    (continuable-assert
     (frame-handle-p frame-obj) nil "Frame ~S does not exist." frame)
    (continuable-assert
     (or (eq slot-type :own)
	 (not (coercible-to-frame-p-internal frame-obj kb kb-local-only-p))
	 (class-p-internal frame kb kb-local-only-p))
     nil "Cannot attach/detach a template slot for a non-class.")
    (ecase slot-type
      (:own `(__slot-of ,slot ,frame-obj))
      (:template `(__template-slot-of ,slot ,frame-obj)))))

(defun facet-attachment-fact (frame slot facet kb slot-type kb-local-only-p)
  (let ((frame-obj (or (coerce-to-frame-internal frame kb nil kb-local-only-p)
		       frame))
	(slot-obj (or (coerce-to-slot-internal slot kb nil kb-local-only-p)
		      slot))
	(facet (coerce-to-facet-internal facet kb t kb-local-only-p)))
    (continuable-assert
     (frame-handle-p frame-obj) nil "Frame ~S does not exist." frame)
    (continuable-assert
     (frame-handle-p slot-obj) nil "Slot ~S does not exist." frame)
    (continuable-assert
     (or (eq slot-type :own)
	 (not (coercible-to-frame-p-internal frame-obj kb kb-local-only-p))
	 (class-p-internal frame-obj kb kb-local-only-p))
     nil "Cannot attach/detach a template facet for a non-class.")
    (ecase slot-type
      (:own `(__facet-of ,facet ,slot-obj ,frame-obj))
      (:template `(__template-facet-of ,facet ,slot-obj ,frame-obj)))))

;==============================================================================
;;; Define the fact store using a trie etc.

;==============================================================================
;==============================================================================

;;; Note:  this must be written in terms of stuff that doesn't touch
;;; get-kbs-of-type-internal through the meta-kb's methods.
(defmethods get-kbs-of-type-internal ((kb-type (structure-tuple-kb tuple-kb))
				      (connection t))
  (let ((meta-kb (meta-kb-internal connection)))
    (ok-back:relation-transitive-closure
     (class-of kb-type) meta-kb
     #'get-class-instances-internal-implementation
     (list meta-kb :direct :all t)
     #'get-class-subclasses-internal
     (list meta-kb :direct :all t)
     t)))

(defparameter *root-path-for-saved-tuplekbs*
  #+Lucid (pwd)
  #+Harlequin-Common-Lisp (hcl:get-working-directory)
  #+(and Allegro (not (and allegro-version>= (version>= 5))))
  (with-open-stream
      (str (excl:run-shell-command  "pwd"
				    :output :stream :wait nil))
    (read-line str))
  #+(and Allegro allegro-version>= (version>= 5)) (excl:current-directory)
  #-(or Allegro Lucid Harlequin-Common-Lisp)
  (progn (cerror "Go ahead, anyway" "Implement PWD") nil))

;(defmethods find-kb-locator-internal
;    ((thing tuplekb-locator) (kb-type (structure-tuple-kb tuple-kb))
;     (connection t))
;  thing)
;
;(defmethods find-kb-locator-internal
;    ((thing symbol) (kb-type (structure-tuple-kb tuple-kb)) (connection t))
;  (let ((type (ignore-errors (get-kb-type-internal thing connection))))
;    (and type (find-kb-locator-internal type kb-type connection))))
;
;
;(defmethods save-kb-as-internal ((new-name-or-locator t)
;                                 (kb (structure-tuple-kb tuple-kb)))
;  (setf (name kb) new-name-or-locator)
;  (put-frame-name-internal kb new-name-or-locator
;                           (meta-kb-internal (connection kb)) t)
;  (save-kb-internal kb t))
;
;(defmethods save-kb-as-internal ((new-name-or-locator tuplekb-locator)
;                                 (kb (structure-tuple-kb tuple-kb)))
;  (setf (name kb) (name new-name-or-locator))
;  (put-frame-name-internal kb (name kb) (meta-kb-internal (connection kb))
;                           t)
;  (save-kb-internal kb t))
;
;(defmethods expunge-kb-internal ((kb-locator t)
;                                 (kb-type (structure-tuple-kb tuple-kb))
;                                 (connection t) (error-p t))
;  (continuable-assert (typep kb-locator 'tuplekb-locator) nil
;                      "Locator ~S is not of the right type" kb-locator)
;  (ignore-errors (delete-file (tuplekb-locator-pathname kb-locator))))

(defmethods openable-kbs-internal ((kb-type (structure-tuple-kb tuple-kb))
				   (connection t) (place t))
  (let ((root-dir (if place
		      (typecase place
			(string (pathname place))
			(pathname place)
			(otherwise nil))
		      *root-path-for-saved-tuplekbs*)))
    (if root-dir
	(let ((paths (directory (make-pathname
				 :defaults root-dir
				 :name :wild
				 :type "kb"))))
	  (let ((existing-locators
		 (let ((locators (get-class-instances-internal
				  :kb-locator (meta-kb-internal connection)
				  :taxonomic :all nil)))
		   (loop for locator in locators
			 when (typep locator 'tuplekb-locator)
			 collect locator))))
	    (let ((to-return nil))
	      (loop for path in paths
		    for match = (find path existing-locators
				      :key 'tuplekb-locator-pathname
				      :test 'equalp)
		    when match
		    do (push match to-return)
		    (setq existing-locators (remove match existing-locators))
		    when (not match)
		    do (let ((instance (make-tuplekb-locator
					:name (with-standard-io-syntax
						  (safely-read-from-string
						   (pathname-name path)))
					:kb-type kb-type
					:pathname path)))
			 (put-instance-types-internal
			  instance :kb-locator (meta-kb-internal connection) t)
			 (push instance to-return)))
	      (loop for loc in existing-locators
		    do (delete-frame-internal loc (meta-kb-internal connection)
					      t))
	      to-return)))
	nil)))

(defmethods delete-slot-internal
    ((slot t) (kb (structure-tuple-kb tuple-kb)) (kb-local-only-p t))
  (delete-frame-internal slot kb kb-local-only-p))

(defmethods delete-facet-internal
    ((facet t) (kb (structure-tuple-kb tuple-kb)) (kb-local-only-p t))
  (delete-frame-internal facet kb kb-local-only-p))

(defmethods rename-slot-internal ((slot t) (new-name t)
				  (kb (structure-tuple-kb tuple-kb))
				  (kb-local-only-p t))
  (put-frame-name-internal slot new-name kb kb-local-only-p))

(defmethods rename-facet-internal ((facet t) (new-name t)
				   (kb (structure-tuple-kb tuple-kb))
				   (kb-local-only-p t))
  (put-frame-name-internal facet new-name kb kb-local-only-p))


(defmethods create-facet-internal
    ((name t) (kb (structure-tuple-kb tuple-kb)) (frame-or-nil t)
     (slot-or-nil t) (slot-type t) (direct-types t) (doc t) (own-slots t)
     (own-facets t) (handle t) (pretty-name t) (kb-local-only-p t))
  (let ((facet (create-reified-non-class
		name :facet direct-types kb doc own-slots own-facets handle
		pretty-name kb-local-only-p)))
    (when (and frame-or-nil slot-or-nil)
      (attach-facet-internal frame-or-nil slot-or-nil facet kb slot-type
			     kb-local-only-p))
    facet))

(defmethods create-slot-internal
    ((name t) (kb (structure-tuple-kb tuple-kb)) (frame-or-nil t)
     (slot-type t) (direct-types t) (doc t) (own-slots t) (own-facets t)
     (handle t) (pretty-name t) (kb-local-only-p t))
  (when (not (member name *tuplekb-internal-slotlike-relations*))
    (let ((slot (create-reified-non-class
		 name :slot direct-types kb doc own-slots own-facets handle
		 pretty-name kb-local-only-p)))
      (when frame-or-nil
	(attach-slot-internal frame-or-nil slot kb slot-type kb-local-only-p))
      slot)))

(defmethods coerce-to-frame-internal
    ((thing symbol) (kb (structure-tuple-kb tuple-kb)) (error-p t)
     (kb-local-only-p t))
  (declare (special *okbc-standard-names*))
  (if (member nil (internal-get-behavior-values :frame-names-required kb))
      (if (and (member thing *okbc-standard-names*)
	       (not (member thing ok-back:*kif-meta-extension-symbols*)))
	  (let ((frame? (get-simple-frame-with-slot-value
			 '__name thing kb kb-local-only-p)))
	    (if (and frame? (not (eq thing frame?)))
		(coerce-to-frame-internal frame? kb error-p kb-local-only-p)
	        (progn (warn "Consistency error:  Standard frame ~S is ~
                              missing.  Reasserting kernel ontology."
			     thing)
		       (initialize-tuple--kb kb)
		       (let ((frame? (get-simple-frame-with-slot-value
				      '__name thing kb kb-local-only-p)))
			 (if (and frame? (not (eq thing frame?)))
			     (coerce-to-frame-internal
			      frame? kb error-p kb-local-only-p)
			     (error "Consistency error:  Standard frame is ~
                                     missing."))))))
	  (call-next-method))
      (if (and (member thing *okbc-standard-names*)
	       (not (member thing ok-back:*kif-meta-extension-symbols*)))
	  (let ((frame? (get-simple-frame-with-slot-value
			 '__name thing kb kb-local-only-p)))
	    (if (and frame? (not (eq thing frame?)))
		(coerce-to-frame-internal frame? kb error-p kb-local-only-p)
	        (progn (warn "Consistency error:  Standard frame ~S is ~
                              missing.  Reasserting kernel ontology."
			     thing)
		       (initialize-tuple--kb kb)
		       (let ((frame? (get-simple-frame-with-slot-value
				      '__name thing kb kb-local-only-p)))
			 (if (and frame? (not (eq thing frame?)))
			     (coerce-to-frame-internal
			      frame? kb error-p kb-local-only-p)
			     (error "Consistency error:  Standard frame is ~
                                     missing."))))))
	  (coerce-literal-to-tuplekb-frame thing kb error-p kb-local-only-p))))

(defmethods coerce-to-frame-internal
    ((thing string) (kb (structure-tuple-kb tuple-kb)) (error-p t)
     (kb-local-only-p t))
  (if (member nil (internal-get-behavior-values :frame-names-required kb))
      (call-next-method)
      (coerce-literal-to-tuplekb-frame thing kb error-p kb-local-only-p)))

(defmethods coerce-to-frame-internal
    ((thing integer) (kb (structure-tuple-kb tuple-kb)) (error-p t)
     (kb-local-only-p t))
  (if (member nil (internal-get-behavior-values :frame-names-required kb))
      (call-next-method)
      (coerce-literal-to-tuplekb-frame thing kb error-p kb-local-only-p)))

(defmethods get-frame-name-internal
    ((frame t) (kb (structure-tuple-kb tuple-kb)) (kb-local-only-p t))
  (multiple-value-bind (frame? found-p)
      (coerce-to-frame-internal frame kb nil kb-local-only-p)
    (if found-p
	(let ((name (get-simple-own-slot-value
		     frame? '__name kb kb-local-only-p)))
	  (if name
	      name
	      (if (member nil (internal-get-behavior-values
			       :frame-names-required kb))
		  nil
		  (continuable-error
		   "Frame ~S has no name, but the :frame-names-required ~
                    requires that there be a name."
		   frame?))))
	(error 'not-coercible-to-frame :frame frame :kb kb))))

(defmethods put-frame-name-internal
    (frame new-name (kb (structure-tuple-kb tuple-kb)) kb-local-only-p)
  (if (get-simple-own-slot-value frame '__name kb kb-local-only-p)
      (put-slot-value-internal frame '__name new-name kb :own
			       :known-true kb-local-only-p)
      (add-slot-value-internal frame '__name new-name kb :equal :own nil
			       :known-true kb-local-only-p)))

(defmethods get-frame-pretty-name-internal
    ((frame t) (kb (structure-tuple-kb tuple-kb)) (kb-local-only-p t))
  (multiple-value-bind (frame? found-p)
      (coerce-to-frame-internal frame kb nil kb-local-only-p)
    (if found-p
	(or (get-simple-own-slot-value
	     frame? '__pretty-name kb kb-local-only-p)
	    (let ((name (get-frame-name-internal frame? kb kb-local-only-p)))
	      (or (and name (string-capitalize (string name)))
		  (if (and (typep frame 'frame-handle)
			   (getf (frame-handle-plist frame) :allocated-name))
		      (princ-to-string
		       (string-capitalize
			(getf (frame-handle-plist frame) :allocated-name)))
		      (princ-to-string frame?)))))
	(if (and (frame-handle-p frame)
		 (getf (frame-handle-plist frame) :allocated-name))
	    ;; Even if not frame-p we may be able to get a name for it!
	    (string-capitalize
	     (princ-to-string
	      (getf (frame-handle-plist frame) :allocated-name)))
	    (error 'not-coercible-to-frame :frame frame :kb kb)))))

(defmethods put-frame-pretty-name-internal
    (frame name (kb (structure-tuple-kb tuple-kb)) kb-local-only-p)
  (put-slot-value-internal frame '__pretty-name (string name) kb :own
			   :known-true kb-local-only-p))

(defmethods coerce-to-class-internal
    ((thing t) (kb (structure-tuple-kb tuple-kb)) (error-p t)
     (kb-local-only-p t))
  (let ((frame (or (coerce-to-frame-internal thing kb nil kb-local-only-p)
		   thing))
	(class-frame (class-frame kb nil)))
    (if (primitive-direct-instance-of-p frame class-frame kb kb-local-only-p)
	(values frame t)
	(if error-p
	    (error 'class-not-found
		   :missing-class thing
		   :kb kb)
	    (values nil nil)))))

(defmethods coerce-to-slot-internal
    ((thing t) (kb (structure-tuple-kb tuple-kb)) (error-p t)
     (kb-local-only-p t))
  (let ((frame (or (coerce-to-frame-internal thing kb nil kb-local-only-p)
		   thing))
	(slot-frame (slot-frame kb nil)))
    (if (primitive-direct-instance-of-p frame slot-frame kb kb-local-only-p)
	(values frame t)
	(if error-p
	    (error 'slot-not-found
		   :frame nil
		   :slot thing
		   :slot-type nil
		   :kb kb)
	    (values nil nil)))))

(defmethods coerce-to-facet-internal
    ((thing t) (kb (structure-tuple-kb tuple-kb)) (error-p t)
     (kb-local-only-p t))
  (let ((frame (or (coerce-to-frame-internal thing kb nil kb-local-only-p)
		   thing))
	(facet-frame (facet-frame kb nil)))
    (if (primitive-direct-instance-of-p frame facet-frame kb kb-local-only-p)
	(values frame t)
	(if error-p
	    (error 'facet-not-found
		   :frame nil
		   :slot nil
		   :facet thing
		   :slot-type nil
		   :kb kb)
	    (values nil nil)))))

(defmethods abstract-kb-class-name-from-kb ((instance tuple-kb))
  (intern (concatenate 'string "ABSTRACT-"
		       (symbol-name (type-of-name instance))
		       "-KB")
	  :ok-back))

(defmethods concrete-kb-class-from-abstract-kb-class-name
    ((name (eql 'ok-back::abstract-tuple-kb-kb)))
  'tuple-kb)

(defmethods allocate-frame-handle-internal 
  ((frame-name t) (frame-type t) (kb (structure-tuple-kb tuple-kb))
   (frame-handle frame-handle))
  frame-handle)

(defmethods allocate-frame-handle-internal
    ((frame-name t) (frame-type t) (kb (structure-tuple-kb tuple-kb))
     frame-handle)
  (let ((handle 
	 (if (and (member frame-name *okbc-standard-names*)
		  (not (member frame-name
			       ok-back:*kif-meta-extension-symbols*)))
	     (find-or-create-frame-handle frame-name frame-name kb t)
	     (progn
	       (when (not (member nil (internal-get-behavior-values
				       :frame-names-required kb)))
		 (continuable-assert
		  (not (coercible-to-frame-p-internal frame-name kb nil)) nil
		  "There is already a frame called ~S" frame-name))
	       (let ((h (create-frame-handle
			 (or frame-handle *undefined-value*) kb)))
		 (when frame-name
		   (setf (getf (frame-handle-plist h) :allocated-name)
			 frame-name))
		 (when frame-type
		   (setf (getf (frame-handle-plist h) :allocated-type)
			 frame-type))
		 h))
	     #+ignore
	     (find-or-create-frame-handle
	      frame-handle frame-handle kb t))))
    (when (eq (frame-handle-thing handle) *undefined-value*)
      (setf (frame-handle-thing handle) handle))
    (let ((internal-relation
	   (rest (assoc frame-name *tuplekb-translation-alist*))))
      (when internal-relation
	;;(let ((*print-readably* nil)) (print (list handle internal-relation)))
	(setf (getf (frame-handle-plist handle) :internal-relation)
	      internal-relation)))
    handle))

(defmethods decontextualize-internal
    ((value t) (from-context t) (kb (structure-tuple-kb tuple-kb)))
  (decontextualize-aux value from-context kb))

(defmethod ok-back:decontextualize-aux
    (value (from-context t) (kb t))
  value)

(defmethod decontextualize-aux
    ((value frame-handle) (from-context (eql :slot))
     (kb t))
  (multiple-value-bind (frame? found-p)
      (coerce-to-frame-internal value kb nil nil)
    (if found-p
	(let ((name (get-frame-name-internal frame? kb nil)))
	  (or (first (member name *okbc-standard-slot-names*))
	      value))
	value)))

(defmethod decontextualize-aux
    ((value frame-handle) (from-context (eql :facet))
     (kb t))
  (multiple-value-bind (frame? found-p)
      (coerce-to-frame-internal value kb nil nil)
    (if found-p
	(let ((name (get-frame-name-internal frame? kb nil)))
	  (or (first (member name *okbc-standard-facet-names*))
	      value))
	value)))

(defmethod decontextualize-aux
    ((value frame-handle) (from-context (eql :frame))
     (kb t))
  (multiple-value-bind (frame? found-p)
      (coerce-to-frame-internal value kb nil nil)
    (if found-p
	(let ((name (get-frame-name-internal frame? kb nil)))
	  (or (first (member name *okbc-standard-names*))
	      value))
	value)))

(defmethod decontextualize-aux ((value cons) (from-context t) (kb t))
  (if (loop with remaining = value
	    while (consp remaining)
	    do (pop remaining)
	    when (not (consp remaining))
	    return (null remaining))
      ;; The list is not dotted.
      (loop while value
	    nconc
	    (let ((car (pop value)))
	      (if (listp value)
		  (list (decontextualize-aux car from-context kb))
		  (cons (decontextualize-aux car from-context kb)
			(decontextualize-aux
			 (prog1 value (setq value nil)) from-context kb)))))
      (intern-remote-value value)))

(defmethods get-direct-own-slot-values-in-detail 
  (frame slot (kb (structure-tuple-kb tuple-kb)) number-of-values
	 (value-selector (eql :either)) kb-local-only-p)
  (get-direct-own-slot-values-in-detail 
   frame slot kb number-of-values :known-true kb-local-only-p))

(defmethods get-direct-template-slot-values-in-detail 
  (frame slot (kb (structure-tuple-kb tuple-kb)) number-of-values 
	 (value-selector (eql :either)) kb-local-only-p)
  (multiple-value-bind 
   (values exact-p more-status)
   (get-direct-template-slot-values-in-detail 
    frame slot kb number-of-values :known-true kb-local-only-p)
   (if values
       (values values exact-p more-status nil)
     (get-direct-template-slot-values-in-detail 
      frame slot kb number-of-values :default-only kb-local-only-p))))

(defmethods get-slot-values-in-detail-internal
    ((frame t) (slot t) (kb (structure-tuple-kb tuple-kb))
     (inference-level (eql :direct))
     (slot-type t) (number-of-values t) (value-selector t)
     (kb-local-only-p t))
  (let ((frame (or (coerce-to-frame-internal frame kb nil
					     kb-local-only-p) frame))
	(slot  (or (coerce-to-frame-internal slot kb nil
					     kb-local-only-p)  slot)))
    (continuable-assert
     frame not-coercible-to-frame :frame frame :kb kb :error-message
     "Cannot have a null frame")
    (continuable-assert
     slot slot-not-found :frame frame :slot slot :kb kb :slot-type slot-type
     :error-message "Cannot have a null slot")
    (continuable-assert (member slot-type '(:own :template)))
    (if (eq slot-type :own)
	(get-direct-own-slot-values-in-detail 
	 frame slot kb number-of-values value-selector
	 kb-local-only-p)
      (get-direct-template-slot-values-in-detail
       frame slot kb number-of-values value-selector kb-local-only-p))))


(defmethods get-direct-template-facet-values-in-detail
  (frame slot facet (kb (structure-tuple-kb tuple-kb)) number-of-values
         (value-selector (eql :either)) kb-local-only-p)
  (multiple-value-bind
   (values exact-p more-status)
   (get-direct-template-facet-values-in-detail
    frame slot facet kb number-of-values :known-true kb-local-only-p)
   (if values
       (values values exact-p more-status nil)
     (get-direct-template-facet-values-in-detail
      frame slot facet kb number-of-values :default-only kb-local-only-p))))

(defmethods get-direct-own-facet-values-in-detail
  (frame slot facet (kb (structure-tuple-kb tuple-kb)) number-of-values
         (value-selector (eql :either)) kb-local-only-p)
  (get-direct-own-facet-values-in-detail
   frame slot facet kb number-of-values :known-true kb-local-only-p))


;;; This runs only for inference-level because of the NIL EQL specialised
;;; method in the default-inheritance mixin.
(defmethods get-facet-values-in-detail-internal
    ((frame t) (slot t) (facet t) (kb (structure-tuple-kb tuple-kb))
     (inference-level t) (slot-type t) (number-of-values t) (value-selector t)
     (kb-local-only-p t))
  (let ((frame (or (coerce-to-frame-internal
		    frame kb nil kb-local-only-p) frame))
	(slot  (or (coerce-to-frame-internal
		    slot kb nil kb-local-only-p)  slot))
	(facet (or (coerce-to-frame-internal
		    facet kb nil kb-local-only-p) facet)))
    (continuable-assert
     frame not-coercible-to-frame :frame frame :kb kb :error-message
     "Cannot have a null frame")
    (continuable-assert
     slot slot-not-found :frame frame :slot slot :kb kb :slot-type slot-type
     :error-message "Cannot have a null slot")
    (continuable-assert
     facet facet-not-found :frame frame :slot slot :facet facet
     :kb kb :error-message "Cannot have a null facet")
    (continuable-assert
     (not (member facet *tuplekb-internal-facetlike-relations*))
     facet-not-found :frame frame :slot slot :facet facet
     :kb kb :error-message
     (format nil "Cannot have a facet called ~S" facet))
    (continuable-assert (member slot-type '(:own :template)))
    (ecase slot-type
      (:own
       (get-direct-own-facet-values-in-detail
	frame slot facet kb number-of-values
	value-selector kb-local-only-p))
      (:template
       (get-direct-template-facet-values-in-detail
	frame slot facet kb number-of-values
	value-selector kb-local-only-p)))))

(defmethods get-kb-direct-parents-internal ((kb (structure-tuple-kb tuple-kb)))
  (tuple-kb-parent-kbs kb))

;; This is factored out to allow us to use a tuple kb as a meta-kb
(defmethods get-class-instances-internal
    ((class t) (kb (structure-tuple-kb tuple-kb))
     (inference-level (eql :direct))
     (number-of-values t) (kb-local-only-p t))
  (get-class-instances-internal-implementation
   class kb t number-of-values kb-local-only-p))

(defmethods get-kb-behaviors-internal ((kb-type-or-kb tuple-kb) (connection t))
  (cons :permission (mapcar #'first *tuplekb-supported-behaviors*)))

(defmethods get-behavior-supported-values-internal
    ((behavior (eql :permission)) (kb (structure-tuple-kb tuple-kb)))
  '(:read :write :add))

(defmethods get-behavior-supported-values-internal
    ((behavior t) (kb (structure-tuple-kb tuple-kb)))
  (rest (rest (assoc behavior *tuplekb-supported-behaviors*))))

(defmethods internal-get-behavior-values
 ((behavior t) (kb (structure-tuple-kb tuple-kb)))
 ;; Circumvent cache!
  (if (eq :permission behavior)
      (if (read-only-p kb)
	  '(:read)
	  '(:read :add :delete))
      (rest (assoc behavior (current-behaviors kb) :test #'eq))))

(defmethods get-behavior-values-internal
    ((behavior t) (kb (structure-tuple-kb tuple-kb)))
  (internal-get-behavior-values behavior kb))

(defmethods put-behavior-values-internal :before
    ((behavior (eql :constraint-checking-time)) (values t)
     (kb (structure-tuple-kb tuple-kb)))
  (continuable-assert
   (= (length values) 1)
   illegal-behavior-values :behavior behavior :proposed-values values))

(defmethods put-behavior-values-internal
    ((behavior t) (values t) (kb (structure-tuple-kb tuple-kb)))
  (let ((entry (assoc behavior *tuplekb-supported-behaviors*)))
    (continuable-assert
     (and entry (second entry))
     illegal-behavior-values
     :behavior behavior
     :proposed-values values))
  (setf (current-behaviors kb)
	(cons (cons behavior values)
	      (remove (assoc behavior (current-behaviors kb))
		      (current-behaviors kb)))))

(defmethods remove-slot-value-internal
    (frame slot value (kb (structure-tuple-kb tuple-kb)) (test t)
	   (slot-type t) (index t)
	 (value-selector (eql :default-only)) (kb-local-only-p t))
  (let ((values (get-slot-values-internal frame slot kb :direct slot-type :all
					  value-selector kb-local-only-p))
	(testfn (decanonicalize-testfn test kb kb-local-only-p)))
    (if (member value values :test testfn)
	(put-slot-values-internal
	 frame slot (remove value values :test testfn)
	 kb slot-type value-selector kb-local-only-p)
      (if (get-slot-values-internal frame slot kb :all-inferable slot-type :all
				    value-selector kb-local-only-p)
	  ;; We don't have the value locally, but we can inherit it, so block.
	  (put-slot-values-internal
	   frame slot '(__deleted) kb slot-type value-selector kb-local-only-p)
	  ;; The value isn't there anywhere, so ignore it.
	  nil))))

(defmethods remove-facet-value-internal
    (frame slot facet value (kb (structure-tuple-kb tuple-kb)) (test t)
	   (slot-type t)
	 (value-selector (eql :default-only)) (kb-local-only-p t))
  (let ((values (get-facet-values-internal
		 frame slot facet kb :direct slot-type :all value-selector
		 kb-local-only-p))
	(testfn (decanonicalize-testfn test kb kb-local-only-p)))
    (if (member value values :test testfn)
	(put-facet-values-internal frame slot facet
				   (remove value values :test testfn)
				   kb slot-type value-selector
				   kb-local-only-p)
        (if (get-facet-values-internal frame slot facet kb :all-inferable
				       slot-type :all value-selector
				       kb-local-only-p)
	    ;; We don't have the value locally, but we can inherit it, so block
	    (put-facet-values-internal
	     frame slot facet '(__deleted) kb slot-type value-selector 
	     kb-local-only-p)
            ;; The value isn't there anywhere, so ignore it.
            nil))))

(defmethods create-individual-internal
    ((name t) (kb (structure-tuple-kb tuple-kb)) (direct-types t) (doc t)
     (own-slots t) (own-facets t) (handle t) (pretty-name t)
     (kb-local-only-p t))
  (create-reified-non-class
   name :individual direct-types kb doc own-slots own-facets handle
   pretty-name kb-local-only-p))

(defmethods get-frames-with-slot-value-internal
    (slot value (kb (structure-tuple-kb tuple-kb))
	  (inference-level (eql :direct))
	  (slot-type t) (value-selector t) (kb-local-only-p t))
  (let ((slot (or (coerce-to-slot-internal slot kb nil kb-local-only-p) slot)))
  (ecase slot-type
    (:own (ecase value-selector
	    (:known-true
	     (multiple-value-bind 
		   (res more)
		 (tuple-store-fetchm `(,slot ?frame ,value)
				     (tuple-kb-tuple-store kb)
				     :return-pattern '?frame
				     :index-hint 1
				     :check-included-kbs-p
				     (check-included-kbs-p kb kb-local-only-p)
				     :max-matches nil
				     :test (compile-pattern
					    `(,slot ?frame ,value)
					    :comparator-alist ((slot eq))))
	       (values res t (if more :more nil))))
	    (:default-only
		(multiple-value-bind 
		      (res more)
		    (tuple-store-fetchm
		     `(__default-slot-value ,slot ?frame ,value)
		     (tuple-kb-tuple-store kb)
		     :return-pattern '?frame
		     :index-hint 1
		     :check-included-kbs-p
		     (check-included-kbs-p kb kb-local-only-p)
		     :max-matches nil
		     :test (compile-pattern
			    `(__default-slot-value
			      ,slot ?frame ,value)
			    :comparator-alist ((slot eq))))
		  (values res t (if more :more nil))))
	    (:either (multiple-value-bind (res1 exact-p1 more1)
			 (get-frames-with-slot-value-internal
			  slot value kb inference-level slot-type
			  :known-true kb-local-only-p)
		       (multiple-value-bind (res2 exact-p2 more2)
			   (get-frames-with-slot-value-internal
			    slot value kb inference-level slot-type
			    :default-only kb-local-only-p)
			 (values (remove-duplicates (append res1 res2))
				 (and exact-p1 exact-p2)
				 (or more1 more2)))))))
    (:template
     (ecase value-selector
       (:known-true
	(multiple-value-bind 
	      (res more)
	    (tuple-store-fetchm `(__template-slot-value ,slot ?frame ,value)
				(tuple-kb-tuple-store kb)
				:return-pattern '?frame
				:index-hint 1
				:check-included-kbs-p
				(check-included-kbs-p kb kb-local-only-p)
				:max-matches nil
				:test (compile-pattern
				       `(__template-slot-value
					 ,slot ?frame ,value)
				       :comparator-alist ((slot eq))))
	  (values res t (if more :more nil))))
       (:default-only
	   (multiple-value-bind 
		 (res more)
	       (tuple-store-fetchm `(__default-template-slot-value
				     ,slot ?frame ,value)
				   (tuple-kb-tuple-store kb)
				   :return-pattern '?frame
				   :index-hint 1
				   :check-included-kbs-p
				   (check-included-kbs-p kb kb-local-only-p)
				   :max-matches nil
				   :test (compile-pattern
					  `(__default-template-slot-value
					    ,slot ?frame ,value)
					  :comparator-alist ((slot eq))))
	     (values res t (if more :more nil))))
       (:either (multiple-value-bind (res1 exact-p1 more1)
		    (get-frames-with-slot-value-internal
		     slot value kb inference-level slot-type
		     :known-true kb-local-only-p)
		  (multiple-value-bind (res2 exact-p2 more2)
		      (get-frames-with-slot-value-internal
		       slot value kb inference-level slot-type
		       :default-only kb-local-only-p)
		    (values (remove-duplicates (append res1 res2))
			    (and exact-p1 exact-p2)
			    (or more1 more2))))))))))

(defmethods get-frames-with-slot-value-internal
    (slot value (kb (structure-tuple-kb tuple-kb))
	  (inference-level (eql :direct))
	  (slot-type (eql :all)) (value-selector t) (kb-local-only-p t))
  (multiple-value-bind (own own-exact-p)
      (get-frames-with-slot-value-internal
	  slot value kb inference-level :own value-selector
	  kb-local-only-p)
    (multiple-value-bind (template template-exact-p)
	(get-frames-with-slot-value-internal
	    slot value kb inference-level :template value-selector
	    kb-local-only-p)
      (values (append own template) (and own-exact-p template-exact-p)))))

(defmethods get-frames-with-facet-value-internal
    (slot facet value (kb (structure-tuple-kb tuple-kb))
	  (inference-level (eql :direct))
	  (slot-type t) (value-selector t) (kb-local-only-p t))
  (let ((slot (or (coerce-to-slot-internal slot kb nil kb-local-only-p) slot))
	(facet (or (coerce-to-facet-internal facet kb nil kb-local-only-p)
		   facet)))
  (ecase slot-type
    (:own (ecase value-selector
	    (:known-true
	     (multiple-value-bind 
		   (res more)
		 (tuple-store-fetchm `(,facet ,slot ?frame ,value)
				     (tuple-kb-tuple-store kb)
				     :return-pattern '?frame
				     :index-hint 1
				     :check-included-kbs-p
				     (check-included-kbs-p kb kb-local-only-p)
				     :max-matches nil
				     :test (compile-pattern
					    `(,facet ,slot ?frame ,value)
					    :comparator-alist ((slot eq)
							       (facet eq))))
	       (values res t (if more :more nil))))
	    (:default-only
		(multiple-value-bind 
		      (res more)
		    (tuple-store-fetchm
		     `(__default-facet-value ,facet ,slot ?frame ,value)
		     (tuple-kb-tuple-store kb)
		     :return-pattern '?frame
		     :index-hint 1
		     :check-included-kbs-p
		     (check-included-kbs-p kb kb-local-only-p)
		     :max-matches nil
		     :test (compile-pattern
			    `(__default-facet-value
			      ,facet ,slot ?frame ,value)
			    :comparator-alist ((slot eq)
					       (facet eq))))
		  (values res t (if more :more nil))))
	    (:either (multiple-value-bind (res1 exact-p1 more1)
			 (get-frames-with-facet-value-internal
			  slot facet value kb inference-level slot-type
			  :known-true kb-local-only-p)
		       (multiple-value-bind (res2 exact-p2 more2)
			   (get-frames-with-facet-value-internal
			    slot facet value kb inference-level slot-type
			    :default-only kb-local-only-p)
			 (values (remove-duplicates (append res1 res2))
				 (and exact-p1 exact-p2)
				 (or more1 more2)))))))
    (:template
     (ecase value-selector
       (:known-true
	(multiple-value-bind 
	      (res more)
	    (tuple-store-fetchm `(__template-facet-value
				  ,facet ,slot ?frame ,value)
				(tuple-kb-tuple-store kb)
				:return-pattern '?frame
				:index-hint 1
				:check-included-kbs-p
				(check-included-kbs-p kb kb-local-only-p)
				:max-matches nil
				:test (compile-pattern
				       `(__template-facet-value
					 ,facet ,slot ?frame ,value)
				       :comparator-alist ((slot eq)
							  (facet eq))))
	  (values res t (if more :more nil))))
       (:default-only
	   (multiple-value-bind 
		 (res more)
	       (tuple-store-fetchm `(__default-template-facet-value
				     ,facet ,slot ?frame ,value)
				   (tuple-kb-tuple-store kb)
				   :return-pattern '?frame
				   :index-hint 1
				   :check-included-kbs-p
				   (check-included-kbs-p kb kb-local-only-p)
				   :max-matches nil
				   :test (compile-pattern
					  `(__default-template-facet-value
					    ,facet ,slot ?frame ,value)
					  :comparator-alist ((slot eq)
							     (facet eq))))
	     (values res t (if more :more nil))))
       (:either (multiple-value-bind (res1 exact-p1 more1)
		    (get-frames-with-facet-value-internal
		     slot facet value kb inference-level slot-type
		     :known-true kb-local-only-p)
		  (multiple-value-bind (res2 exact-p2 more2)
		      (get-frames-with-facet-value-internal
		       slot facet value kb inference-level slot-type
		       :default-only kb-local-only-p)
		    (values (remove-duplicates (append res1 res2))
			    (and exact-p1 exact-p2)
			    (or more1 more2))))))))))

(defmethods get-frames-with-facet-value-internal
    (slot facet value (kb (structure-tuple-kb tuple-kb))
	  (inference-level (eql :direct))
	  (slot-type (eql :all)) (value-selector t) (kb-local-only-p t))
  (multiple-value-bind (own own-exact-p)
      (get-frames-with-facet-value-internal
       slot facet value kb inference-level :own
       value-selector kb-local-only-p)
    (multiple-value-bind (template template-exact-p)
	(get-frames-with-facet-value-internal
	 slot facet value kb inference-level :template value-selector
	 kb-local-only-p)
      (values (append own template)
	      (and own-exact-p template-exact-p)))))

(defun direct-coercible-to-frame-p (frame-name kb kb-local-only-p)
  (let ((hit? (get-simple-frame-with-slot-value
	       '__name frame-name kb kb-local-only-p)))
    (if hit?
	(values hit? t)
	(values nil nil))))

(defmethods ok-cache:register-side-effect
 ((kb (tuple-kb structure-tuple-kb)) &optional (arg nil))
  (when (eq (ok-cache:caching-policy kb) :agressive)
    (ok-cache:flush-cache kb))
  (call-next-method arg))

(defun initialize-tuple-kb-class (class-name kb)
  (setf (ok-cache:caching-policy kb) :agressive)
  (let ((supers
	 (rest
	  (or (assoc class-name *okbc-standard-class-direct-superclass-alist*)
	      (assoc :otherwise
		     *okbc-standard-class-direct-superclass-alist*)))))
    (let ((real-supers
	   (loop for super in supers
		 when (member super *okbc-standard-class-names*)
		 collect (progn (initialize-tuple-kb-class super kb)
				(direct-coercible-to-frame-p
				 super kb nil)))))
      (let ((frame (direct-coercible-to-frame-p class-name kb nil)))
	(if frame
	    ;; Do the internal sort of check to avoid recursion from
	    ;; coerce-to-frame!
	    ;; But still make sure it's a full first-class citizen...
	    (progn (initialize-bootstrap-class class-name frame kb real-supers
					       nil)
		   :already-exists)
	    (create-bootstrap-class class-name kb real-supers nil))))))

(defun initialize-tuple--kb (kb)
  (setf (tuple-store-kb (tuple-kb-tuple-store kb)) kb)
  (when (or (not (parent-kbs kb))
	    (loop for k in (parent-kbs kb)
		  always (not (get-simple-frame-with-slot-value
			       '__name :thing k t))))
    (loop for class-name in *okbc-class-relation-symbols*
	  do (initialize-tuple-kb-class class-name kb))
    (loop for class-name in *okbc-standard-class-names*
	  do (initialize-tuple-kb-class class-name kb))
    ;; Now fix up :class so that it's a class and a thing.
    (let ((class_frame (class-frame kb nil))
	  (frame_frame (frame-frame kb nil))
	  (thing_frame (get-simple-frame-with-slot-value
			'__name :thing kb nil)))
      (let ((fact `(__instance-of ,class_frame ,class_frame)))
	(insert fact (tuple-kb-tuple-store kb) t))
      (let ((fact `(__instance-of ,class_frame ,thing_frame)))
	(insert fact (tuple-kb-tuple-store kb) t))
      (let ((fact `(__instance-of ,class_frame ,frame_frame)))
	(insert fact (tuple-kb-tuple-store kb) t))

      (let ((fact `(__instance-of ,frame_frame ,class_frame)))
	(insert fact (tuple-kb-tuple-store kb) t))
      (let ((fact `(__instance-of ,frame_frame ,frame_frame)))
	(insert fact (tuple-kb-tuple-store kb) t))
      (let ((fact `(__instance-of ,frame_frame ,thing_frame)))
	(insert fact (tuple-kb-tuple-store kb) t))
    
      (let ((fact `(__instance-of ,thing_frame ,thing_frame)))
	(insert fact (tuple-kb-tuple-store kb) t))
      (let ((fact `(__instance-of ,thing_frame ,class_frame)))
	(insert fact (tuple-kb-tuple-store kb) t))
      (let ((fact `(__instance-of ,thing_frame ,frame_frame)))
	(insert fact (tuple-kb-tuple-store kb) t)))
    (loop with frame_frame = (frame-frame kb nil)
	  for name in (append *okbc-class-relation-symbols*
			      *okbc-standard-class-names*)
	  for frame = (get-simple-frame-with-slot-value '__name name kb nil)
	  do (insert `(__instance-of ,frame ,frame_frame)
		     (tuple-kb-tuple-store kb) t))
    (loop for slot-name in *okbc-standard-slot-names*
	  when (not (direct-coercible-to-frame-p slot-name kb nil))
	  do (create-reified-standard-non-class slot-name :slot kb nil))
    (loop for facet-name in *okbc-standard-facet-names*
	  when (not (direct-coercible-to-frame-p facet-name kb nil))
	  do (create-reified-standard-non-class facet-name :facet kb nil))))

(define-default-inheritance-methods
    (ok-back:get-frames-with-slot-value-internal-direct
     ok-back:get-frames-with-facet-value-internal-direct)
  tuple-kb
  structure-tuple-kb)

(defun initialize-tuple-kb-tuple-store (instance indexing-type)
  (ecase indexing-type
    (:hash-index
     (setf (tuple-store instance) (tuple-store::create-tuple-store t nil)))
    (:full-index
     (setf (tuple-store instance) (tuple-store::create-tuple-store nil t)))
    (:no-index
     (setf (tuple-store instance)
	   (tuple-store::create-tuple-store nil nil)))))

(defmethod shared-initialize :after
  ((instance tuple-kb) (slot-names t) &rest args &key
   (indexing-type *default-tuple-kb-indexing-type*)
   (cache-p t cache-p-supplied-p)
   (frame-names-required nil fnr-supplied-p))
  (declare (ignore args))
  (when (not (eq instance (clos:class-prototype (class-of instance))))
    (when (not (packagep (io-package instance)))
      (let ((package (if (packagep (io-package instance))
			 (io-package instance)
			 (find-package (io-package instance)))))
	(setf (io-package instance) package)))
    (when fnr-supplied-p
      (put-behavior-values-internal
       :frame-names-required (list frame-names-required) instance))
    (when cache-p-supplied-p
      (setf (ok-cache:allow-caching-p instance) cache-p))
    (initialize-tuple-kb-tuple-store instance indexing-type)
    (initialize-tuple--kb instance)))

(defun ok-back:make-structure-tuple-kb (&rest args)
  "Creates and initializes a <code>structure-tuple-kb</code> instance.  This is
   analogous to <code>make-instance</code> on <code>tuple-kb</code>."
  (let ((instance (apply 'construct-structure-tuple-kb
			 (loop for (key value) on args by #'cddr
			       when (not (eq key :indexing-type))
			       append (list key value)))))
    (let ((indexing-type
	   (getf args :indexing-type *default-tuple-kb-indexing-type*)))
      (initialize-tuple-kb-tuple-store instance indexing-type)
      (initialize-tuple--kb instance)
      instance)))

(defmethod get-user-roots ((class t) (kb t) (kb-local-only-p t))
  (let ((frame (coerce-to-frame-internal class kb nil kb-local-only-p)))
    (let ((name (and frame
		     (get-frame-name-internal frame kb kb-local-only-p))))
      (if (and (member name *okbc-standard-names*)
	       (not (member name ok-back:*kif-meta-extension-symbols*)))
	  (loop for sub in (get-class-subclasses-internal frame kb :direct
							  :all kb-local-only-p)
		append (get-user-roots sub kb kb-local-only-p))
	  (list frame)))))

(defmethods get-kb-roots-internal
    ((kb (tuple-kb structure-tuple-kb)) (selector (eql :user))
     (kb-local-only-p t))
  (let ((classes (call-next-method)))
    (remove-duplicates
     (loop for class in classes
	   append (get-user-roots class kb kb-local-only-p)))))


(defmethod allocate-all-symbol-stash-indices ((facts t) (kb t))
  (allocate-symbol-stash-indices ok-back:*okbc-standard-names*)
  (allocate-symbol-stash-indices facts))

(defun save-sentential-kb (kb facts pathname)
  (implement-with-kb-io-syntax-internal
   #'(lambda ()
       (with-open-file (stream pathname
			 :direction :output)
	 (let ((stream (underlying-stream stream :output))
	       (*symbol-stash-counter* -1)
	       (*symbol-stash-table* (make-hash-table :test #'eq)))
	   (declare (special *symbol-stash-counter* *symbol-stash-table*))
	   (prin1 (name kb) stream)
	   (print (unique-id kb) stream)
	   (print (current-behaviors kb) stream)
	   (allocate-all-symbol-stash-indices facts kb)	   
	   ;; Now print out the package table.
	   (let ((packages nil))
	     (maphash #'(lambda (k v)
			  (declare (ignore v))
			  (let ((p (symbol-package k)))
			    (when (and (not (eq *keyword-package* p))
				       (not (eq *okbc-package* p)))
			      (let ((entry (or (assoc p packages)
					       (let ((new (list p nil)))
						 (push new packages)
						 new))))
				(multiple-value-bind (sym flag)
				  (find-symbol k p)
				  (declare (ignore sym))
				  (when (eq :external flag)
				    (push (symbol-name k)
					  (second entry))))))))
		      *symbol-stash-table*)
	     (fast-terpri stream)
	     (fast-write-string "(" stream)
	     (loop for (p syms) in packages
		   for first-p = t then nil
		   when (not first-p)
		   do (fast-terpri stream)
		   (fast-write-string " " stream)
		   do (prin1 (package-name p) stream)
		   (fast-write-string " " stream)
		   (prin1 syms stream))
	     (fast-write-string ")" stream))
	   (fast-terpri stream)
	   (fast-write-string "(" stream)
	   (let ((first-p t))
	     (maphash #'(lambda (k v)
			  (when (not first-p)
			    (fast-terpri stream)
			    (fast-write-string " " stream))
			  (setq first-p nil)
			  (prin1 k stream)
			  (fast-write-string " " stream)
			  (fast-write-fixnum v stream))
		      *symbol-stash-table*))
	   (fast-write-string ")" stream)
	   (loop for fact in facts
		 for count from 0
		 do (fast-terpri stream)
		 (cond ((= (mod count 5000) 4999)
			(fast-write-string "+" *standard-output*)
			(fast-terpri *standard-output*))
		       ((= (mod count 100) 99)
			(fast-write-string "." *standard-output*))
		       (t nil))
		 (print-fact fact kb stream)))))
   kb :file t))

(defmethods ok-back:print-abstract-handle-for-kb
 ((thing frame-handle) (kb (tuple-kb structure-tuple-kb)) (stream t))
  (declare (special *print-pretty-frame-handles*))
 (if *print-pretty-frame-handles*
     (format stream "[~A]" (get-frame-pretty-name-internal thing kb nil))
     (call-next-method)))

;;; START OF SUBSTITUTION GROUP !!!!!!!!!!!!
(with-substitution-groups ((("STRUCTURE-TUPLE-KB" "TUPLE-KB")))

;==============================================================================

;;; Now actually define the OKBC binding.

(defmethod frame-frame ((kb tuple-kb) kb-local-only-p)
 (or (if kb-local-only-p
	 (or (tuple-kb-cache-of-frame-frame-local kb)
	     (setf (tuple-kb-cache-of-frame-frame-local kb)
		   (get-simple-frame-with-slot-value
		    '__name :frame kb kb-local-only-p)))
	 (or (tuple-kb-cache-of-frame-frame-global kb)
	     (setf (tuple-kb-cache-of-frame-frame-global kb)
		   (get-simple-frame-with-slot-value
		    '__name :frame kb kb-local-only-p))))
     (progn (initialize-tuple--kb kb)
	    (frame-frame kb kb-local-only-p))))

(defmethod class-frame ((kb tuple-kb) kb-local-only-p)
 (or (if kb-local-only-p
	 (or (tuple-kb-cache-of-class-frame-local kb)
	     (setf (tuple-kb-cache-of-class-frame-local kb)
		   (get-simple-frame-with-slot-value
		    '__name :class kb kb-local-only-p)))
	 (or (tuple-kb-cache-of-class-frame-global kb)
	     (setf (tuple-kb-cache-of-class-frame-global kb)
		   (get-simple-frame-with-slot-value
		    '__name :class kb kb-local-only-p))))
     (progn (initialize-tuple--kb kb)
	    (class-frame kb kb-local-only-p))))

(defmethod slot-frame ((kb tuple-kb) kb-local-only-p)
 (or (if kb-local-only-p
	 (or (tuple-kb-cache-of-slot-frame-local kb)
	     (setf (tuple-kb-cache-of-slot-frame-local kb)
		   (get-simple-frame-with-slot-value
		    '__name :slot kb kb-local-only-p)))
	 (or (tuple-kb-cache-of-slot-frame-global kb)
	     (setf (tuple-kb-cache-of-slot-frame-global kb)
		   (get-simple-frame-with-slot-value
		    '__name :slot kb kb-local-only-p))))
     (progn (initialize-tuple--kb kb)
	    (slot-frame kb kb-local-only-p))))

(defmethod facet-frame ((kb tuple-kb) kb-local-only-p)
 (or (if kb-local-only-p
	 (or (tuple-kb-cache-of-facet-frame-local kb)
	     (setf (tuple-kb-cache-of-facet-frame-local kb)
		   (get-simple-frame-with-slot-value
		    '__name :facet kb kb-local-only-p)))
	 (or (tuple-kb-cache-of-facet-frame-global kb)
	     (setf (tuple-kb-cache-of-facet-frame-global kb)
		   (get-simple-frame-with-slot-value
		    '__name :facet kb kb-local-only-p))))
     (progn (initialize-tuple--kb kb)
	    (facet-frame kb kb-local-only-p))))

(defmethod individual-frame ((kb tuple-kb) kb-local-only-p)
 (or (if kb-local-only-p
	 (or (tuple-kb-cache-of-individual-frame-local kb)
	     (setf (tuple-kb-cache-of-individual-frame-local kb)
		   (get-simple-frame-with-slot-value
		    '__name :individual kb kb-local-only-p)))
	 (or (tuple-kb-cache-of-individual-frame-global kb)
	     (setf (tuple-kb-cache-of-individual-frame-global kb)
		   (get-simple-frame-with-slot-value
		    '__name :individual kb kb-local-only-p))))
     (progn (initialize-tuple--kb kb)
	    (individual-frame kb kb-local-only-p))))

(defmethod ok-cache:flush-cache ((instance tuple-kb))
  (setf (tuple-kb-cache-of-frame-frame-local  instance) nil)
  (setf (tuple-kb-cache-of-frame-frame-global instance) nil)
  (setf (tuple-kb-cache-of-class-frame-local  instance) nil)
  (setf (tuple-kb-cache-of-class-frame-global instance) nil)
  (setf (tuple-kb-cache-of-slot-frame-local   instance) nil)
  (setf (tuple-kb-cache-of-slot-frame-global  instance) nil)
  (setf (tuple-kb-cache-of-facet-frame-local  instance) nil)
  (setf (tuple-kb-cache-of-facet-frame-global instance) nil)
  (setf (tuple-kb-cache-of-individual-frame-local  instance) nil)
  (setf (tuple-kb-cache-of-individual-frame-global instance) nil)
  (call-next-method))

(defmethod coerce-to-frame-internal
    ((thing t) (kb tuple-kb) (error-p t) (kb-local-only-p t))
  (let ((facts-p (indexed-in-tuple-store-p thing (tuple-kb-tuple-store kb))))
    (if facts-p
	;; Don't call get-frame-name to avoid recursion.
	;; (if (get-simple-own-slot-value thing '__name kb kb-local-only-p)
	    ;; It's not really a frame unless it's got a name, otherwise
	    ;; it's a disembodied frame handle.
	(if (primitive-direct-instance-of-p
	     thing (frame-frame kb nil) kb kb-local-only-p)
	    ;; We now have a class explicitly denoting :frame-ness.
	    (values thing t)
	    (if error-p
		(error 'not-coercible-to-frame :frame thing :kb kb)
	        (values nil nil)))
	(if error-p
	    (error 'not-coercible-to-frame :frame thing :kb kb)
	    (values nil nil)))))

(defmethod handle-unhandled-sentence
    (sentence (kb tuple-kb) (frame t) (value-selector t) (kb-local-only-p t)
	      (key t))
  (let ((frame
	 (and frame (coerce-to-frame-internal frame kb t kb-local-only-p))))
    (ecase key
      (:tell (insert sentence (tuple-kb-tuple-store kb) t)
	     (when (and frame (not (is-in-tree frame sentence)))
	       (insert `(__has-sentence ,frame ',sentence)
		       (tuple-kb-tuple-store kb) t)))
      (:untell
       (if (eq (tuple-store-fetchm sentence (tuple-kb-tuple-store kb)
				   :check-included-kbs-p
				   (check-included-kbs-p kb kb-local-only-p))
	       :fail)
	   nil
	   (progn (drop sentence (tuple-kb-tuple-store kb) nil
			(check-included-kbs-p kb kb-local-only-p)) t)))
      (:tellable t))))

(defmethod handle-unhandled-query
    ((query t) target-query (kb tuple-kb) (inference-level t) (error-p t)
     (value-selector t) (kb-local-only-p t) (bindings t))
  (let ((vars (variables-in target-query)))
    (let ((results (tuple-store-fetchm (if (eq :holds (first target-query))
					   (rest target-query)
					   target-query)
				       (tuple-kb-tuple-store kb)
				       :return-pattern vars
				       :check-included-kbs-p
				       (check-included-kbs-p
					kb kb-local-only-p))))
      (if (eq :fail results)
	  (values :fail t)
	  (values (loop for result in results
			collect (append (mapcar #'cons vars result)
					bindings))
		  t)))))

(defmethod handle-simple-query
    ((query t) target-query (kb tuple-kb) (inference-level (eql :direct))
     (error-p t) (value-selector t) kb-local-only-p bindings)
  (if (and (or (tuple-store::tuple-store-hash-index-p
		(tuple-kb-tuple-store kb))
	       (tuple-store-full-index-p (tuple-kb-tuple-store kb)))
	   (let ((sym (first target-query)))
	     (or (and (not (symbolp sym))
		      (not (procedure-p sym)))
		 (and (symbolp sym)
		      (not (or (find sym *kif-operator-symbols*
				     :test #'string=)
			       (find sym *evaluable-predicate-symbols*
				     :test #'string=)
			       (find sym ok-back::*kif-meta-extension-symbols*
				     :test #'string=)))))))
      (let ((reformulated
	     (if (= (length target-query) 2)
		 ;; class/instance
		 `(:instance-of ,(second target-query) ,(first target-query))
		 (if (eq :holds (first target-query))
		     (rest target-query)
		     target-query))))
	(let ((names-required-p (not (member nil (internal-get-behavior-values
						  :frame-names-required kb)))))
	  (when names-required-p
	    (setq reformulated (coerce-to-kb-value-internal
				reformulated :value kb nil nil t
				:error-if-not-unique kb-local-only-p))))
	(let ((vars (variables-in target-query))
	      (pattern (sublis *tuplekb-translation-alist* reformulated)))
	  (let ((results (tuple-store-fetchm pattern (tuple-kb-tuple-store kb)
					     :return-pattern vars
					     :check-included-kbs-p
					     (check-included-kbs-p
					      kb kb-local-only-p))))
	  
	    (if (eq :fail results)
		(values :fail t)
		(let ((filtered
		       (loop for result in results
			     unless
			     (loop for x in result
				   thereis
				   (member
				    x *non-okbc-mapping-internal-relations*))
			     collect (append (mapcar #'cons vars result)
					     bindings))))
		  (if (or filtered (not results))
		      (values (sublis *tuplekb-backtranslation-alist* filtered)
			      t)
		      (values :fail t)))))))
      (call-next-method)))

(defmethod debug-facts (atom (kb tuple-kb))
  (facts-full-indexed-under (fast-hash-key atom) (tuple-kb-tuple-store kb)))

;==============================================================================
;; These trump the cache methods
(defmethods eql-in-kb-internal :around
  ((arg0 (number string)) (arg1 t) (kb tuple-kb) (kb-local-only-p t))
  (eql arg0 arg1))

(defmethods eql-in-kb-internal :around
  ((arg0 t) (arg1 (number string)) (kb tuple-kb) (kb-local-only-p t))
  (eql arg0 arg1))

(defmethods equal-in-kb-internal :around
  ((arg0 (number string)) (arg1 t) (kb tuple-kb) (kb-local-only-p t))
  (equal arg0 arg1))

(defmethods equal-in-kb-internal :around
  ((arg0 t) (arg1 (number string)) (kb tuple-kb) (kb-local-only-p t))
  (equal arg0 arg1))
;==============================================================================

(defmethod get-frame-sentences-internal
    ((frame t) (kb tuple-kb) (number-of-values t) (okbc-sentences-p t)
     (value-selector t) (kb-local-only-p t))
  (let ((frame (coerce-to-frame-internal frame kb t kb-local-only-p)))
    (let ((facts (facts-full-indexed-under (fast-hash-key frame)
					   (tuple-kb-tuple-store kb))))
      (let ((filtered-facts
	     (ecase value-selector
	       (:either
		(loop for fact in facts
		      for entry =
		      (second (assoc (first fact)
				     *tuplekb-defaulting-relations-alist*))
		      collect (if (eq '__has-sentence (first fact))
				  (dequote (third fact))
				  (if entry
				      (if (eq :none entry)
					  (rest fact)
					  (cons entry (rest fact)))
				      fact))))
	       (:default
		   (loop for fact in facts
			 for entry =
			 (second (assoc (first fact)
					*tuplekb-defaulting-relations-alist*))
			 when entry
			 collect (if (eq '__has-sentence (first fact))
				     (dequote (third fact))
				     (if entry
					 (if (eq :none entry)
					     (rest fact)
					     (cons entry (rest fact)))
					 fact))))
	       (:known-true
		(loop for fact in facts
		      for entry =
		      (assoc (first fact)
			     *tuplekb-defaulting-relations-alist*)
		      when (not entry)
		      collect (if (eq '__has-sentence (first fact))
				  (dequote (third fact))
				  fact))))))
	(let ((translated
	       (sublis *tuplekb-backtranslation-alist* filtered-facts)))
	  (values (if okbc-sentences-p
		      translated
		      (loop for s in translated
			    unless (okbc-sentence-p s)
			    collect s))
		  t))))))


(defmethod ok-back:load-okbc-kb-internal :around
   ((pathname t) (kb tuple-kb) (value-selector t) (kb-local-only-p t)
    (frame-handle-mapping-table t) (handle-to-name-mapping-table t)
    (delayed-sentences t) (action t) (sentence-action t) (language t)
    (substitute-OKBC-standard-names-p t))
 ;; Temporarily disable caching during bulk loading.  Things are
 ;; pathalogical otherwise.
   (let ((ok-cache:*allow-okbc-caching-p* nil)
	 (old-behavior-values (internal-get-behavior-values 
			       :constraint-checking-time kb)))
     (unwind-protect
	  (progn (put-behavior-values-internal 
		  :constraint-checking-time '(:never) kb)
		 (call-next-method))
       (put-behavior-values-internal
	:constraint-checking-time old-behavior-values kb)
       (ok-cache:register-side-effect kb :load-okbc-kb))))

		       
;;; This runs only for inference-level because of the NIL EQL specialised
;;; method in the default-inheritance mixin.

(defmethod get-simple-own-slot-value
  (frame slot (kb tuple-kb) kb-local-only-p)
  (let ((match? (fetch-one-bindingm `(,slot ,frame ?value)
				    (tuple-kb-tuple-store kb)
				    (compile-pattern
				     `(,slot ,frame ?value)
				     :comparator-alist ((slot eq)
							(frame eq)))
				    1 (check-included-kbs-p
				       kb kb-local-only-p))))
    (if (eq match? :fail)
	nil
        (rest (assoc '?value match?)))))

(defmethod get-simple-frame-with-slot-value
  (slot value (kb tuple-kb) kb-local-only-p)
  (let ((match? (fetch-one-bindingm `(,slot ?frame ,value)
				    (tuple-kb-tuple-store kb)
				    (compile-pattern
				     `(,slot ?frame ,value)
				     :comparator-alist ((slot eq)))
				    1 (check-included-kbs-p
				       kb kb-local-only-p))))
    (if (eq match? :fail)
	nil
        (rest (assoc '?frame match?)))))

(defmethod get-direct-own-slot-values-in-detail 
    (frame slot (kb tuple-kb) number-of-values
	   (value-selector (eql :known-true)) kb-local-only-p)
  (multiple-value-bind 
	(res more)
      (tuple-store-fetchm `(,slot ,frame ?value) (tuple-kb-tuple-store kb)
			  :return-pattern '?value
			  :index-hint 1
			  :check-included-kbs-p
			  (check-included-kbs-p kb kb-local-only-p)
			  :max-matches (if (eq number-of-values :all)
					   nil
					   number-of-values)
			  :test (compile-pattern
				 `(,slot ,frame ?value)
				 :comparator-alist ((slot eq)
						    (frame eq))))
    (values (loop for x in res
		  when (not (eq '__deleted x))
		  collect (list x t nil))
	    t
	    (if more :more nil)
	    nil)))

(defmethod get-direct-own-slot-values-in-detail 
  ((frame t) (slot t) (kb tuple-kb) (number-of-values t)
	 (value-selector (eql :default-only)) (kb-local-only-p t))
  (if (eq :fail (fetch-one-bindingm
		 `(__default-slot-value ,slot ,frame __deleted)
		 (tuple-kb-tuple-store kb)
		 (compile-pattern
		  `(__default-slot-value ,slot ,frame __deleted)
		  :comparator-alist
		  ((frame eq) (slot eq)))
		 1 (check-included-kbs-p kb kb-local-only-p)))
      (values nil t nil nil)
      (values nil t nil t)))

(defmethod get-direct-template-slot-values-in-detail 
  (frame slot (kb tuple-kb) number-of-values 
	 (value-selector (eql :known-true)) kb-local-only-p)
  (multiple-value-bind 
   (res more)
      (tuple-store-fetchm
       `(__template-slot-value ,slot ,frame ?value)
       (tuple-kb-tuple-store kb)
       :return-pattern '?value
       :index-hint 2
       :check-included-kbs-p (check-included-kbs-p kb kb-local-only-p)
       :max-matches (if (eq number-of-values :all)
			nil
			number-of-values)
       :test (compile-pattern
	      `(__template-slot-value ,slot ,frame ?value)
	      :comparator-alist ((slot eq)
				 (frame eq))))
   (values (loop for x in res collect (list x t nil))
	   t (if more :more nil) nil)))

(defmethod get-direct-template-slot-values-in-detail 
 (frame slot (kb tuple-kb) number-of-values 
	(value-selector (eql :default-only)) kb-local-only-p)
 (multiple-value-bind (res more)
   (tuple-store-fetchm
    `(__default-template-slot-value ,slot ,frame ?value)
    (tuple-kb-tuple-store kb)
    :return-pattern '?value
    :index-hint 2
    :check-included-kbs-p (check-included-kbs-p kb kb-local-only-p)
    :max-matches (if (eq number-of-values :all)
		     nil
		     number-of-values)
    :test (compile-pattern
	   `(__default-template-slot-value ,slot ,frame ?value)
	   :comparator-alist ((slot eq)
			      (frame eq))))
   (if res
       (if (rest res)
	   (generic-error "Internal consistency error - too many defaults: ~S"
			  res)
	   (if (eq (first res) '__deleted)
	       (values nil t nil t)
	       (values (list (list (first res) t t)) t nil t)))
       (values nil t (if more :more nil) nil))))

(defmethod get-direct-template-facet-values-in-detail
  (frame slot facet (kb tuple-kb) number-of-values
         (value-selector (eql :known-true)) kb-local-only-p)
  (multiple-value-bind 
   (res more)
   (tuple-store-fetchm
    `(__template-facet-value ,facet ,slot ,frame ?value)
    (tuple-kb-tuple-store kb)
    :return-pattern '?value
    :index-hint 3
    :max-matches (if (eq number-of-values :all)
		     nil
		     number-of-values)
    :check-included-kbs-p (check-included-kbs-p kb kb-local-only-p)
    :test (compile-pattern
	   `(__template-facet-value ,facet ,slot ,frame ?value)
	   :comparator-alist ((slot eq)
			      (facet eq)
			      (frame eq))))
   (values (loop for x in res collect (list x t nil))
	   t (if more :more nil) nil)))

(defmethod get-direct-template-facet-values-in-detail
    (frame slot facet (kb tuple-kb) number-of-values
	   (value-selector (eql :default-only)) kb-local-only-p)
  (multiple-value-bind 
	(res more)
      (tuple-store-fetchm
       `(__default-template-facet-value ,facet ,slot ,frame ?value)
       (tuple-kb-tuple-store kb)
       :index-hint 3
       :return-pattern '?value
       :max-matches (if (eq number-of-values :all)
			nil
			number-of-values)
       :check-included-kbs-p (check-included-kbs-p kb kb-local-only-p)
       :test (compile-pattern
	      `(__default-template-facet-value ,facet ,slot ,frame ?value)
	      :comparator-alist ((slot eq)
				 (facet eq)
				 (frame eq))))
    (if res
	(if (rest res)
	    (generic-error
	     "Internal consistency error - too many defaults: ~S" res)
	    (if (eq (first res) '__deleted)
		(values nil t nil t)
		(values (list (list (first res) t t)) t nil t)))
	(values nil t (if more :more nil) nil))))

(defmethod get-direct-own-facet-values-in-detail
    (frame slot facet (kb tuple-kb) number-of-values
	   (value-selector (eql :known-true)) kb-local-only-p)
  (multiple-value-bind
	(res more)
      (tuple-store-fetchm
       `(,facet ,slot ,frame ?value)
       (tuple-kb-tuple-store kb)
       :index-hint 2
       :max-matches (if (eq number-of-values :all) nil number-of-values)
       :return-pattern '?value
       :check-included-kbs-p (check-included-kbs-p kb kb-local-only-p)
       :test (compile-pattern
	      `(,facet ,slot ,frame ?value)
	      :comparator-alist ((slot eq)
				 (facet eq)
				 (frame eq))))
    (values (loop for x in res
		  when (not (eq '__deleted x))
		  collect (list x t nil))
	    t
	    (if more :more nil)
	    nil)))

(defmethod get-direct-own-facet-values-in-detail
  ((frame t) (slot t) (facet t) (kb tuple-kb) (number-of-values t)
         (value-selector (eql :default-only)) (kb-local-only-p t))
  (if (eq :fail (fetch-one-bindingm
		 `(__default-facet-value ,facet ,slot ,frame __deleted)
		 (tuple-kb-tuple-store kb)
		 (compile-pattern
		  `(__default-facet-value ,facet ,slot ,frame __deleted)
		  :comparator-alist
		  ((frame eq) (slot eq) (facet eq)))
		 2 (check-included-kbs-p kb kb-local-only-p)))
      (values nil t nil nil)
      (values nil t nil t)))

(defun tuple-kb-get-direct-types-from-tuples
    (instance kb number-of-values kb-local-only-p)
  (multiple-value-bind (results more-status)
      (tuple-store-fetchm
       `(__instance-of ,instance ?class)
       (tuple-kb-tuple-store kb)
       :return-pattern '?class
       :index-hint 1
       :check-included-kbs-p (check-included-kbs-p kb kb-local-only-p)
       :max-matches (if (eq number-of-values :all)
			nil
			number-of-values)
       :test (compile-pattern `(__instance-of ,instance ?class)
			      :comparator-alist
			      ((instance eq))))
    (values results (if more-status :more nil))))

(defmethod primitive-direct-instance-of-p
    (instance class (kb tuple-kb) (kb-local-only-p t))
  (let ((class (if (symbolp class)
		   (get-simple-frame-with-slot-value
		    '__name class kb kb-local-only-p)
		   class)))
    (not (eq :fail
	     (fetch-one-bindingm
	      `(__instance-of ,instance ,class) (tuple-kb-tuple-store kb)
	      (compile-pattern `(__instance-of ,instance ,class)
			       :comparator-alist
			       ((instance eq) (class eq)))
	      1 (check-included-kbs-p kb kb-local-only-p))))))

(defmethod instance-of-p-internal
    (thing class (kb tuple-kb) (inference-level (eql :direct))
	   (kb-local-only-p t))
  (let ((class (if (symbolp class)
		   (get-simple-frame-with-slot-value
		    '__name class kb kb-local-only-p)
		   class))
	(frame (or (coerce-to-frame-internal thing kb nil kb-local-only-p)
		   thing)))
    (not (eq :fail
	     (fetch-one-bindingm
	      `(__instance-of ,frame ,class) (tuple-kb-tuple-store kb)
	      (compile-pattern `(__instance-of ,frame ,class)
			       :comparator-alist
			       ((frame eq) (class eq)))
	      1 (check-included-kbs-p kb kb-local-only-p))))))

(defmethod get-instance-types-internal
    ((frame t) (kb tuple-kb) (inference-level (eql :direct))
     (number-of-values t) (kb-local-only-p t))
  (let ((frame (or (coerce-to-frame-internal
		       frame kb nil kb-local-only-p)
		      frame)))
    (continuable-assert
     frame not-coercible-to-frame :frame frame :kb kb :error-message
     "Cannot have a null instance frame")
    (values (or (tuple-kb-get-direct-types-from-tuples
		 frame kb number-of-values kb-local-only-p)
		(multiple-value-bind (class found-p)
		    (coerce-to-frame-internal :thing kb nil kb-local-only-p)
		  (if found-p
		      (list class)
		      nil)))
	    t)))

(defmethods ask-internal
    ((query t) (kb tuple-kb) (reply-pattern t) (inference-level t)
     (number-of-values t) (error-p t) (where t) (timeout t) (value-selector t)
     (kb-local-only-p t))
  (with-kbs-to-search (kb) (call-next-method)))

(defun tuple-kb-direct-member-slot-value-p-equal
    (frame slot value kb slot-type value-selector kb-local-only-p)
  (or (and (or (eq value-selector :either)
	       (eq value-selector :known-true))
	   (not (eq :fail
		    (ecase slot-type
		      (:own
		       (fetch-one-bindingm
			`(,slot ,frame ,value) (tuple-kb-tuple-store kb)
			(compile-pattern `(,slot ,frame ,value)
					 :comparator-alist
					 ((frame eq) (slot eq)
					  (value equal)))
			1 (check-included-kbs-p kb kb-local-only-p)))
		      (:template
		       (fetch-one-bindingm
			`(__template-slot-value ,slot ,frame ,value)
			(tuple-kb-tuple-store kb)
			(compile-pattern
			 `(__template-slot-value ,slot ,frame ,value)
			 :comparator-alist
			 ((frame eq) (slot eq) (value equal)))
			1 (check-included-kbs-p kb kb-local-only-p)))))))
      (and (or (eq value-selector :either)
	       (eq value-selector :default-only))
	   (not (eq :fail
		    (ecase slot-type
		      (:own
		       (fetch-one-bindingm
			`(__default-slot-value ,slot ,frame ,value)
			(tuple-kb-tuple-store kb)
			(compile-pattern
			 `(__default-slot-value ,slot ,frame ,value)
			 :comparator-alist
			 ((frame eq) (slot eq) (value equal)))
			1 (check-included-kbs-p kb kb-local-only-p)))
		      (:template
		       (fetch-one-bindingm
			`(__default-template-slot-value ,slot ,frame ,value)
			(tuple-kb-tuple-store kb)
			(compile-pattern
			 `(__default-template-slot-value ,slot ,frame ,value)
			 :comparator-alist
			 ((frame eq) (slot eq) (value equal)))
			1 (check-included-kbs-p kb kb-local-only-p)))))))))

(defmethods member-slot-value-p-internal
    ((frame frame-handle) (slot frame-handle) value (kb tuple-kb)
	   (inference-level (eql :direct))
	   (test (eql :equal)) (slot-type t)
	   (value-selector t)
	   (kb-local-only-p t))
  (if (consp value)
      (call-next-method)
      (let ((names-required-p
	     (not (member nil (internal-get-behavior-values
			       :frame-names-required kb)))))
	(if names-required-p
	    (or (tuple-kb-direct-member-slot-value-p-equal
		 frame slot value kb slot-type
		 value-selector kb-local-only-p)
		(typecase value
		  (null nil)	
		  (symbol
		   (let ((vframe (coerce-to-frame-internal
				  value kb t kb-local-only-p)))
		     (and vframe
			  (tuple-kb-direct-member-slot-value-p-equal
			   frame slot vframe kb slot-type
			   value-selector kb-local-only-p))))
		  (frame-handle
		   (let ((name (get-simple-own-slot-value
				value '__name kb kb-local-only-p)))
		     (and name
			  (tuple-kb-direct-member-slot-value-p-equal
			   frame slot name kb slot-type
			   value-selector kb-local-only-p))))
		  (otherwise nil)))
	    (tuple-kb-direct-member-slot-value-p-equal
	     frame slot value kb slot-type
	     value-selector kb-local-only-p)))))

(defmethod tuple-kb:get-class-instances-internal-implementation
    ((class t) (kb tuple-kb) (inference-level t) (number-of-values t)
     (kb-local-only-p t))
  (continuable-assert inference-level)
  (let ((class (or (coerce-to-frame-internal
		    class kb nil kb-local-only-p) class)))
    (continuable-assert
     class not-coercible-to-frame :frame class :kb kb :error-message
     "Cannot have a null class")
    (continuable-assert
     (not (member class '(__slot __facet __class __individual)))
     not-coercible-to-frame :frame class :kb kb :error-message
     (format nil "Cannot have a class called ~S" class))
    (multiple-value-bind (results more-status)
      (tuple-store-fetchm `(__instance-of ?instance ,class)
			  (tuple-kb-tuple-store kb)
			  :index-hint 1
			  :return-pattern '?instance
			  :check-included-kbs-p
			  (check-included-kbs-p kb kb-local-only-p)
			  :test (compile-pattern
				 `(__instance-of ?instance ,class)
				 :comparator-alist
				 ((class eq))))
      (values results t (if more-status :more nil)))))

(defmethod get-class-superclasses-internal
    ((class t) (kb tuple-kb) (inference-level (eql :direct))
     (number-of-values t) (kb-local-only-p t))
  (let ((class (or (coerce-to-frame-internal
		    class kb nil kb-local-only-p) class)))
    (continuable-assert
     class not-coercible-to-frame :frame class :kb kb :error-message
     "Cannot have a null class")
    (multiple-value-bind (results more-status)
      (tuple-store-fetchm `(__subclass-of ,class ?super)
			  (tuple-kb-tuple-store kb)
			  :index-hint 1
			  :return-pattern '?super
			  :check-included-kbs-p
			  (check-included-kbs-p kb kb-local-only-p)
			  :test
			  (compile-pattern `(__subclass-of ,class ?super)
					   :comparator-alist
					   ((class eq))))
      (values results t (if more-status :more nil)))))

(defmethod get-class-subclasses-internal
    ((class t) (kb tuple-kb) (inference-level (eql :direct))
     (number-of-values t) (kb-local-only-p t))
  (let ((class (or (coerce-to-frame-internal
		    class kb nil kb-local-only-p) class)))
    (continuable-assert
     class not-coercible-to-frame :frame class :kb kb :error-message
     "Cannot have a null class")
    (multiple-value-bind (results more-status)
      (tuple-store-fetchm `(__subclass-of ?sub ,class)
			  (tuple-kb-tuple-store kb)
			  :index-hint 1
			  :check-included-kbs-p
			  (check-included-kbs-p kb kb-local-only-p)
			  :return-pattern '?sub
			  :test (compile-pattern `(__subclass-of ?sub ,class)
						 :comparator-alist
						 ((class eq))))
      (values results t (if more-status :more nil)))))

(defmethod class-p-internal
    ((thing t) (kb tuple-kb) (kb-local-only-p t))
  (let ((thing (or (coerce-to-frame-internal
		    thing kb nil kb-local-only-p) thing))
	(class-frame (class-frame kb nil)))
    (and thing
	 (or (not (eq :fail (fetch-one-bindingm
			     `(__instance-of ,thing ,class-frame)
			     (tuple-kb-tuple-store kb)
			     (compile-pattern `(__instance-of ,thing
						,class-frame)
					      :comparator-alist
					      ((thing eq)
					       (class-frame eq)))
			     1 (check-included-kbs-p kb kb-local-only-p))))
	     (not (eq :fail (fetch-one-bindingm
			     `(__instance-of ?instance ,thing)
			     (tuple-kb-tuple-store kb)
			     (compile-pattern `(__instance-of ?instance ,thing)
					      :comparator-alist
					      ((thing eq)))
			     1 (check-included-kbs-p kb kb-local-only-p))))
	     (not (eq :fail (fetch-one-bindingm
			     `(__subclass-of ,thing ?superclass)
			     (tuple-kb-tuple-store kb)
			     (compile-pattern
			      `(__subclass-of ,thing ?superclass)
			      :comparator-alist ((thing eq)))
			     1 (check-included-kbs-p kb kb-local-only-p))))
	     (not (eq :fail (fetch-one-bindingm
			     `(__subclass-of ?subclass ,thing)
			     (tuple-kb-tuple-store kb)
			     (compile-pattern
			      `(__subclass-of ?subclass ,thing)
			      :comparator-alist ((thing eq)))
			     1 (check-included-kbs-p kb kb-local-only-p))))))))

(defmethod slot-p-internal ((thing t) (kb tuple-kb) (kb-local-only-p t))
  (let ((slot (or (coerce-to-frame-internal thing kb nil kb-local-only-p)
		  thing)))
    (cond ((member slot *tuplekb-internal-slotlike-relations*) nil)
	  (slot
	   (or (primitive-direct-instance-of-p
		slot :slot kb kb-local-only-p)
	       (not (eq :fail (fetch-one-bindingm
			       `(,slot ?frame ?value)
			       (tuple-kb-tuple-store kb)
			       (compile-pattern
				`(,slot ?frame ?value)
				:return-pattern '?value
				:comparator-alist ((slot eq)))
			       0 (check-included-kbs-p kb kb-local-only-p))))
	       (not (eq :fail (fetch-one-bindingm
			       `(__slot-of ,slot ?frame)
			       (tuple-kb-tuple-store kb)
			       (compile-pattern
				`(__slot-of ,slot ?frame)
				:comparator-alist ((slot eq)))
			       1 (check-included-kbs-p kb kb-local-only-p))))
	       (not (eq :fail
			(fetch-one-bindingm
			 `(__template-slot-value ,slot ?frame ?value)
			 (tuple-kb-tuple-store kb)
			 (compile-pattern
			  `(__template-slot-value ,slot ?frame ?value)
			  :return-pattern '?value
			  :comparator-alist ((slot eq)))
			 1 (check-included-kbs-p kb kb-local-only-p))))
	       (not (eq :fail
			(fetch-one-bindingm
			 `(__default-template-slot-value
			   ,slot ?frame ?value)
			 (tuple-kb-tuple-store kb)
			 (compile-pattern
			  `(__default-template-slot-value
			    ,slot ?frame ?value)
			  :return-pattern '?value
			  :comparator-alist ((slot eq)))
			 1 (check-included-kbs-p kb kb-local-only-p))))
	       (not (eq :fail
			(fetch-one-bindingm
			 `(__default-slot-value
			   ,slot ?frame ?value)
			 (tuple-kb-tuple-store kb)
			 (compile-pattern
			  `(__default-slot-value
			    ,slot ?frame ?value)
			  :return-pattern '?value
			  :comparator-alist ((slot eq)))
			 1 (check-included-kbs-p kb kb-local-only-p))))
	       (not (eq :fail (fetch-one-bindingm
			       `(__template-slot-of ,slot ?frame)
			       (tuple-kb-tuple-store kb)
			       (compile-pattern
				`(__template-slot-of ,slot ?frame)
				:comparator-alist ((slot eq)))
			       1 (check-included-kbs-p kb kb-local-only-p))))
	       ;; Now check for slot-p using facet sentences.
	       (not (eq :fail (fetch-one-bindingm
			       `(?facet ,slot ?frame ?value)
			       (tuple-kb-tuple-store kb)
			       (compile-pattern
				`(?facet ,slot ?frame ?value)
				:return-pattern '?value
				:comparator-alist ((slot eq)))
			       0 (check-included-kbs-p kb kb-local-only-p))))
	       (not (eq :fail (fetch-one-bindingm
			       `(__facet-of ?facet ,slot ?frame)
			       (tuple-kb-tuple-store kb)
			       (compile-pattern
				`(__facet-of ?facet ,slot ?frame)
				:return-pattern '?frame
				:comparator-alist ((slot eq)))
			       1 (check-included-kbs-p kb kb-local-only-p))))
	       (not (eq :fail (fetch-one-bindingm
			       `(__template-facet-value
				 ?facet ,slot ?frame ?value)
			       (tuple-kb-tuple-store kb)
			       (compile-pattern
				`(__template-facet-value
				  ?facet ,slot ?frame ?value)
				:return-pattern '?value
				:comparator-alist ((slot eq)))
			       1 (check-included-kbs-p kb kb-local-only-p))))
	       (not (eq :fail (fetch-one-bindingm
			       `(__default-template-facet-value
				 ?facet ,slot ?frame ?value)
			       (tuple-kb-tuple-store kb)
			       (compile-pattern
				`(__default-template-facet-value
				  ?facet ,slot ?frame ?value)
				:return-pattern '?value
				:comparator-alist ((slot eq)))
			       1 (check-included-kbs-p kb kb-local-only-p))))
	       (not (eq :fail (fetch-one-bindingm
			       `(__default-facet-value
				 ?facet ,slot ?frame ?value)
			       (tuple-kb-tuple-store kb)
			       (compile-pattern
				`(__default-facet-value
				  ?facet ,slot ?frame ?value)
				:return-pattern '?value
				:comparator-alist ((slot eq)))
			       1 (check-included-kbs-p kb kb-local-only-p))))
	       (not (eq :fail (fetch-one-bindingm
			       `(__template-facet-of
				 ?facet ,slot ?frame)
			       (tuple-kb-tuple-store kb)
			       (compile-pattern
				`(__template-facet-of
				  ?facet ,slot ?frame)
				:return-pattern '?frame
				:comparator-alist ((slot eq)))
			       1 (check-included-kbs-p kb kb-local-only-p))))))
	  (t nil))))

(defmethod frame-has-slot-p-internal ((frame t) (slot t) (kb tuple-kb)
				      (inference-level (eql :direct))
				      (slot-type t) (kb-local-only-p t))
  (let ((frame (or (coerce-to-frame-internal frame kb nil kb-local-only-p)
		   frame))
	(slot (or (coerce-to-slot-internal slot kb nil kb-local-only-p) slot)))
    (continuable-assert
     (frame-handle-p frame) not-coercible-to-frame :frame frame :kb kb)
    (cond ((member slot *tuplekb-internal-slotlike-relations*) nil)
	  (slot
	   (or (if (eq slot-type :own)
		   (or (not (eq :fail (fetch-one-bindingm
				       `(,slot ,frame ?value)
				       (tuple-kb-tuple-store kb)
				       (compile-pattern
					`(,slot ,frame ?value)
					:comparator-alist ((frame eq)
							   (slot eq)))
				       1 (check-included-kbs-p
					  kb kb-local-only-p))))
		       (not (eq :fail (fetch-one-bindingm
				       `(__slot-of ,slot ,frame)
				       (tuple-kb-tuple-store kb)
				       (compile-pattern
					`(__slot-of ,slot ,frame)
					:comparator-alist ((frame eq)
							   (slot eq)))
				       2 (check-included-kbs-p
					  kb kb-local-only-p))))
		       (not (eq :fail (fetch-one-bindingm
				       `(__default-slot-value
					 ,slot ,frame ?value)
				       (tuple-kb-tuple-store kb)
				       (compile-pattern
					`(__default-slot-value
					  ,slot ,frame ?value)
					:comparator-alist ((frame eq)
							   (slot eq)))
				       2 (check-included-kbs-p
					  kb kb-local-only-p)))))
		   (or (not (eq :fail (fetch-one-bindingm
				       `(__template-slot-value
					 ,slot ,frame ?value)
				       (tuple-kb-tuple-store kb)
				       (compile-pattern
					`(__template-slot-value
					  ,slot ,frame ?value)
					:comparator-alist ((frame eq)
							   (slot eq)))
				       2 (check-included-kbs-p
					  kb kb-local-only-p))))
		       (not (eq :fail (fetch-one-bindingm
				       `(__default-template-slot-value
					 ,slot ,frame ?value)
				       (tuple-kb-tuple-store kb)
				       (compile-pattern
					`(__default-template-slot-value
					  ,slot ,frame ?value)
					:comparator-alist ((frame eq)
							   (slot eq)))
				       2 (check-included-kbs-p
					  kb kb-local-only-p))))
		       (not (eq :fail (fetch-one-bindingm
				       `(__template-slot-of ,slot ,frame)
				       (tuple-kb-tuple-store kb)
				       (compile-pattern
					`(__template-slot-of ,slot ,frame)
					:comparator-alist ((frame eq)
							   (slot eq)))
				       2 (check-included-kbs-p
					  kb kb-local-only-p))))))
	       ;; Now try facet axioms
	       (if (eq slot-type :own)
		   (or (not (eq :fail (fetch-one-bindingm
				       `(?facet ,slot ,frame ?value)
				       (tuple-kb-tuple-store kb)
				       (compile-pattern
					`(?facet ,slot ,frame ?value)
					:return-pattern '?value
					:comparator-alist ((slot eq)
							   (frame eq)))
				       2 (check-included-kbs-p
					  kb kb-local-only-p))))
		       (not (eq :fail (fetch-one-bindingm
				       `(__facet-of ?facet ,slot ,frame)
				       (tuple-kb-tuple-store kb)
				       (compile-pattern
					`(__facet-of ?facet ,slot ,frame)
					:comparator-alist ((slot eq)
							   (frame eq)))
				       3 (check-included-kbs-p
					  kb kb-local-only-p))))
		       (not (eq :fail (fetch-one-bindingm
				       `(__default-facet-value
					 ?facet ,slot ,frame ?value)
				       (tuple-kb-tuple-store kb)
				       (compile-pattern
					`(__default-facet-value
					  ?facet ,slot ,frame ?value)
					:return-pattern '?value
					:comparator-alist ((slot eq)
							   (frame eq)))
				       3 (check-included-kbs-p
					  kb kb-local-only-p)))))
		   (or (not (eq :fail (fetch-one-bindingm
				       `(__template-facet-value
					 ?facet ,slot ,frame ?value)
				       (tuple-kb-tuple-store kb)
				       (compile-pattern
					`(__template-facet-value
					  ?facet ,slot ,frame ?value)
					:return-pattern '?value
					:comparator-alist ((slot eq)
							   (frame eq)))
				       3 (check-included-kbs-p
					  kb kb-local-only-p))))
		       (not (eq :fail (fetch-one-bindingm
				       `(__default-template-facet-value
					 ?facet ,slot ,frame ?value)
				       (tuple-kb-tuple-store kb)
				       (compile-pattern
					`(__default-template-facet-value
					  ?facet ,slot ,frame ?value)
					:return-pattern '?value
					:comparator-alist ((slot eq)
							   (frame eq)))
				       3 (check-included-kbs-p
					  kb kb-local-only-p))))
		       (not (eq :fail (fetch-one-bindingm
				       `(__template-facet-of
					 ?facet ,slot ,frame)
				       (tuple-kb-tuple-store kb)
				       (compile-pattern
					`(__template-facet-of
					  ?facet ,slot ,frame)
					:comparator-alist ((slot eq)
							   (frame eq)))
				       3 (check-included-kbs-p
					  kb kb-local-only-p))))))))
	  (t nil))))

(defmethod facet-p-internal ((thing t) (kb tuple-kb) (kb-local-only-p t))
  (let ((thing (or (coerce-to-frame-internal
		    thing kb nil kb-local-only-p) thing)))
    (cond ((member thing *tuplekb-internal-facetlike-relations*)
	   nil)
	  (thing
	   (or (primitive-direct-instance-of-p
		thing :facet kb kb-local-only-p)
	       (not (eq :fail (fetch-one-bindingm
			       `(,thing ?slot ?frame ?value)
			       (tuple-kb-tuple-store kb)
			       (compile-pattern
				`(,thing ?slot ?frame ?value)
				:return-pattern '?value
				:comparator-alist ((thing eq)))
			       0 (check-included-kbs-p kb kb-local-only-p))))
	       (not (eq :fail (fetch-one-bindingm
			       `(__facet-of ,thing ?slot ?frame)
			       (tuple-kb-tuple-store kb)
			       (compile-pattern
				`(__facet-of ,thing ?slot ?frame)
				:return-pattern '?frame
				:comparator-alist ((thing eq)))
			       1 (check-included-kbs-p kb kb-local-only-p))))
	       (not (eq :fail (fetch-one-bindingm
			       `(__template-facet-value
				 ,thing ?slot ?frame ?value)
			       (tuple-kb-tuple-store kb)
			       (compile-pattern
				`(__template-facet-value
				  ,thing ?slot ?frame ?value)
				:return-pattern '?value
				:comparator-alist ((thing eq)))
			       1 (check-included-kbs-p kb kb-local-only-p))))
	       (not (eq :fail (fetch-one-bindingm
			       `(__default-template-facet-value
				 ,thing ?slot ?frame ?value)
			       (tuple-kb-tuple-store kb)
			       (compile-pattern
				`(__default-template-facet-value
				  ,thing ?slot ?frame ?value)
				:return-pattern '?value
				:comparator-alist ((thing eq)))
			       1 (check-included-kbs-p kb kb-local-only-p))))
	       (not (eq :fail (fetch-one-bindingm
			       `(__default-facet-value
				 ,thing ?slot ?frame ?value)
			       (tuple-kb-tuple-store kb)
			       (compile-pattern
				`(__default-facet-value
				  ,thing ?slot ?frame ?value)
				:return-pattern '?value
				:comparator-alist ((thing eq)))
			       1 (check-included-kbs-p kb kb-local-only-p))))
	       (not (eq :fail (fetch-one-bindingm
			       `(__template-facet-of
				 ,thing ?slot ?frame)
			       (tuple-kb-tuple-store kb)
			       (compile-pattern
				`(__template-facet-of
				  ,thing ?slot ?frame)
				:return-pattern '?frame
				:comparator-alist ((thing eq)))
			       1 (check-included-kbs-p kb kb-local-only-p))))))
	  (t nil))))

(defmethod slot-has-facet-p-internal ((frame t) (slot t) (facet t)
				      (kb tuple-kb)
				      (inference-level (eql :direct))
				      (slot-type t) (kb-local-only-p t))
  (let ((frame (or (coerce-to-frame-internal frame kb nil kb-local-only-p)
		   frame))
	(slot  (coerce-to-slot-internal   slot kb t kb-local-only-p))
	(facet (coerce-to-facet-internal facet kb t kb-local-only-p)))
    (continuable-assert
     (frame-handle-p frame) not-coercible-to-frame :frame frame :kb kb)
    (cond ((member facet *tuplekb-internal-facetlike-relations*)
	   nil)
	  (facet
	   (if (eq slot-type :own)
	       (or (not (eq :fail (fetch-one-bindingm
				   `(,facet ,slot ,frame ?value)
				   (tuple-kb-tuple-store kb)
				   (compile-pattern
				    `(,facet ,slot ,frame ?value)
				    :comparator-alist ((facet eq)
						       (slot eq)
						       (frame eq)))
				   2 (check-included-kbs-p
				      kb kb-local-only-p))))
		   (not (eq :fail (fetch-one-bindingm
				   `(__facet-of ,facet ,slot ,frame)
				   (tuple-kb-tuple-store kb)
				   (compile-pattern
				    `(__facet-of ,facet ,slot ,frame)
				    :comparator-alist ((facet eq)
						       (slot eq)
						       (frame eq)))
				   3 (check-included-kbs-p
				      kb kb-local-only-p))))
		   (not (eq :fail (fetch-one-bindingm
				   `(__default-facet-value
				     ,facet ,slot ,frame ?value)
				   (tuple-kb-tuple-store kb)
				   (compile-pattern
				    `(__default-facet-value
				      ,facet ,slot ,frame ?value)
				    :comparator-alist ((facet eq)
						       (slot eq)
						       (frame eq)))
				   3 (check-included-kbs-p
				      kb kb-local-only-p)))))
	       (or (not (eq :fail (fetch-one-bindingm
				   `(__template-facet-value
				     ,facet ,slot ,frame ?value)
				   (tuple-kb-tuple-store kb)
				   (compile-pattern
				    `(__template-facet-value
				      ,facet ,slot ,frame ?value)
				    :comparator-alist ((facet eq)
						       (slot eq)
						       (frame eq)))
				   3 (check-included-kbs-p
				      kb kb-local-only-p))))
		   (not (eq :fail (fetch-one-bindingm
				   `(__default-template-facet-value
				     ,facet ,slot ,frame ?value)
				   (tuple-kb-tuple-store kb)
				   (compile-pattern
				    `(__default-template-facet-value
				      ,facet ,slot ,frame ?value)
				    :comparator-alist ((facet eq)
						       (slot eq)
						       (frame eq)))
				   3 (check-included-kbs-p
				      kb kb-local-only-p))))
		   (not (eq :fail (fetch-one-bindingm
				   `(__template-facet-of
				     ,facet ,slot ,frame)
				   (tuple-kb-tuple-store kb)
				   (compile-pattern
				    `(__template-facet-of
				      ,facet ,slot ,frame)
				    :comparator-alist ((facet eq)
						       (slot eq)
						       (frame eq)))
				   3 (check-included-kbs-p
				      kb kb-local-only-p)))))))
	  (t nil))))

(defmethod get-slot-facets-internal
    ((frame t) (slot t) (kb tuple-kb) (inference-level t) (slot-type t)
     (kb-local-only-p t))
  (let ((frame (or (coerce-to-frame-internal
		    frame kb nil kb-local-only-p) frame))
	(slot  (or (coerce-to-frame-internal
		    slot kb nil kb-local-only-p)  slot)))
    (continuable-assert
     frame not-coercible-to-frame :frame frame :kb kb :error-message
     "Cannot have a null frame")
    (continuable-assert
     slot slot-not-found :frame frame :slot slot :kb kb :slot-type slot-type
     :error-message "Cannot have a null slot")
    (values
     (remove-duplicates
      (append (if (member slot-type '(:all :own))
		  (append
		   (tuple-store-fetchm
		    `(__facet-of ?facet ,slot ,frame)
		    (tuple-kb-tuple-store kb)
		    :index-hint 2
		    :return-pattern '?facet
		    :check-included-kbs-p
		    (check-included-kbs-p kb kb-local-only-p)
		    :test (compile-pattern
			   `(__facet-of ?facet ,slot ,frame)
			   :return-pattern ?facet
			   :comparator-alist ((slot eq) (frame eq))))
		   (set-difference
		    (tuple-store-fetchm
		     `(?facet ,slot ,frame ?value)
		     (tuple-kb-tuple-store kb)
		     :index-hint 1
		     :return-pattern '?facet
		     :check-included-kbs-p
		     (check-included-kbs-p kb kb-local-only-p)
		     :test (compile-pattern
			    `(?facet ,slot ,frame ?value)
			    :return-pattern ?facet
			    :comparator-alist ((slot eq)
					       (frame eq))))
		    *tuplekb-internal-facetlike-relations*))
		  nil)
	      (if (member slot-type '(:all :template))
		  (append
		   (tuple-store-fetchm
		    `(__template-facet-of ?facet ,slot ,frame)
		    (tuple-kb-tuple-store kb)
		    :index-hint 2
		    :return-pattern '?facet
		    :check-included-kbs-p
		    (check-included-kbs-p kb kb-local-only-p)
		    :test (compile-pattern
			   `(__template-facet-of ?facet ,slot ,frame)
			   :return-pattern ?facet
			   :comparator-alist ((slot eq) (frame eq))))
		   (tuple-store-fetchm
		    `(__template-facet-value ?facet ,slot ,frame ?value)
		    (tuple-kb-tuple-store kb)
		    :index-hint 2
		    :return-pattern '?facet
		    :check-included-kbs-p
		    (check-included-kbs-p kb kb-local-only-p)
		    :test (compile-pattern
			   `(__template-facet-value ?facet ,slot ,frame ?value)
			   :return-pattern ?facet
			   :comparator-alist ((slot eq) (frame eq)))))
		  nil)))
     t)))

(defmethod get-frame-slots-internal
    ((frame t) (kb tuple-kb) (inference-level (eql :direct)) (slot-type t)
     (kb-local-only-p t))
  (let ((frame (or (coerce-to-frame-internal
		    frame kb nil kb-local-only-p) frame)))
    (continuable-assert
     frame not-coercible-to-frame :frame frame :kb kb :error-message
     "Cannot have a null frame")
    (let ((slots
	   (remove-duplicates
	    (append
	     (if (member slot-type '(:all :own))
		 (set-difference  
		  (append
		   (tuple-store-fetchm
		    `(__slot-of ?slot ,frame)
		    (tuple-kb-tuple-store kb)
		    :index-hint 1
		    :check-included-kbs-p
		    (check-included-kbs-p kb kb-local-only-p)
		    :return-pattern '?slot
		    :test (compile-pattern `(__slot-of ?slot ,frame)
					   :return-pattern ?slot
					   :comparator-alist
					   ((frame eq))))
		   (tuple-store-fetchm
		    `(?slot ,frame ?value)
		    (tuple-kb-tuple-store kb)
		    :index-hint 0
		    :check-included-kbs-p
		    (check-included-kbs-p kb kb-local-only-p)
		    :return-pattern '?slot
		    :test (compile-pattern `(?slot ,frame ?value)
					   :return-pattern ?slot
					   :comparator-alist
					   ((frame eq))))
		   (tuple-store-fetchm
		    `(__default-slot-value ?slot ,frame ?value)
		    (tuple-kb-tuple-store kb)
		    :index-hint 1
		    :check-included-kbs-p
		    (check-included-kbs-p kb kb-local-only-p)
		    :return-pattern '?slot
		    :test (compile-pattern
			   `(__default-slot-value ?slot ,frame ?value)
			   :return-pattern ?slot
			   :comparator-alist
			   ((frame eq)))))
		   *tuplekb-internal-slotlike-relations*)
		 nil)
	     (if (member slot-type '(:all :template))
		 (append
		  (tuple-store-fetchm
		   `(__template-slot-of ?slot ,frame)
		   (tuple-kb-tuple-store kb)
		   :index-hint 1
		   :check-included-kbs-p
		   (check-included-kbs-p kb kb-local-only-p)
		   :return-pattern '?slot
		   :test (compile-pattern
			  `(__template-slot-of ?slot ,frame)
			  :return-pattern ?slot
			  :comparator-alist ((frame eq))))
		  (tuple-store-fetchm
		   `(__default-template-slot-value ?slot ,frame ?value)
		   (tuple-kb-tuple-store kb)
		   :index-hint 1
		   :check-included-kbs-p
		   (check-included-kbs-p kb kb-local-only-p)
		   :return-pattern '?slot
		   :test (compile-pattern
			  `(__default-template-slot-value ?slot ,frame ?value)
			  :return-pattern ?slot
			  :comparator-alist
			  ((frame eq))))
		  (tuple-store-fetchm
		   `(__template-slot-value ?slot ,frame ?value)
		   (tuple-kb-tuple-store kb)
		   :index-hint 1
		   :check-included-kbs-p
		   (check-included-kbs-p kb kb-local-only-p)
		   :return-pattern '?slot
		   :test (compile-pattern
			  `(__template-slot-value ?slot ,frame ?value)
			  :return-pattern ?slot
			  :comparator-alist
			  ((frame eq)))))
		 nil)
	     ;;; Now try facets....
	     (if (member slot-type '(:all :own))
		 (let ((facts
			(append
			 (tuple-store-fetchm
			  `(__facet-of ?facet ?slot ,frame)
			  (tuple-kb-tuple-store kb)
			  :index-hint 1
			  :check-included-kbs-p
			  (check-included-kbs-p kb kb-local-only-p)
			  :return-pattern '(?facet ?slot)
			  :test (compile-pattern
				 `(__facet-of ?facet ?slot ,frame)
				 :return-pattern (?facet ?slot)
				 :comparator-alist
				 ((frame eq))))
			 (tuple-store-fetchm
			  `(?facet ?slot ,frame ?value)
			  (tuple-kb-tuple-store kb)
			  :index-hint 0
			  :check-included-kbs-p
			  (check-included-kbs-p kb kb-local-only-p)
			  :return-pattern '(?facet ?slot)
			  :test (compile-pattern
				 `(?facet ?slot ,frame ?value)
				 :return-pattern (?facet ?slot)
				 :comparator-alist
				 ((frame eq))))
			 (tuple-store-fetchm
			  `(__default-facet-value ?facet ?slot ,frame ?value)
			  (tuple-kb-tuple-store kb)
			  :index-hint 1
			  :check-included-kbs-p
			  (check-included-kbs-p kb kb-local-only-p)
			  :return-pattern '(?facet ?slot)
			  :test (compile-pattern
				 `(__default-facet-value
				   ?facet ?slot ,frame ?value)
				 :return-pattern (?facet ?slot)
				 :comparator-alist
				 ((frame eq)))))))
		   (loop for (facet slot) in facts
			 when (not (member
				    facet
				    *tuplekb-internal-facetlike-relations*))
			 collect slot))
		 nil)
	     (if (member slot-type '(:all :template))
		 (append
		  (tuple-store-fetchm
		   `(__template-facet-of ?facet ?slot ,frame)
		   (tuple-kb-tuple-store kb)
		   :index-hint 1
		   :check-included-kbs-p
		   (check-included-kbs-p kb kb-local-only-p)
		   :return-pattern '?slot
		   :test (compile-pattern
			  `(__template-facet-of ?facet ?slot ,frame)
			  :return-pattern ?slot
			  :comparator-alist
			  ((frame eq))))
		  (tuple-store-fetchm
		   `(__default-template-facet-value ?facet ?slot ,frame ?value)
		   (tuple-kb-tuple-store kb)
		   :index-hint 1
		   :check-included-kbs-p
		   (check-included-kbs-p kb kb-local-only-p)
		   :return-pattern '?slot
		   :test (compile-pattern
			  `(__default-template-facet-value
			    ?facet ?slot ,frame ?value)
			  :return-pattern ?slot
			  :comparator-alist
			  ((frame eq))))
		  (tuple-store-fetchm
		   `(__template-facet-value ?facet ?slot ,frame ?value)
		   (tuple-kb-tuple-store kb)
		   :index-hint 1
		   :check-included-kbs-p
		   (check-included-kbs-p kb kb-local-only-p)
		   :return-pattern '?slot
		   :test (compile-pattern
			  `(__template-facet-value ?facet ?slot ,frame ?value)
			  :return-pattern ?slot
			  :comparator-alist
			  ((frame eq)))))
		 nil))
	    :test (decanonicalize-testfn :equal kb kb-local-only-p))))
      (values slots t))))

(defmethod get-frame-in-kb-internal
    ((thing t) (kb tuple-kb) (error-p t) (kb-local-only-p t))
  (coerce-to-frame-internal thing kb error-p kb-local-only-p))

(defmethod get-kb-frames-internal ((kb tuple-kb) (kb-local-only-p t))
  (maybe-post-hoc-full-index-kb (tuple-kb-tuple-store kb))
  (let ((ht (make-hash-table))
	(all nil))
    (loop for c in (tuple-store-fetchm
		    `(__instance-of ?instance ?class)
		    (tuple-kb-tuple-store kb)
		    :check-included-kbs-p
		    (check-included-kbs-p kb kb-local-only-p)
		    :return-pattern '?class
		    :test (compile-pattern `(__instance-of ?instance ?class)
					   :return-pattern '?class))
	  unless (member c *tuplekb-internal-relations*)
	  do (let ((key (fast-hash-key c)))
	       (when (not (gethash key ht))
		 (setf (gethash key ht) c)
		 (push c all))))
    (loop for i in (tuple-store-fetchm
		    `(__instance-of ?instance ?class)
		    (tuple-kb-tuple-store kb)
		    :check-included-kbs-p
		    (check-included-kbs-p kb kb-local-only-p)
		    :return-pattern '?instance
		    :test (compile-pattern `(__instance-of ?instance ?class)
					   :return-pattern '?instance))
	  unless (member i *tuplekb-internal-relations*)
	  do (let ((key (fast-hash-key i)))
	       (when (not (gethash key ht))
		 (setf (gethash key ht) i)
		 (push i all))))
    all))

(defmethod get-kb-classes-internal ((kb tuple-kb) (selector t)
				    (kb-local-only-p t))
  (maybe-post-hoc-full-index-kb (tuple-kb-tuple-store kb))
  (let ((ht (make-hash-table))
	(all nil)
	(class-frame (class-frame kb nil)))
    (loop for c in (tuple-store-fetchm
		    `(__instance-of ?class ,class-frame)
		    (tuple-kb-tuple-store kb)
		    :check-included-kbs-p
		    (check-included-kbs-p kb kb-local-only-p)
		    :return-pattern '?class
		    :test (compile-pattern `(__instance-of ?class ,class-frame)
					   :return-pattern '?class
					   :comparator-alist
					   ((class-frame eq))))
	  do (let ((key (fast-hash-key c)))
	       (when (not (gethash key ht))
		 (setf (gethash key ht) c)
		 (push c all))))
    (loop for c in (tuple-store-fetchm
		    `(__instance-of ?instance ?class)
		    (tuple-kb-tuple-store kb)
		    :check-included-kbs-p
		    (check-included-kbs-p kb kb-local-only-p)
		    :return-pattern '?class
		    :test (compile-pattern `(__instance-of ?instance ?class)
					   :return-pattern '?class))
	  unless (member c *tuplekb-internal-relations*)
	  do (let ((key (fast-hash-key c)))
	       (when (not (gethash key ht))
		 (setf (gethash key ht) c)
		 (push c all))))
    all))

(defmethod get-kb-individuals-internal ((kb tuple-kb) (selector t)
					(kb-local-only-p t))
  (maybe-post-hoc-full-index-kb (tuple-kb-tuple-store kb))
  (let ((ht (make-hash-table))
	(all nil))
    (let ((matches (tuple-store-fetchm
		    `(__instance-of ?instance ?class)
		    (tuple-kb-tuple-store kb)
		    :check-included-kbs-p
		    (check-included-kbs-p kb kb-local-only-p)
		    :return-pattern '?instance
		    :test (compile-pattern `(__instance-of ?instance ?class)
					   :return-pattern '?instance))))
      (loop for i in matches
	    unless (class-p-internal i kb kb-local-only-p)
	    do (let ((key (fast-hash-key i)))
		 (when (not (gethash key ht))
		   (setf (gethash key ht) i)
		   (push i all)))))
    all))

(defmethod attach-slot-internal (frame slot (kb tuple-kb)
				       (slot-type t) (kb-local-only-p t))
  (when (member :immediate (internal-get-behavior-values 
			    :constraint-checking-time kb))
    (enforce-domain-constraint frame slot kb slot-type :all-inferable
			       :either kb-local-only-p))
  (let ((fact (slot-attachment-fact frame slot kb slot-type kb-local-only-p)))
    (insert fact (tuple-kb-tuple-store kb) t)))

(defmethod detach-slot-internal (frame slot (kb tuple-kb)
				       (slot-type t)
				       (kb-local-only-p t))
  (let ((fact (slot-attachment-fact frame slot kb slot-type kb-local-only-p)))
    (drop fact (tuple-kb-tuple-store kb) t
	  (check-included-kbs-p kb kb-local-only-p))))

(defmethod put-slot-values-internal
    ((frame t) (slot t) (values t) (kb tuple-kb) (slot-type t)
     (value-selector t) (kb-local-only-p t))
  (with-read-only-checking (kb)
    (continuable-assert
     frame not-coercible-to-frame :frame frame :kb kb :error-message
     "Cannot have a null frame")
    (continuable-assert
     slot slot-not-found :frame frame :slot slot :kb kb :slot-type slot-type
     :error-message "Cannot have a null slot")
    (let ((frame (or (coerce-to-frame-internal
		      frame kb nil kb-local-only-p) frame))
	  (slot  (ensure-has-slot slot slot-type kb kb-local-only-p)))
      (continuable-assert
       frame not-coercible-to-frame :frame frame :kb kb
       :error-message "Cannot have a null frame")
      (continuable-assert
       slot slot-not-found :frame frame :slot slot :kb kb :slot-type slot-type
       :error-message "Cannot have a null slot")
      (when (member :immediate (internal-get-behavior-values 
				:constraint-checking-time kb))
        (let ((current-values
	       (get-slot-values-internal frame slot kb :all-inferable
					 slot-type :all :either nil)))
	  (enforce-slot-constraints 
	   frame slot current-values values kb :all-inferable slot-type
	   :either nil)))
      (ecase slot-type
        (:own 
	 (ecase value-selector
           (:known-true (drop `(,slot ,frame ?value)
			      (tuple-kb-tuple-store kb) nil
			      (check-included-kbs-p kb kb-local-only-p))
			(let ((internal (and (frame-handle-p slot)
					     (getf (frame-handle-plist slot)
						   :internal-relation))))
			  (when internal
			    (drop `(,internal ,frame ?value)
				  (tuple-kb-tuple-store kb) nil
				  (check-included-kbs-p kb kb-local-only-p)))))
	   (:default-only
	     (drop `(__default-slot-value ,slot ,frame ?value)
		   (tuple-kb-tuple-store kb) nil
		   (check-included-kbs-p kb kb-local-only-p)))))
	(:template
	 (ecase value-selector
	   (:known-true
	    (drop `(__template-slot-value ,slot ,frame ?value)
		  (tuple-kb-tuple-store kb) nil
		  (check-included-kbs-p kb kb-local-only-p)))
	   (:default-only
	    (drop `(__default-template-slot-value ,slot ,frame ?value)
		  (tuple-kb-tuple-store kb) nil
		  (check-included-kbs-p kb kb-local-only-p))))))
      (loop with internal = (and (frame-handle-p slot)
				 (getf (frame-handle-plist slot)
				       :internal-relation))
	    for value in values
	    for facts = (ecase slot-type
			  (:own
			   (ecase value-selector
			     (:known-true
			      (if internal
				  `((,slot ,frame ,value)
				    (,internal ,frame ,value))
				  `((,slot ,frame ,value))))
			     (:default-only 
				 (if (eq value '__deleted)
				     `((__default-slot-value
					,slot ,frame ,value))
				     (continuable-error
				      "Cannot put a default own slot value")))))
			  (:template
			   (ecase value-selector
			     (:known-true
			      `((__template-slot-value ,slot ,frame ,value)))
			     (:default-only
				 `((__default-template-slot-value
				    ,slot ,frame ,value))))))
	    do (loop for fact in facts
		     do (insert fact (tuple-kb-tuple-store kb) t))))))

(defmethod add-slot-value-internal
    ((frame t) (slot t) (value t) (kb tuple-kb) (test t) (slot-type t)
     (add-before t) (value-selector t) (kb-local-only-p t))
  (with-read-only-checking (kb)
    (continuable-assert
     frame not-coercible-to-frame :frame frame :kb kb :error-message
     "Cannot have a null frame")
    (continuable-assert slot slot-not-found :frame frame :slot slot :kb kb
			:slot-type slot-type
			:error-message "Cannot have a null slot")
    (let ((frame (or (coerce-to-frame-internal
		      frame kb nil kb-local-only-p) frame))
	  (slot (ensure-has-slot slot slot-type kb kb-local-only-p)))
      (continuable-assert frame not-coercible-to-frame :frame frame :kb kb
			  :error-message "Cannot have a null frame")
      (continuable-assert slot slot-not-found :frame frame :slot slot :kb kb
			  :slot-type slot-type
			  :error-message "Cannot have a null slot")
      (when (member :immediate (internal-get-behavior-values 
				:constraint-checking-time kb))
        (let ((current-values
	       (get-slot-values-internal frame slot kb :all-inferable
					 slot-type :all :either nil)))
	  (enforce-slot-constraints 
	   frame slot current-values 
	   (if (member value current-values 
		       :test #'(lambda (x y)
				 (equal-in-kb-internal 
				  x y kb kb-local-only-p)))
	       current-values
	     (cons value current-values))
	   kb :all-inferable slot-type :either nil)))
      (ecase value-selector
        (:known-true
	 (let ((facts (ecase slot-type
			(:own (let ((internal
				     (and (frame-handle-p slot)
					  (getf (frame-handle-plist slot)
						:internal-relation))))
				(if internal
				    `((,slot ,frame ,value)
				      (,internal ,frame ,value))
				    `((,slot ,frame ,value)))))
			(:template
			 `((__template-slot-value ,slot ,frame ,value))))))
	   (loop for fact in facts
		 do (insert fact (tuple-kb-tuple-store kb) t))))
	(:default-only
	 ;; Can only have one default slot value, so delete any existing ones.
	 (ecase slot-type
	   (:template
	    (drop `(__default-template-slot-value ,slot ,frame ?value)
		  (tuple-kb-tuple-store kb) nil
		  (check-included-kbs-p kb kb-local-only-p)))
	   (:own
	    (drop `(__default-slot-value ,slot ,frame ?value)
		  (tuple-kb-tuple-store kb) nil
		  (check-included-kbs-p kb kb-local-only-p))))
	 (let ((fact (ecase slot-type
		       (:template `(__default-template-slot-value
				    ,slot ,frame ,value))
		       (:own `(__default-slot-value ,slot ,frame ,value)))))
	   (insert fact (tuple-kb-tuple-store kb) t)))))))

(defmethod attach-facet-internal (frame slot facet (kb tuple-kb)
					(slot-type t) (kb-local-only-p t))
  (when (member :immediate (internal-get-behavior-values 
			    :constraint-checking-time kb))
    (enforce-domain-constraint frame slot kb slot-type :all-inferable
			       :either kb-local-only-p))
  (let ((fact (facet-attachment-fact frame slot facet kb slot-type
				     kb-local-only-p)))
    (insert fact (tuple-kb-tuple-store kb) t)))

(defmethod detach-facet-internal (frame slot facet (kb tuple-kb)
					(slot-type t) (kb-local-only-p t))
  (let ((fact (facet-attachment-fact frame slot facet kb slot-type
				     kb-local-only-p)))
    (drop fact (tuple-kb-tuple-store kb) t
	  (check-included-kbs-p kb kb-local-only-p))))

(defmethod put-facet-values-internal
    ((frame t) (slot t) (facet t) (values t) (kb tuple-kb)
     (slot-type t) (value-selector t) (kb-local-only-p t))
  (with-read-only-checking (kb)
    (continuable-assert
     frame not-coercible-to-frame :frame frame :kb kb :error-message
     "Cannot have a null frame")
    (continuable-assert slot slot-not-found :frame frame :slot slot :kb kb
			:slot-type slot-type
			:error-message "Cannot have a null slot")
    (continuable-assert
     facet facet-not-found :frame frame :slot slot :facet facet
     :kb kb :error-message "Cannot have a null facet")
    (let ((frame (or (coerce-to-frame-internal
		      frame kb nil kb-local-only-p) frame))
	  (slot (ensure-has-slot slot slot-type kb kb-local-only-p)))
      (continuable-assert frame not-coercible-to-frame :frame frame :kb kb
			  :error-message "Cannot have a null frame")
      (continuable-assert slot slot-not-found :frame frame :slot slot :kb kb
			  :slot-type slot-type
			  :error-message "Cannot have a null slot")
      (let ((facet (ensure-has-facet facet slot slot-type kb
				     kb-local-only-p)))
	(continuable-assert
	 facet facet-not-found :frame frame :slot slot :facet facet
	 :kb kb :error-message "Cannot have a null facet")
	(when (member :immediate (internal-get-behavior-values 
				  :constraint-checking-time kb))
	  (let ((current-values (get-facet-values-internal
				 frame slot facet kb :all-inferable slot-type
				 :all :either nil)))
	    (check-assertion-of-constraint-facet-values
	     frame slot facet current-values values kb :all-inferable
	     slot-type value-selector kb-local-only-p)))
	(ecase slot-type
	  (:own 
	   (ecase value-selector
	    (:known-true
	     (drop `(,facet ,slot ,frame ?value) (tuple-kb-tuple-store kb) nil
		   (check-included-kbs-p kb kb-local-only-p))
	     (let ((internal (and (frame-handle-p facet)
				  (getf (frame-handle-plist facet)
					:internal-relation))))
	       (when internal
		 (drop `(,internal ,slot ,frame ?value)
		       (tuple-kb-tuple-store kb) nil
		       (check-included-kbs-p kb kb-local-only-p)))))
	    (:default-only
		(drop `(__default-facet-value ,facet ,slot ,frame ?value)
		      (tuple-kb-tuple-store kb) nil
		      (check-included-kbs-p kb kb-local-only-p)))))
	  (:template
	   (ecase value-selector
	    (:known-true
	     (drop
	      `(__template-facet-value ,facet ,slot ,frame ?value)
	      (tuple-kb-tuple-store kb) nil
	      (check-included-kbs-p kb kb-local-only-p)))
	    (:default-only
	     (drop
	      `(__default-template-facet-value ,facet ,slot ,frame ?value)
	      (tuple-kb-tuple-store kb) nil
	      (check-included-kbs-p kb kb-local-only-p))))))
	(loop with internal = (and (frame-handle-p facet)
				   (getf (frame-handle-plist facet)
					 :internal-relation))
	      for value in values
	      for facts
	      = (ecase slot-type
		  (:own
		   (ecase value-selector
		     (:known-true
		      (if internal
			  `((,facet ,slot ,frame ,value)
			    (,internal ,slot ,frame ,value))
			  `((,facet ,slot ,frame ,value))))
		     (:default-only
			 (if (eq value '__deleted)
			     `((__default-facet-value
				,facet ,slot ,frame ,value))
			     (continuable-error
			      "Cannot put a default own facet value")))))
		  (:template
		   (ecase value-selector
		     (:known-true
		      `((__template-facet-value
			 ,facet ,slot ,frame ,value)))
		     (:default-only
			 `((__default-template-facet-value
			   ,facet ,slot ,frame ,value))))))
	      do (loop for fact in facts
		       do (insert fact (tuple-kb-tuple-store kb) t)))))))

(defmethod put-class-superclasses-internal
    ((class t) (new-superclasses t) (kb tuple-kb) (kb-local-only-p t))
  (with-read-only-checking (kb)
    (let ((class (or (coerce-to-frame-internal
		      class kb nil kb-local-only-p) class)))
      (continuable-assert class not-coercible-to-frame :frame class :kb kb
			  :error-message "Cannot have a null class")
      (drop `(__subclass-of ,class ?super) (tuple-kb-tuple-store kb) nil
	    (check-included-kbs-p kb kb-local-only-p))
      (loop for new-super in new-superclasses
	    for coerced-new-super
	    = (or (coerce-to-frame-internal
		   new-super kb nil kb-local-only-p) new-super)
	    for fact = `(__subclass-of ,class ,coerced-new-super)
	    do (continuable-assert coerced-new-super not-coercible-to-frame
				   :frame class :kb kb :error-message
				   "Cannot have a null superclass.")
	    (insert fact (tuple-kb-tuple-store kb) t)))))

(defmethod add-class-superclass-internal
    ((class t) (new-superclass t) (kb tuple-kb) (kb-local-only-p t))
  (with-read-only-checking (kb)
    (let ((class (or (coerce-to-frame-internal
		      class kb nil kb-local-only-p) class)))
      (continuable-assert class not-coercible-to-frame :frame class :kb kb
			  :error-message "Cannot have a null class")
      (let ((coerced-new-super
	     (or (coerce-to-frame-internal
		  new-superclass kb nil kb-local-only-p) new-superclass)))
	(continuable-assert coerced-new-super not-coercible-to-frame
			    :frame class :kb kb :error-message
			    "Cannot have a null superclass.")
	(let ((fact `(__subclass-of ,class ,coerced-new-super)))
	  (insert fact (tuple-kb-tuple-store kb) t))))))

(defmethod put-instance-types-internal
    ((frame t) (new-types t) (kb tuple-kb) (kb-local-only-p t))
  (with-read-only-checking (kb)
    (let ((frame (or (coerce-to-frame-internal
		      frame kb nil kb-local-only-p) frame)))
      (continuable-assert frame not-coercible-to-frame :frame frame :kb kb
			  :error-message "Cannot have a null frame")
      (let ((existing-types (tuple-kb-get-direct-types-from-tuples
			     frame kb :all kb-local-only-p)))
	(loop for type in existing-types
	      unless (member type '(__facet __slot __class __individual))
	      do (drop `(__instance-of ,frame ,type) (tuple-kb-tuple-store kb)
		       nil (check-included-kbs-p kb kb-local-only-p))))
      (loop for new-type in (list-if-not new-types)
	    for coerced-new-type
	    = (or (coerce-to-frame-internal
		   new-type kb nil kb-local-only-p) new-type)
	    for fact = `(__instance-of ,frame ,coerced-new-type)
	    do (continuable-assert
		coerced-new-type not-coercible-to-frame :frame frame
		:kb kb :error-message "Cannot have a null type.")
	    (insert fact (tuple-kb-tuple-store kb) t)))))

(defmethod add-instance-type-internal
    ((frame t) (new-type t) (kb tuple-kb) (kb-local-only-p t))
  (with-read-only-checking (kb)
    (let ((frame (or (coerce-to-frame-internal
		      frame kb nil kb-local-only-p) frame)))
      (continuable-assert frame not-coercible-to-frame :frame frame :kb kb
			  :error-message "Cannot have a null frame")
      (let ((coerced-new-type
	     (or (coerce-to-frame-internal
		  new-type kb nil kb-local-only-p) new-type)))
	(continuable-assert
	 coerced-new-type not-coercible-to-frame :frame frame
	 :kb kb :error-message "Cannot have a null type.")
	(let ((fact `(__instance-of ,frame ,coerced-new-type)))
	  (insert fact (tuple-kb-tuple-store kb) t))))))

(defmethod create-bootstrap-class
    ((name t) (kb tuple-kb) (direct-superclasses t)
     (kb-local-only-p t))
  (with-read-only-checking 
      (kb)
    (let ((frame (allocate-frame-handle-internal name :class kb nil)))
      (insert `(__name ,frame ,name) (tuple-kb-tuple-store kb) t)
      (when (not (member name '(:thing :class :frame)))

	
	(let ((class_frame (class-frame kb nil)))
	  (assert class_frame () "Frame for class is missing.")
	  (let ((fact `(__instance-of ,frame ,class_frame)))
	    (insert fact (tuple-kb-tuple-store kb) t))))
      (insert `(__primitive ,frame) (tuple-kb-tuple-store kb) t)
      (when (not (eq :thing name))
	(loop for super in (list-if-not
			    (or direct-superclasses
				(direct-coercible-to-frame-p
				 :thing kb kb-local-only-p)))
	      do (let ((fact `(__subclass-of ,frame ,super)))
		   (insert fact (tuple-kb-tuple-store kb) t))))
      frame)))

(defmethod initialize-bootstrap-class
    (name (frame t) (kb tuple-kb) (direct-superclasses t)
     (kb-local-only-p t))
  (with-read-only-checking 
      (kb)
    (insert `(__name ,frame ,name) (tuple-kb-tuple-store kb) t)
    (when (not (member name '(:thing :class :frame)))
      (let ((class_frame (class-frame kb nil)))
	(assert class_frame () "Frame for class is missing.")
	(let ((fact `(__instance-of ,frame ,class_frame)))
	  (insert fact (tuple-kb-tuple-store kb) t))))
    (insert `(__primitive ,frame) (tuple-kb-tuple-store kb) t)
    (when (not (eq :thing name))
      (loop for super in (list-if-not
			  (or direct-superclasses
			      (direct-coercible-to-frame-p
			       :thing kb kb-local-only-p)))
	    do (let ((fact `(__subclass-of ,frame ,super)))
		 (insert fact (tuple-kb-tuple-store kb) t))))
    frame))

(defmethod create-class-internal
    ((name t) (kb tuple-kb) (direct-types t) (direct-superclasses t)
     (primitive-p t) (doc t) (template-slots t) (template-facets t)
     (own-slots t) (own-facets t) (handle t) (pretty-name t)
     (kb-local-only-p t))
  (declare (special *okbc-standard-names*))
  (let ((standard-p
	 (and (member name *okbc-standard-names*)
	      (not (member name ok-back:*kif-meta-extension-symbols*)))))
    (if standard-p
	(coerce-to-frame-internal name kb t kb-local-only-p)
	(let ((names-required-p (not (member nil (internal-get-behavior-values
						  :frame-names-required kb)))))
	  (continuable-assert (or name (not names-required-p)))
	  (with-read-only-checking 
	      (kb)
	    (let ((frame (or handle
			     (if names-required-p
				 (multiple-value-bind (existing found-p)
				     (if standard-p
					 (direct-coercible-to-frame-p
					  name kb kb-local-only-p)
					 (coerce-to-frame-internal
					  name kb nil kb-local-only-p))
				   (if found-p
				       (get-frame-handle-internal
					existing kb kb-local-only-p)
				       (allocate-frame-handle-internal
					name :class kb nil)))
				 (allocate-frame-handle-internal
				  name :class kb nil)))))
	      (when name
		(put-frame-name-internal frame name kb kb-local-only-p))
	      (insert `(__instance-of ,frame ,(frame-frame kb nil))
		      (tuple-kb-tuple-store kb) t)
	      (let ((class-frame (class-frame kb nil)))
		(if direct-types
		    (loop for type in (cons class-frame
					    (list-if-not direct-types))
			  do (add-instance-type-internal
			      frame type kb kb-local-only-p))
		    (when (not (primitive-direct-instance-of-p
				frame class-frame kb kb-local-only-p))
		      (add-instance-type-internal
		       frame class-frame kb kb-local-only-p))))
	      (when doc
		(add-slot-value-internal
		 frame '__documentation doc kb :equal :own nil
		 :known-true kb-local-only-p))
	      (when primitive-p (insert `(__primitive ,frame)
					(tuple-kb-tuple-store kb) t))
	      (when (not (eq :thing name))
		(loop for super in (list-if-not
				    (or direct-superclasses
					(coerce-to-frame-internal
					 :thing kb nil kb-local-only-p)))
		      do (add-class-superclass-internal
			  frame super kb kb-local-only-p)))
	      (multiple-value-bind (defined-slot-alist defined-facet-alist)
		  (initialize-slots-and-facets frame kb own-slots own-facets
					       :own kb-local-only-p)
		(initialize-slots-and-facets frame kb template-slots
					     template-facets :template
					     kb-local-only-p
					     defined-slot-alist
					     defined-facet-alist))
	      (when pretty-name
		(put-frame-pretty-name-internal
		 frame pretty-name kb kb-local-only-p))
	      frame))))))

(defmethod primitive-p-internal ((class t) (kb tuple-kb) (kb-local-only-p t))
  (let ((class (or (coerce-to-frame-internal
		    class kb nil kb-local-only-p) class)))
    (if class
	(not (eq :fail
		 (fetch-one-bindingm
		  `(__primitive ,class) (tuple-kb-tuple-store kb)
		  (compile-pattern `(__primitive ,class)
				   :comparator-alist ((class eq)))
		  0 (check-included-kbs-p kb kb-local-only-p))))
	t)))

(defmethod tuple-kb-p ((instance t)) nil)
(defmethod tuple-kb-p ((instance tuple-kb)) t)


;==============================================================================

;;; These might need to be revisited.

(defmethod ok-back:kb-locator-class-for-kb-type ((kb-type tuple-kb))
  'tuplekb-locator)

(defmethod create-kb-locator-internal ((thing tuple-kb) (kb-type tuple-kb)
				       (connection t))
  (let ((instance (make-tuplekb-locator
		   :name (name thing)
		   :kb-type kb-type
		   :pathname (make-pathname
			      :defaults *root-path-for-saved-tuplekbs*
			      :name (with-standard-io-syntax
					(prin1-to-string (name thing)))
			      :type "kb"))))
    (put-instance-types-internal instance :kb-locator
				 (meta-kb-internal connection) t)
    instance))

;(defmethod find-kb-locator-internal
;    ((thing tuple-kb) (kb-type tuple-kb) (connection t))
;  (let ((locators (get-class-instances-internal
;                   :kb-locator (meta-kb-internal connection)
;                   :taxonomic :all nil)))
;    (loop for locator in locators
;          when (and (typep locator 'tuplekb-locator)
;                    (eq (name locator) (name thing)))
;          return locator
;          finally (return (create-kb-locator-internal
;                           thing kb-type connection)))))


(defmethod save-kb-internal ((kb tuple-kb) (error-p t))
  (save-tuple-kb kb *tuplekb-file-format* error-p))

(defmethod implement-with-kb-io-syntax-internal
 ((procedure t) (kb tuple-kb) (purpose (eql :file)) (kb-local-only-p t))
   (with-standard-io-syntax
       (let ((*readtable* *tuplekb-readtable*)
	     (*package* (io-package kb)))
	 (funcall procedure))))

(defmethod save-tuple-kb ((kb tuple-kb) (format (eql :lisp)) (error-p t))
  (let ((facts (tuple-store:facts-locally-full-indexed-under
		'?x (tuple-kb-tuple-store kb)))
	(locator (find-kb-locator-internal kb kb (connection kb)))
	(*encode-other-data-structure-function*
	 #'(lambda (thing stream)
	     (if error-p
		 (continuable-error "Cannot save data structure: ~S" thing)
		 (warn "Cannot save data structure: ~S.  Saving NIL instead"
		       thing))
	     (encode-data-structure-to-stream nil stream :portable))))
    (declare (special *encode-other-data-structure-function*))
    (continuable-assert (typep locator 'tuplekb-locator) nil
			"Cannot get the right sort of locator for ~S" kb)
    (format t "~%There are ~D facts to save.~%" (length facts))
    (save-sentential-kb kb facts (tuplekb-locator-pathname locator))
    t))

(defmethod allocate-all-symbol-stash-indices :before ((facts t) (kb tuple-kb))
  ;; Do these fist so that they have short numbers!
  (allocate-symbol-stash-indices *tuplekb-internal-relations*))

(defmethod save-tuple-kb ((kb tuple-kb) (format (eql :portable)) (error-p t))
  (let ((facts (tuple-store:facts-locally-full-indexed-under
		'?x (tuple-kb-tuple-store kb)))
	(locator (find-kb-locator-internal kb kb (connection kb)))
	(*encode-other-data-structure-function*
	 #'(lambda (thing stream)
	     (if error-p
		 (continuable-error "Cannot save data structure: ~S" thing)
		 (warn "Cannot save data structure: ~S.  Saving NIL instead"
		       thing))
	     (encode-data-structure-to-stream nil stream :portable)))
	(temp-file-name
	 (if error-p
	     nil
	     (make-pathname :name (format nil "tmp-save-~D"
					  (get-universal-time))
			    :type "sav"
			    :defaults (pathname "/tmp/")))))
    (declare (special *encode-other-data-structure-function*))
    (continuable-assert (typep locator 'tuplekb-locator) nil
			"Cannot get the right sort of locator for ~S" kb)
    (unwind-protect
	 (with-open-file (stream (tuplekb-locator-pathname locator)
				 :direction :output)
	   (loop for fact in facts
		 do (format stream "FACT~%")
		    (if error-p
			(encode-data-structure-to-stream fact stream :portable)
			(let ((error-found-p nil))
			  (with-open-file (s temp-file-name :direction :output)
			    (multiple-value-bind (res err)
				(ignore-errors
				 (values (encode-data-structure-to-stream
					  fact s :portable)
					 nil))
			      (declare (ignore res))
			      (when err
				(setq error-found-p t))))
			  (when (not error-found-p)
			    (with-open-file
				(s temp-file-name :direction :input)
			      (loop for line = (read-line s nil :eof)
				    until (eq line :eof)
				    do (fast-write-string line stream)
				       (terpri stream))))))))
      (when temp-file-name
	(ignore-errors (delete-file temp-file-name))))
    t))

;(defmethod close-kb-internal ((kb tuple-kb) (save-p t))
;  (when save-p (save-kb-internal kb t))
;  (let ((locator (find-kb-locator-internal kb kb (connection kb))))
;    (put-instance-types-internal
;     locator nil (meta-kb-internal (connection kb)) t)
;    (put-instance-types-internal
;     kb nil (meta-kb-internal (connection kb)) t)
;    (setf (tuple-kb-tuple-store kb) :this-kb-has-been-closed)
;    (when (eq kb (current-kb)) (setq *current-kb* nil))))

(defmethod close-kb-internal :after ((kb tuple-kb) (save-p t))
	   (setf (tuple-kb-tuple-store kb) :this-kb-has-been-closed))

;(defmethod open-kb-internal
;    ((kb-locator t) (kb-type tuple-kb) (connection t) (error-p t))
;  (let ((locator (find-kb-locator-internal kb-locator kb-type connection)))
;    (let ((existing (find-kb-of-type-internal (name locator)
;                                              kb-type (local-connection))))
;      (with-open-file (stream (tuplekb-locator-pathname locator)
;                              :direction :input)
;        (let ((kb (or existing
;                      (create-kb-internal
;                       (name locator) kb-type locator nil
;                       (local-connection))))
;              (facts nil))
;          (catch :stop
;            (loop do
;                  ;; Synch first...
;                  (loop for line = (read-line stream nil :eof)
;                        when (eq line :eof) do (throw :stop :stop)
;                        when (string= "FACT" line)
;                        return t)
;                  ;; Now read and insert the fact
;                  (let ((fact
;                         (if error-p
;                             (decode-data-structure-from-stream
;                              stream :portable)
;                             (ignore-errors
;                              (decode-data-structure-from-stream
;                               stream :portable)))))
;                    (push fact facts))))
;          (loop for fact in facts
;                do (insert fact (tuple-kb-tuple-store kb) t))
;          kb)))))

(defmethod load-kb-from-file ((pathname t) (kb tuple-kb) (error-p t))
  (load-kb-from-file-in-format pathname kb error-p *tuplekb-file-format*))

(defmethod load-kb-from-file-in-format
     ((pathname t) (kb tuple-kb) (error-p t) (file-format (eql :lisp)))
  (with-open-file (stream pathname :direction :input)
    (let ((stream (underlying-stream stream :input)))
      (implement-with-kb-io-syntax-internal
       #'(lambda ()
	   (setf (name kb) (read stream))
	   (setf (unique-id kb) (read stream))
	   (setf (current-behaviors kb) (read stream))
	   (let ((package-list (read stream)))
	     (loop for (package-name export-list) on package-list by #'cddr
		   for package = (or (find-package package-name)
				     (make-package package-name))
		   do (loop for string in export-list
			    for sym = (intern string package)
			    do (export sym package))))
	   (let ((mapping-list (read stream))
		 (tuple-store::*register-tuple-store-side-effects-p* nil))
	     (declare (special
		       tuple-store::*register-tuple-store-side-effects-p*))
	     (let ((*symbol-stash-index-table*
		    (make-array (ceiling (length mapping-list) 2)))
		   (ok-back:*default-kb* kb)
		   (count 0))
	       (declare (special *symbol-stash-index-table*))
	       (loop for (symbol index) on mapping-list by #'cddr
		     do (setf (aref *symbol-stash-index-table*
				    (the fixnum index))
			      symbol))
	       (loop for fact = (read stream nil :eof)
		     until (eq fact :eof)
		     do (insert fact (tuple-kb-tuple-store kb) t nil)
		     (cond ((= (mod count 5000) 4999)
			    (fast-write-string "+" *standard-output*)
			    (fast-terpri *standard-output*))
			   ((= (mod count 100) 99)
			    (fast-write-string "." *standard-output*))
			   (t nil))
		     (incf count))))
	   (ok-cache:register-side-effect (tuple-kb-tuple-store kb) :load))
       kb :file t)))
  kb)

(defmethod load-kb-from-file-in-format
     ((pathname t) (kb tuple-kb) (error-p t) (file-format (eql :portable)))
  (with-open-file (stream pathname :direction :input)
    (let ((facts nil))
      (catch :stop
	(loop do
	      ;; Synch first...
	      (loop for line = (read-line stream nil :eof)
		    when (eq line :eof) do (throw :stop :stop)
		    when (string= "FACT" line)
		    return t)
	      ;; Now read and insert the fact
	      (let ((fact
		     (if error-p
			 (decode-data-structure-from-stream
			  stream :portable)
			 (ignore-errors
			  (decode-data-structure-from-stream
			   stream :portable)))))
		(push fact facts))))
      (loop for fact in facts
	    do (insert fact (tuple-kb-tuple-store kb) t))
      kb)))

(defmethod delete-frame-internal
    ((frame t) (kb tuple-kb) (kb-local-only-p t))
  (let ((frame (or (coerce-to-frame-internal frame kb nil kb-local-only-p)
		   frame)))
    (maybe-post-hoc-full-index-kb (tuple-kb-tuple-store kb))
    (let ((facts (facts-full-indexed-under frame (tuple-kb-tuple-store kb))))
      (loop for fact in facts
	    do (drop fact (tuple-kb-tuple-store kb) t
		     (check-included-kbs-p kb kb-local-only-p))))))

(defmethod ensure-has-facet
 (facet slot slot-type (kb tuple-kb) kb-local-only-p)
  (if (member facet *tuplekb-internal-facetlike-relations*)
      (values facet nil)
      (multiple-value-bind (real-facet found-p)
	     (coerce-to-facet-internal facet kb nil kb-local-only-p)
	(let ((facet-frame (facet-frame kb nil)))
	  (cond ((primitive-direct-instance-of-p real-facet facet-frame kb
						 kb-local-only-p)
		 real-facet)
		((primitive-direct-instance-of-p facet facet-frame kb
						 kb-local-only-p)
		 facet)
		(t (let ((new-facet
			  (create-facet-internal
			   (if found-p
			       (if (symbolp real-facet)
				   real-facet
				   (get-frame-name-internal
				    real-facet kb kb-local-only-p))
			       (if (symbolp facet) facet nil))
			   kb nil slot slot-type
			   nil nil nil nil
			   (if found-p
			       (if (symbolp real-facet) nil real-facet)
			       (if (symbolp facet) nil facet))
			   nil kb-local-only-p)))
		     (values new-facet :asserted-facet-p))))))))

(defmethod ensure-has-slot (slot slot-type (kb tuple-kb) kb-local-only-p)
  (if (member slot *tuplekb-internal-slotlike-relations*)
      (values slot nil)
      (multiple-value-bind (real-slot found-p)
	  (coerce-to-slot-internal slot kb nil kb-local-only-p)
	(when (not found-p) (setq real-slot slot))
	(let ((slot-frame (slot-frame kb nil)))
	  (cond ((primitive-direct-instance-of-p real-slot slot-frame kb
						 kb-local-only-p)
		 real-slot)
		((primitive-direct-instance-of-p slot slot-frame kb
						 kb-local-only-p)
		 slot)
		(t (let ((new-slot (create-slot-internal
				    (if found-p
					(if (symbolp real-slot)
					    real-slot
					    (get-frame-name-internal
					     real-slot kb kb-local-only-p))
					(if (symbolp slot) slot nil))
				    kb nil slot-type nil nil nil 
				    nil
				    (if found-p
					(if (symbolp real-slot) nil real-slot)
					(if (symbolp slot) nil slot))
				    nil kb-local-only-p)))
		     (values new-slot :asserted-slot-p))))))))


;==============================================================================
) ;;; END OF SUBSTITUTION GROUP !!!!!!
;------------------------------------------------------------------------------
;==============================================================================
;------------------------------------------------------------------------------

;==============================================================================

