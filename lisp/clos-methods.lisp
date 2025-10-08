(in-package :ok-kernel)

;==============================================================================

(defmethod get-frame-name-internal
  ((frame t) (kb ok-back:frame-name-interning-mixin)
   (kb-local-only-p t))
  (or (call-next-method frame kb kb-local-only-p)
      (let ((frame (or (coerce-to-frame-internal frame kb nil kb-local-only-p)
		       frame)))
	(if (symbolp frame)
	    frame
	    (let ((key (fast-hash-key frame)))
	      (or (gethash key (frame-name-mapping-table kb))
		  (let ((new (intern (format nil "~S" frame)
				     *frame-names-package*)))
		    (setf (gethash key (frame-name-mapping-table kb)) new)
		    (setf (gethash new (name-to-frame-mapping-table kb)) frame)
		    new)))))))

(defmethod coerce-to-frame-internal
  ((thing symbol) (kb ok-back:frame-name-interning-mixin) (error-p t)
   (kb-local-only-p t))
  (multiple-value-bind (frame found-p)
      (call-next-method thing kb nil kb-local-only-p)
    (if found-p
        (values frame found-p)
        (let ((frame? (gethash thing (name-to-frame-mapping-table kb))))
          (multiple-value-bind (frame found-p)
              (if frame?
                  (call-next-method frame? kb nil kb-local-only-p)
                  (values nil nil))
            (if found-p
                (values frame found-p)
                (let ((frame? (gethash thing (frame-name-mapping-table kb))))
                  (if frame?
                      (call-next-method frame? kb error-p kb-local-only-p)
                      (if error-p
                          (error 'okbc:not-coercible-to-frame
				 :frame thing :kb kb)
                          (values nil nil))))))))))

(defmethod delete-frame-internal :before
    ((frame t) (kb ok-back:frame-name-interning-mixin) (kb-local-only-p t))
    (let ((frame (or (coerce-to-frame-internal frame kb nil kb-local-only-p)
		     frame)))
      (when (not (symbolp frame))
	(let ((key (fast-hash-key frame)))
	  (let ((name (gethash key (frame-name-mapping-table kb))))
	    (when name (remhash key (frame-name-mapping-table kb)))
	    (remhash name (name-to-frame-mapping-table kb)))))))

(defmethod allocate-frame-handle-internal
  ((frame-name symbol) (frame-type t) (kb ok-back:frame-name-interning-mixin)
   (frame-handle t))
  (let ((frame? (gethash frame-name (name-to-frame-mapping-table kb))))
    (if frame?
	(get-frame-handle-internal frame? kb nil)
	(call-next-method))))

;==============================================================================

;;; In this class we globally define all symbols to be slot-p.  This is
;;; necessary because there is no global space of slots, so coerce-to-slot
;;; won't wotk without it.
(defmethod slot-p-internal
    ((thing symbol)
     (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin)
     (kb-local-only-p t))
  t)

(defmethod coerce-to-slot-internal
    ((thing symbol)
     (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin) (error-p t)
     (kb-local-only-p t))
  (multiple-value-bind (slot found-p)
      (call-next-method thing kb nil kb-local-only-p)
    (if found-p
	(values slot found-p)
	(values thing t))))

;;; The order in which we build up values is kinda arbitrary, and
;;; Some mixins will often return NIL as a slot value as a punt, so pick
;;; the first non-null value.
(defmethod get-slot-value-internal
  ((frame t) (slot symbol)
   (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin)
   (inference-level t) (slot-type t) (value-selector t) (kb-local-only-p t))
  (let ((values (get-slot-values-internal
		 frame slot kb inference-level slot-type :all value-selector
		 kb-local-only-p)))
    (when (rest values)
      (error 'cardinality-violation
	     :frame frame :slot slot :kb kb
	     :constraint "Single valued slot"
	     :error-message "Cardinality must be 1"))
    (values (loop for v in values
		  when v return v
		  finally (return nil))
	    t)))

(defmethod get-slot-values-in-detail-internal
  ((frame standard-object) (slot symbol)
   (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin)
   (inference-level t) (slot-type (eql :own)) (number-of-values t)
   (value-selector t) (kb-local-only-p t))
  (let ((local-values (ecase value-selector
			((:either :known-true)
			 (if (and (slot-exists-p frame slot)
				  (slot-boundp frame slot))
			     (list (slot-value frame slot))
			     nil))
			(:default-only nil))))
    (multiple-value-bind (values exact-p more-status default-p)
	(call-next-method frame slot kb inference-level slot-type
			  number-of-values
			  (if local-values :known-true value-selector)
			  kb-local-only-p)
	(values (append (loop for val in local-values collect (list val t nil))
			values)
		exact-p more-status
		(or (not (null local-values)) default-p)))))

(defmethod get-slot-values-in-detail-internal
  ((frame standard-class) (slot symbol)
   (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin)
   (inference-level t) (slot-type (eql :template)) (number-of-values t)
   (value-selector t) (kb-local-only-p t))
  (ecase value-selector
    ((:either :default-only)
     (multiple-value-bind (values exact-p more-status default-p)
       (call-next-method)
       (let ((local-values 
	      (ecase value-selector
		((:either :default-only)
		 (if (slot-exists-p (class-prototype-safe frame) slot)
		     (let ((slotd
			    (find-if #'(lambda (x)
					 (equal (slot-definition-name x)
						slot))
				     (clos:class-slots frame))))
		       (continuable-assert slotd slot-not-found
				   :frame frame :slot slot :slot-type slot-type
				   :kb kb)
		       (if (clos::slot-definition-initfunction slotd)
			   (list (clos:slot-definition-initform slotd))
			   nil))
		     nil))
		(:known-true nil))))
	 (values
	  (append (loop for val in local-values collect (list val t t)) values)
	  exact-p more-status (or (not (null local-values)) default-p)))))
    (:known-true (values nil t nil nil))))

(defmethod get-slot-values-in-detail-internal
  ((frame standard-class) (slot symbol)
   (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin)
   (inference-level t) (slot-type (eql :own)) (number-of-values t)
   (value-selector t) (kb-local-only-p t))
  (multiple-value-bind (values exact-p more-status default-p)
      (call-next-method)
    (let ((local-values 
	   (ecase value-selector
	     ((:either :known-true)
	      (if (and (slot-exists-p frame slot)
		       (slot-boundp frame slot))
		  (list (slot-value frame slot))
		  nil))
	     (:default-only nil))))
      (values
       (append (loop for val in local-values collect (list val t nil)) values)
       exact-p more-status (or (not (null local-values)) default-p)))))

(defmethod class-p-internal
    ((thing class) (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin)
     (kb-local-only-p t))
  t)

(defmethod get-class-superclasses-internal
  ((class class) (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin)
   (inference-level t) (number-of-values t) (kb-local-only-p t))
  (if (eq :direct inference-level)
      (multiple-value-bind (rest exact-p) (call-next-method)
	(values
	 (remove-duplicates
	  (append (clos:class-direct-superclasses class) rest)
	  :test (decanonicalize-testfn :eql kb kb-local-only-p))
	 exact-p nil))
      (call-next-method)))

(defmethod get-class-subclasses-internal
  ((class class) (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin)
   (inference-level t) (number-of-values t) (kb-local-only-p t))
  (if (eq :direct inference-level)
      (multiple-value-bind (rest exact-p more-status)
	  (call-next-method)
	(values
	 (remove-duplicates
	  (append (clos:class-direct-subclasses class) rest)
	  :test (decanonicalize-testfn :eql kb kb-local-only-p))
	 exact-p more-status))
      (call-next-method)))

(defmethod get-instance-types-internal
  ((frame standard-object)
   (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin)
   (inference-level t) (number-of-values t) (kb-local-only-p t))
  (if (eq :direct inference-level)
      (multiple-value-bind (rest exact-p more-status) (call-next-method)
	(values
	 (remove-duplicates (cons (class-of frame) rest)
			    :test (decanonicalize-testfn
				   :eql kb kb-local-only-p))
	 exact-p more-status))
      (call-next-method)))

(defmethod get-frame-slots-internal
  ((frame standard-object)
   (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin) (inference-level t)
   (slot-type (eql :own)) (kb-local-only-p t))
  (let ((clos-slots (if (typep frame 'standard-class)
			;;; standard-class is also a standard-object,
			;;; so we block here
			nil
			(if (eq :direct inference-level)
			    (mapcar #'slot-definition-name
				    (class-direct-slots (class-of frame)))
			    (mapcar #'slot-definition-name
				    (class-slots (class-of frame)))))))
    (multiple-value-bind (other-slots exact-p) (call-next-method)
      (values (remove-duplicates (append clos-slots other-slots)) exact-p))))

(defmethod get-frame-slots-internal
    ((frame standard-class)
     (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin)
     (inference-level t) (slot-type (eql :all)) (kb-local-only-p t))
  (let ((clos-slots
	 (if (eq :direct inference-level)
	     (mapcar #'slot-definition-name (class-direct-slots frame))
	     (append (mapcar #'slot-definition-name
			     (if (clos:class-finalized-p frame)
				 (class-slots frame)
				 (class-direct-slots frame)))
		     (mapcar #'slot-definition-name
			     (class-slots (class-of frame)))))))
    (multiple-value-bind (other-slots exact-p) (call-next-method)
      (values (remove-duplicates (append clos-slots other-slots)) exact-p))))

(defmethod get-frame-slots-internal
  ((frame standard-class)
   (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin) (inference-level t)
   (slot-type (eql :own)) (kb-local-only-p t))
  (let ((clos-slots
	 (macrolet ((all-slots ()
		      `(append (mapcar #'slot-definition-name
				(class-slots (class-of frame)))
			(loop for slotd in
			 (if (clos:class-finalized-p frame)
			     (class-slots frame)
			     (class-direct-slots frame))
			 when (eq (slot-definition-allocation slotd)
			       :class)
			 collect (slot-definition-name
				  slotd)))))
	   (if (eq :direct inference-level)
	       (mapcar #'slot-definition-name
		       (class-direct-slots (class-of frame)))
	       (all-slots)))))
    (multiple-value-bind (other-slots exact-p) (call-next-method)
      (values (remove-duplicates (append clos-slots other-slots)) exact-p))))

(defmethod get-frame-slots-internal
    ((frame standard-class)
     (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin)
     (inference-level t) (slot-type (eql :template)) (kb-local-only-p t))
  (let ((clos-slots (loop for slotd in
			  (if (clos:class-finalized-p frame)
			      (class-slots frame)
			      (class-direct-slots frame))
			  when (eq (slot-definition-allocation slotd)
				   :instance)
			  collect (slot-definition-name slotd))))
    (multiple-value-bind (other-slots exact-p) (call-next-method)
      (values (remove-duplicates (append clos-slots other-slots)) exact-p))))

(defmethod put-slot-values-internal
    ((frame standard-object) (slot symbol) (values t)
     (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin)
     (slot-type (eql :own)) (value-selector (eql :known-true))
     (kb-local-only-p t))
    (if (slot-exists-p frame slot)
	(progn (continuable-assert
		(<= (length values) 1) cardinality-violation
		:frame frame :slot slot
		:kb kb :error-message
		"CLOS instances can have at most one slot value.")
	       (if values
		   (setf (slot-value frame slot) (first values))
		   (slot-makunbound frame slot)))
	(call-next-method)))

(defmethod put-slot-values-internal
    ((frame standard-class) (slot symbol) (values t)
     (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin)
     (slot-type (eql :own)) (value-selector (eql :known-true))
     (kb-local-only-p t))
    (if (slot-exists-p frame slot)
	(progn (continuable-assert
		(<= (length values) 1) cardinality-violation
		:frame frame :slot slot
		:kb kb :error-message
		"CLOS instances can have at most one slot value.")
	       (if values
		   (setf (slot-value frame slot) (first values))
		   (slot-makunbound frame slot)))
	(call-next-method)))

(defmethod put-slot-values-internal
    ((frame standard-class) (slot symbol) (values t)
     (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin)
     (slot-type (eql :template)) (value-selector (eql :default-only))
     (kb-local-only-p t))
    (if (slot-exists-p (class-prototype-safe frame) slot)
	(progn (continuable-assert
		(<= (length values) 1) cardinality-violation
		:frame frame :slot slot
		:kb kb :error-message
		"CLOS instances can have at most one slot value.")
	       (let ((slotd
		      (find-if #'(lambda (x)
				   (equal (slot-definition-name x)
					  slot))
			       (clos:class-slots frame))))
		 (continuable-assert slotd slot-not-found
			     :frame frame :slot slot :slot-type slot-type
			     :kb kb)
		 (if values
		     (let ((value (first values)))
		       (setf #-(or EXCL Harlequin-Common-Lisp)
			     (clos::slot-definition-initfunction slotd)
			     #+(or EXCL Harlequin-Common-Lisp)
			     (slot-value slotd 'clos::initfunction)
			     #'(lambda () value)))
		     (setf #-(or EXCL Harlequin-Common-Lisp)
			   (clos::slot-definition-initfunction slotd)
			   #+(or EXCL Harlequin-Common-Lisp)
			   (slot-value slotd 'clos::initfunction)
			   nil))))
	(call-next-method)))

;==============================================================================

#+Lucid
(defun get-defstruct-slots (type-name)
  (declare (special lucid::*defstructs*))
  (let ((vect (let ((struct (gethash type-name lucid::*defstructs*)))
		(and struct
		     (lucid::structure-ref struct 7 (type-of struct))))))
    (cond (vect
	   (loop for elt being the array-elements of vect
		 for name = (lucid::structure-ref elt 0 (type-of elt))
		 collect name))
	  (t nil))))

#+Harlequin-Common-Lisp
(defun get-defstruct-slots (type-name)
  (let ((vect (let ((struct (get type-name
				 'structure::new-structure-definition)))
		(and struct (aref struct 11)))))
    (cond (vect
	   (loop for elt being the array-elements of vect
		 for name = (structure::dsd-name elt)
		 collect name))
	  (t nil))))

#+EXCL
;; This uses internal protocol.  Rewritten by BWM.
;(defun get-defstruct-slots (type-name)
;  (let ((descr (get type-name 'EXCL::%STRUCTURE-DEFINITION)))
;    (and descr
;         (loop for slot in (slot-value descr 'excl::slots)
;               collect (slot-value slot 'excl::name)))))
(defun get-defstruct-slots (type-name)  ; rewrite bwm
  (let ((class (clos::find-class type-name)))
    (and class
         (mapcar #'clos:slot-definition-name (clos:class-slots class)))))

#-(or Lucid EXCL Harlequin-Common-Lisp)
(cerror "Go ahead, anyway" "get-defstruct-slots not implemented")

#+(or lucid EXCL Harlequin-Common-Lisp)
(defmethod get-defstruct-slot (Name (class clos::class))
  (get-defstruct-slot name (class-name class)))

#+Lucid
(defmethod get-defstruct-slot (Name (type symbol))
  (declare (special lucid::*defstructs*))
  (let ((vect (let ((struct (gethash type lucid::*defstructs*)))
		(and struct
		     (lucid::structure-ref struct 7 (type-of struct))))))
    (cond (vect
	   (loop for elt being the array-elements of vect
		 when (eq Name (lucid::structure-ref elt 0 (type-of elt)))
		 return elt))
	  ((numberp name) name)
	  (t nil))))

#+Harlequin-Common-Lisp
(defmethod get-defstruct-slot (Name (type symbol))
  (let ((vect (let ((struct (get type 'structure::new-structure-definition)))
		(and struct (aref struct 11)))))
    (cond (vect
	   (loop for elt being the array-elements of vect
		 when (eq Name (structure::dsd-name elt))
		 return elt))
	  ((numberp name) name)
	  (t nil))))

#+EXCL
;; This uses internal protocol.  Rewritten by BWM.
;(defmethod get-defstruct-slot (Name (type symbol))
;  (let ((descr (get type 'EXCL::%STRUCTURE-DEFINITION)))
;    (and descr
;         (let ((slots (slot-value descr 'excl::slots)))
;           (loop for slot in slots
;                 when (eq name (slot-value slot 'excl::name))
;                 return slot)))))
(defmethod get-defstruct-slot (name (type symbol)) ; rewrite, bwm
  (let ((class (clos::find-class type)))
    (and class
         (find name (clos:class-slots class)
	       :key #'clos:slot-definition-name))))

#-(or EXCL Lucid Harlequin-Common-Lisp)
(cerror "Go ahead, anyway" "get-defstruct-slot not implemented")

(defmethod get-slot-values-in-detail-internal
  ((frame structure-class) (slot symbol)
   (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin)
   (inference-level t) (slot-type (eql :own)) (number-of-values t)
   (value-selector t) (kb-local-only-p t))
  (multiple-value-bind (values exact-p more-status default-p)
		       (call-next-method)
    (let ((local-values 
	   (ecase value-selector
	     ((:either :known-true)
	      (if (and (slot-exists-p frame slot)
		       (slot-boundp frame slot))
		  (list (slot-value frame slot))
		nil))
	     (:default-only nil))))
      (values
       (append (loop for val in local-values collect (list val t nil)) values)
       exact-p more-status (or (not (null local-values)) default-p)))))

(defmethod get-slot-values-in-detail-internal
  ((frame structure-class) (slot symbol)
   (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin)
   (inference-level t) (slot-type (eql :template)) (number-of-values t)
   (value-selector t) (kb-local-only-p t))
  (multiple-value-bind (values exact-p more-status default-p)
    (call-next-method)
    (let ((local-values
	   (ecase value-selector
	     ((:either :default-only)
	      (let ((slot-obj
		     (if (class-name frame);; anonymous class
			 (get-defstruct-slot slot (class-name frame))
		       nil)))
		(if slot-obj
		    #+Lucid
		  (list (eval (lucid::structure-ref
			       slot-obj 4 (type-of slot-obj))))
		  #+EXCL
		  (list (slot-value slot-obj 'excl::default))
		  #-(or EXCL Lucid) (generic-error "Implement me")
		  nil)))
	     (:known-true nil))))
      (values
       (append (loop for val in local-values collect (list val t t)) values)
       exact-p more-status (or (not (null local-values)) default-p)))))

(defmethod class-p-internal
    ((thing structure-class)
     (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin)
     (kb-local-only-p t))
  t)

(defmethod get-frame-slots-internal
    ((frame structure-class)
     (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin)
     (inference-level t) (slot-type (eql :all)) (kb-local-only-p t))
  (let ((clos-slots (append (get-defstruct-slots (class-name frame))
			    (mapcar #'slot-definition-name
				    (class-slots (class-of frame))))))
    (multiple-value-bind (other-slots exact-p) (call-next-method)
      (values (remove-duplicates (append clos-slots other-slots)) exact-p))))

(defmethod get-frame-slots-internal
    ((frame structure-class)
     (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin)
     (inference-level t) (slot-type (eql :template)) (kb-local-only-p t))
  (let ((defstruct-slots (get-defstruct-slots (class-name frame))))
    (multiple-value-bind (other-slots exact-p) (call-next-method)
      (values (remove-duplicates (append defstruct-slots other-slots))
	      exact-p))))

(defmethod get-frame-slots-internal
    ((frame structure-class)
     (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin)
     (inference-level t) (slot-type (eql :own)) (kb-local-only-p t))
  (let ((clos-slots
	 (macrolet
	     ((all-slots ()
		`(append (mapcar #'slot-definition-name
			  (class-slots (class-of frame)))
		  (loop for slotd in (class-slots frame)
		   when
		   (and #-excl t
			#+excl (compute-applicable-methods
				#'slot-definition-allocation
				(list slotd)) ; bwm an allegro bug?
			(eq (slot-definition-allocation slotd)
			    :class))
		   collect (slot-definition-name
			    slotd)))))
	   (if (eq :direct inference-level)
	       (mapcar #'slot-definition-name
		       (class-direct-slots (class-of frame)))
	       (all-slots)))))
    (multiple-value-bind (other-slots exact-p) (call-next-method)
      (values (remove-duplicates (append clos-slots other-slots)) exact-p))))

(defmethod put-slot-values-internal
    ((frame structure-class) (slot symbol) (values t)
     (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin)
     (slot-type (eql :own)) (value-selector (eql :known-true))
     (kb-local-only-p t))
    (if (slot-exists-p frame slot)
	(progn (continuable-assert
		(<= (length values) 1) cardinality-violation
		:frame frame :slot slot
		:kb kb :error-message
		"CLOS instances can have at most one slot value.")
	       (with-read-only-checking (kb)
		 (if values
		     (setf (slot-value frame slot) (first values))
		     (slot-makunbound frame slot))))
	(call-next-method)))

(defmethod put-slot-values-internal
    ((frame structure-class) (slot symbol) (values t)
     (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin)
     (slot-type (eql :template)) (value-selector (eql :default-only))
     (kb-local-only-p t))
  (let ((slot-obj
	 (if (class-name frame);; anonymous class
	     (get-defstruct-slot slot (class-name frame))
	     nil)))
    (if slot-obj
	(progn (continuable-assert
		(<= (length values) 1) cardinality-violation
		:frame frame :slot slot
		:kb kb :error-message
		"DEFSTRUCT instances can have at most one slot value.")
	       (with-read-only-checking (kb)
		 #-(or EXCL Lucid) (generic-error "Implement me")
		 #+EXCL (setf (slot-value slot-obj 'excl::default)
			      (if values (first values) nil))
		 #+Lucid
		 (setf (lucid::structure-ref slot-obj 4 (type-of slot-obj))
		       (list 'quote
			     (if values (first values) nil)))))
	(call-next-method))))

(defmethod get-slot-values-in-detail-internal
  ((frame structure-object) (slot symbol)
   (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin)
   (inference-level t) (slot-type (eql :own)) (number-of-values t)
   (value-selector t) (kb-local-only-p t))
  (let ((local-values
	 (ecase value-selector
	   ((:either :default-only)
	    (let ((slot-obj
		   (let ((cl (class-of frame)))
		     (if (or (not (class-name cl));; anonymous class
			     (eq (class-name cl) (type-of-name frame)))
			 (get-defstruct-slot slot cl)
			 (get-defstruct-slot slot (type-of-name frame))))))
	      (if slot-obj
		  #+Lucid
		  (let ((index (lucid::structure-ref
				slot-obj 1 (type-of slot-obj))))
		    (list (lucid::structure-ref
			   frame index (type-of frame))))
		  #+EXCL (list (slot-value frame slot))
		  #-(or EXCL Lucid) (generic-error "Implement me")
		  nil)))
	   (:known-true nil))))
    (multiple-value-bind (values exact-p more-status default-p)
	(call-next-method frame slot kb inference-level slot-type
			  number-of-values
			  (if local-values :known-true value-selector)
			  kb-local-only-p)
      (values
       (append (loop for val in local-values collect (list val t nil)) values)
       exact-p more-status (or (not (null local-values)) default-p)))))

(defmethod get-instance-types-internal
  ((frame structure-object)
   (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin)
   (inference-level t)(number-of-values t) (kb-local-only-p t))
  (if (eq :direct inference-level)
      (multiple-value-bind (rest exact-p more-status) (call-next-method)
	(values
	 (append (list (class-of frame)) rest)
	 exact-p more-status))
      (call-next-method)))

(defmethod get-frame-slots-internal
    ((frame structure-object)
     (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin)
     (inference-level t) (slot-type (eql :own)) (kb-local-only-p t))
  (let ((defstruct-slots (get-defstruct-slots (type-of-name frame))))
    (multiple-value-bind (other-slots exact-p) (call-next-method)
      (values (remove-duplicates (append defstruct-slots other-slots))
	      exact-p))))

(defmethod put-slot-values-internal
    ((frame structure-object) (slot symbol) (values t)
     (kb ok-back:frames-have-clos-slots-as-okbc-slots-mixin)
     (slot-type (eql :own)) (value-selector (eql :known-true))
     (kb-local-only-p t))
  (let ((slot-obj
	 (let ((cl (class-of frame)))
	   (if (or (not (class-name cl));; anonymous class
		   (eq (class-name cl) (type-of-name frame)))
	       (get-defstruct-slot slot cl)
	       (get-defstruct-slot slot (type-of-name frame))))))
    (with-read-only-checking (kb)
      (if slot-obj
	  (progn (continuable-assert
		  (<= (length values) 1) cardinality-violation
		  :frame frame :slot slot :kb kb
		  :error-message
		  "DEFSTRUCT instances can have at most one slot value.")
		 #+Lucid
		 (let ((index (lucid::structure-ref
			       slot-obj 1 (type-of slot-obj))))
		   (setf (lucid::structure-ref frame index (type-of frame))
			 (if values (first values) nil)))
		 #+EXCL (setf (slot-value frame slot) 
			      (if values (first values) nil))
		 #-(or EXCL Lucid) (generic-error "Implement me"))
	  (call-next-method)))))

;==============================================================================
;==============================================================================

(defokbcclass frame-forward-reference () ((name :initarg :name)))

(defmethod print-object ((instance frame-forward-reference) (stream t))
  (print-unreadable-object
   (instance stream :type t :identity t)
   (if (slot-boundp instance 'name)
       (ignore-errors (princ (slot-value instance 'name) stream))
       (princ "?????" stream))))

(defun coerce-to-clos-slot-name (slot kb kb-local-only-p)
  (coerce-clos-class-name
   (let ((slot-frame (coerce-to-frame-internal slot kb nil kb-local-only-p)))
     (if slot-frame
	 (get-frame-name-internal slot-frame kb kb-local-only-p)
	 (frame-forward-reference-name slot)))))

(defmethod frame-forward-reference-name ((instance t)) instance)

(defmethod frame-forward-reference-name ((instance frame-forward-reference))
  (slot-value instance 'name))

(defmethod get-frame-name-internal
  ((frame frame-forward-reference) (kb t) (kb-local-only-p t))
  (slot-value frame 'name))

(defmethod coerce-to-frame-internal 
  ((thing frame-forward-reference) (kb t) (error-p t) (kb-local-only-p t))
  (if error-p
      (error 'not-coercible-to-frame :frame thing :kb kb)
      nil))

(defun coerce-clos-class-name (frame-name)
  (if (keywordp frame-name)
      (intern (symbol-name frame-name) *frame-names-package*)
      frame-name))

(defmethod allocate-frame-handle-internal 
  ((frame-name t) (frame-type t) (kb ok-back:clos-only-okbc-mixin)
   (frame-handle t))
  (ecase frame-type
    (:class
     (let ((real-name (coerce-clos-class-name frame-name)))
       (or (find-class real-name nil)
	   (progn (eval `(defclass ,real-name (frame-forward-reference) ()))
		  (find-class real-name t)))))
    (:individual (make-instance 'frame-forward-reference
				:name frame-name))))

(defmethod get-instance-types-internal
    ((frame t) (kb ok-back:clos-only-okbc-mixin)
     (inference-level t) (number-of-values t) (kb-local-only-p t))
  (values nil t))

(defmethod primitive-p-internal
    ((class t) (kb ok-back:clos-only-okbc-mixin) (kb-local-only-p t))
  t)

(defmethod get-class-instances-internal
    ((class t) (kb ok-back:clos-only-okbc-mixin)
     (inference-level t) (number-of-values t) (kb-local-only-p t))
  ;;; We preserve the normal CLOS behavior of not tenuring the instances
  (values nil nil))

(defmethod get-class-superclasses-internal
    ((class t) (kb ok-back:clos-only-okbc-mixin)
     (inference-level t) (number-of-values t) (kb-local-only-p t))
  ;; This is taken care of by frames-have-clos-slots-as-okbc-slots-mixin!
  (values nil t))

(defmethod get-class-subclasses-internal
    ((class t) (kb ok-back:clos-only-okbc-mixin) (inference-level t)
     (number-of-values t) (kb-local-only-p t))
  (values nil t))

(defmethod class-p-internal
    ((thing t) (kb ok-back:clos-only-okbc-mixin) (kb-local-only-p t))
  nil)

(defmethod class-p-internal
    ((thing symbol) (kb ok-back:clos-only-okbc-mixin) (kb-local-only-p t))
  (let ((frame (coerce-to-frame-internal thing kb nil kb-local-only-p)))
    (and frame
	 (not (eq frame thing))
	 (class-p-internal frame kb kb-local-only-p))))

(defmethod facet-p-internal
    ((thing t) (kb ok-back:clos-only-okbc-mixin) (kb-local-only-p t))
  nil)

(defmethod slot-has-facet-p-internal
    ((frame t) (slot t) (facet t) (kb ok-back:clos-only-okbc-mixin)
     (inference-level t) (slot-type t) (kb-local-only-p t))
  nil)

(defmethod put-instance-types-internal
    ((frame t) (new-types t) (kb ok-back:clos-only-okbc-mixin)
     (kb-local-only-p t))
  (let ((new-types (if (listp new-types) new-types (list new-types)))
	(frame (or (coerce-to-frame-internal frame kb nil kb-local-only-p)
		   frame)))
    (continuable-assert (typep frame 'standard-object) not-coercible-to-frame
			:frame frame :kb kb
			:error-message (format nil "Illegal frame type for ~S"
					       frame))
    (continuable-assert
     (= (length new-types) 1) cardinality-violation
     :frame frame :slot nil
     :kb kb :error-message
     (format nil "CLOS KB instances can only have one direct type, ~
                             not ~S"
	     new-types))
    (when (not (typep frame (first new-types)))
      (change-class
       frame
       (if (symbolp (first new-types))
	   (find-class (coerce-clos-class-name (first new-types)))
	   (first new-types))))
    frame))

(defmethod close-kb-internal ((kb ok-back:clos-only-okbc-mixin) (save-p t))
  (when save-p (save-kb-internal kb t))
  (let ((locator (find-kb-locator-internal kb kb (connection kb))))
    (put-instance-types-internal
     locator nil (meta-kb-internal (connection kb)) t)
    (put-instance-types-internal
     kb nil (meta-kb-internal (connection kb)) t)
    (when (eq kb (current-kb)) (setq *current-kb* nil))))

(defmethod expunge-kb-internal
    ((kb-locator t) (kb-type ok-back:clos-only-okbc-mixin)
     (connection t) (error-p t))
  (when error-p (generic-error "Cannot expunge CLOS KBs using OKBC")))

(defmethod save-kb-internal ((kb ok-back:clos-only-okbc-mixin) (error-p t))
  (continuable-error "Cannot save CLOS KBs using OKBC"))

(defmethod revert-kb-internal ((kb ok-back:clos-only-okbc-mixin) (error-p t))
  (continuable-error "Cannot revert CLOS KBs using OKBC"))

(defmethod put-slot-values-internal
    ((frame t) (slot t) (values t) (kb ok-back:clos-only-okbc-mixin)
     (slot-type t)
     (value-selector t) (kb-local-only-p t))
  ;; This is handled by the
  ;; ok-back:frames-have-clos-slots-as-okbc-slots-mixin wrapper
  nil)

(defmethod put-facet-values-internal
    ((frame t) (slot t) (facet t) (values t) (kb ok-back:clos-only-okbc-mixin)
     (slot-type t) (value-selector t) (kb-local-only-p t))
  ;; This is handled by the
  ;; ok-back:frames-have-clos-slots-as-okbc-slots-mixin wrapper
  nil)

(defmethod create-facet-internal
    ((name t) (kb ok-back:clos-only-okbc-mixin) (frame-or-nil t)
     (slot-or-nil t)
     (slot-type t) (direct-types t) (doc t) (own-slots t) (own-facets t)
     (handle t) (pretty-name t) (kb-local-only-p t))
  ;; facets not supported in ok-back:clos-only-okbc-mixin
  nil)

(defmethod get-frame-slots-internal
    ((frame t) (kb ok-back:clos-only-okbc-mixin) (inference-level t)
     (slot-type t) (kb-local-only-p t))
  ;; This is handled by the
  ;; ok-back:frames-have-clos-slots-as-okbc-slots-mixin wrapper
  (values nil t))

(defmethod get-frame-slots-internal
    ((frame t) (kb ok-back:clos-only-okbc-mixin) (inference-level t)
     (slot-type (eql :all)) (kb-local-only-p t))
  (append
   (get-frame-slots-internal frame kb inference-level :own kb-local-only-p)
   (get-frame-slots-internal frame kb inference-level
			     :template kb-local-only-p)))

(defmethod get-frame-slots-internal
    ((frame symbol) (kb ok-back:clos-only-okbc-mixin) (inference-level t)
     (slot-type t) (kb-local-only-p t))
  (let ((frame (coerce-to-frame-internal frame kb nil kb-local-only-p)))
    (if (and frame (not (eq frame frame)))
	(get-frame-slots-internal frame kb inference-level slot-type
				  kb-local-only-p)
	(values nil t))))

(defmethod get-slot-facets-internal
    ((frame t) (slot t) (kb ok-back:clos-only-okbc-mixin) (inference-level t)
     (slot-type t) (kb-local-only-p t))
  ;; This is handled by the
  ;; ok-back:frames-have-clos-slots-as-okbc-slots-mixin wrapper
  (values nil t))

(defmethod get-slot-values-in-detail-internal
    ((frame t) (slot t) (kb ok-back:clos-only-okbc-mixin) (inference-level t)
     (slot-type t) (number-of-values t) (value-selector t) (kb-local-only-p t))
  (values nil t nil nil))

(defmethod get-slot-values-in-detail-internal
    ((frame symbol) (slot t) (kb ok-back:clos-only-okbc-mixin)
     (inference-level t) (slot-type t) (number-of-values t) (value-selector t)
     (kb-local-only-p t))
  (let ((frame (coerce-to-frame-internal frame kb nil kb-local-only-p)))
    (if (and frame (not (eq frame frame)))
	(get-slot-values-internal frame slot kb inference-level slot-type
				  number-of-values value-selector
				  kb-local-only-p)
	(values nil t nil nil))))

(defmethod get-facet-values-in-detail-internal
    ((frame t) (slot t) (facet t) (kb ok-back:clos-only-okbc-mixin)
     (inference-level t) (slot-type t) (number-of-values t) (value-selector t)
     (kb-local-only-p t))
  ;; This is handled by the
  ;; ok-back:frames-have-clos-slots-as-okbc-slots-mixin wrapper
  (values nil t nil))

(defmethod delete-slot-internal
    ((slot t) (kb ok-back:clos-only-okbc-mixin) (kb-local-only-p t))
  (continuable-error "You cannot globally delete slots in CLOS kbs"))

(defmethod delete-frame-internal
    ((frame t) (kb ok-back:clos-only-okbc-mixin) (kb-local-only-p t))
  (continuable-error "You cannot delete frames in pure CLOS kbs."))

(defmethod create-individual-internal
   ((name t) (kb ok-back:clos-only-okbc-mixin) (direct-types t) (doc t)
    (own-slots t) (own-facets t) (handle t) (pretty-name t)
    (kb-local-only-p t))
 (let ((direct-types
	(if (listp direct-types) direct-types (list direct-types))))
   (when (> (length direct-types) 1)
     (warn "CLOS KB instances can only have one direct type, not ~S.  ~
             Picking ~S"
	   direct-types (first direct-types)))
   (let ((frame (make-instance (or (first direct-types) 'standard-object))))
     (loop for (slot-name . slot-values) in own-slots
	   do (setf (slot-value frame slot-name) (first slot-values)))
     frame)))

(defmethod create-individual-internal :around
 ((name t) (kb ok-back:frame-name-interning-mixin) (direct-types t) (doc t)
  (own-slots t) (own-facets t) (handle t) (pretty-name t)
  (kb-local-only-p t))
 (let ((frame (call-next-method))
       (name (coerce-clos-class-name name)))
   (let ((key (fast-hash-key frame)))
     (when name
       (setf (gethash key (frame-name-mapping-table kb)) name)
       (setf (gethash name (name-to-frame-mapping-table kb)) frame))
     (when pretty-name
       (put-frame-pretty-name-internal
	frame pretty-name kb kb-local-only-p)))
   frame))

(defmethod create-class-internal
    ((name t) (kb ok-back:clos-only-okbc-mixin) (direct-types t)
     (direct-superclasses t) (primitive-p t) (doc t) (template-slots t)
     (template-facets t) (own-slots t) (own-facets t) (handle t)
     (pretty-name t) (kb-local-only-p t))
  (let ((direct-superclasses (mapcar 'coerce-clos-class-name
				     (if (listp direct-superclasses)
					 direct-superclasses
					 (list direct-superclasses))))
	(name (coerce-clos-class-name name)))
    (eval `(defclass
	    ,name
	    (,@direct-superclasses)
	    ,(append (loop for (slot . slot-values)
			   in template-slots
			   for slot-name
			   = (coerce-to-clos-slot-name slot kb kb-local-only-p)
			   do (continuable-assert
			       (and (symbolp slot-name) slot-name)
			       slot-not-found :frame name
			       :slot-type :template :slot slot-name)
			   collect
			   (list slot-name
				 :initform
				 (list 'quote (first slot-values))
				 :allocation :instance))
		     (loop for (slot . slot-values)
			   in own-slots
			   for slot-name
			   = (coerce-to-clos-slot-name slot kb kb-local-only-p)
			   do (continuable-assert
			       (and (symbolp slot-name) slot-name)
			       slot-not-found :frame name
			       :slot-type :own :slot slot-name)
			   collect
			   (list slot-name
				 :initform
				 (list 'quote (first slot-values))
				 :allocation :class)))
	    ,@(if doc `((:documentation ,doc)) nil)))
    (let ((frame (find-class name)))
      (when pretty-name
	(put-frame-pretty-name-internal
	 frame pretty-name kb kb-local-only-p))
      frame)))

(defmethod put-class-superclasses-internal
    ((class t) (new-superclasses t) (kb ok-back:clos-only-okbc-mixin)
     (kb-local-only-p t))
  (let ((class-frame (coerce-to-frame-internal class kb t kb-local-only-p))
	(new-superclasses (loop for s in (if (listp new-superclasses)
				       new-superclasses
				       (list new-superclasses))
			  for sclass = (coerce-to-frame-internal
					s kb t kb-local-only-p)
			  do (continuable-assert
			      (typep sclass 'class) not-coercible-to-frame
			      :frame sclass :kb kb
			      :error-message
			      "Superclasses of clos-kb classes ~
                               must be CLOS classes.")
			  collect sclass)))
    (reinitialize-instance
     class-frame
     :name (class-name class-frame)
     :direct-superclasses new-superclasses
     :direct-slots (clos::class-direct-slots class-frame))))

(defun generic-attach-slot-to-standard-class (name class slot-type kb)
  #+(or EXCL Lucid Harlequin-Common-Lisp) (declare (ignore kb))
  #+(or Lucid Harlequin-Common-Lisp)
  (add-slot-to-amop-class name class slot-type)
  #+EXCL (add-slot-to-excl-class name class slot-type)
  #-(or EXCL Lucid Harlequin-Common-Lisp)
  (error 'okbc:method-missing :kb kb :okbcop 'okbc:attach-slot))

(defmethod create-slot-internal
    ((name symbol) (kb ok-back:clos-only-okbc-mixin)
     (frame-or-nil standard-class)
     (slot-type t) (direct-types t) (doc t) (own-slots t)
     (own-facets t) (handle t) (pretty-name t) (kb-local-only-p t))
  (if (or (member name (get-frame-slots-internal frame-or-nil kb :all-inferable
						 :own kb-local-only-p))
	  (member name (get-frame-slots-internal frame-or-nil kb :all-inferable
						 :template kb-local-only-p)))
      (continuable-error "Slot ~S is already defined on class ~S"
			 name frame-or-nil)
      (generic-attach-slot-to-standard-class name frame-or-nil slot-type kb)))

#+EXCL
(defun add-slot-to-excl-class (name class-frame slot-type)
  (let ((new-slot-specs
	 (cons (list name :allocation
		     (case slot-type
		       (:template :instance)
		       (:own :class)))
	       (loop for s in (clos::class-direct-slots class-frame)
		     for source
		     = `(,(clos::slot-definition-name s)
			 ,@(when (slot-boundp s 'clos::initform)
				 (list :initform
				       (clos::slot-definition-initform s)))
			 :readers
			 ,(clos::slot-definition-readers s)
			 :writers
			 ,(clos::slot-definition-writers s)
			 :initargs
			 ,(clos::slot-definition-initargs s)
			 :allocation
			 ,(clos::slot-definition-allocation s))
		     collect source))))
    (reinitialize-instance
     class-frame
     :name (class-name class-frame)
     :direct-slots (loop for s in (clos::canonicalize-dslots class-frame
				   new-slot-specs)
			 collect (eval s))
     :direct-superclasses (clos::class-direct-superclasses class-frame))))

#+Lucid
(defun add-slot-to-amop-class (name class-frame slot-type)
  (let ((new-slot-spec
	 ;; (LIST (QUOTE (:NAME NEW-TEMPLATE-SLOT :ALLOCATION :INSTANCE)))
	 (let ((slot-spec (list (list name :allocation
				      (case slot-type
					(:template :instance)
					(:own :class))))))
	   (second (second (clos::canonicalize-direct-slots slot-spec))))))
    (reinitialize-instance
     class-frame
     :name (class-name class-frame)
     :direct-slots (cons new-slot-spec
			 (clos::class-direct-slots class-frame))
     :direct-superclasses (clos::class-direct-superclasses class-frame))))

#+Harlequin-Common-Lisp
(defun add-slot-to-amop-class (name class-frame slot-type)
  (let ((new-slot-spec
	 ;; (LIST (QUOTE (:NAME NEW-TEMPLATE-SLOT :ALLOCATION :INSTANCE)))
	 (let ((slot-spec (list class-frame (list name :allocation
						  (case slot-type
						    (:template :instance)
						    (:own :class))))))
	   (eval (first (clos::canonicalize-defclass-slot slot-spec))))))
    (reinitialize-instance
     class-frame
     :name (class-name class-frame)
     :direct-slots (cons new-slot-spec
			 (clos::class-direct-slots class-frame))
     :direct-superclasses (clos::class-direct-superclasses class-frame))))

(defmethod create-slot-internal
    ((name t) (kb ok-back:clos-only-okbc-mixin) (frame-or-nil symbol)
     (slot-type t) (direct-types t) (doc t) (own-slots t) (own-facets t)
     (handle t) (pretty-name t) (kb-local-only-p t))
  (let ((frame (coerce-to-frame-internal frame-or-nil kb nil kb-local-only-p)))
    (if (and frame (not (eq frame name)))
	(create-slot-internal name kb frame slot-type direct-types
			      doc own-slots own-facets handle pretty-name
			      kb-local-only-p)
	nil)))

(defmethod create-slot-internal
    ((name t) (kb ok-back:clos-only-okbc-mixin) (frame-or-nil t) (slot-type t)
     (direct-types t) (doc t) (own-slots t) (own-facets t) (handle t)
     (pretty-name t) (kb-local-only-p t))
  nil)

(defmethod get-frame-name-internal
    ((frame t) (kb ok-back:clos-only-okbc-mixin) (kb-local-only-p t))
  nil)

(defmethod get-frame-name-internal
    ((frame class) (kb ok-back:clos-only-okbc-mixin) (kb-local-only-p t))
  (let ((name (class-name frame)))
    (if (and name (symbolp name))
	name
	(call-next-method))))

(defmethod coerce-to-frame-internal
    ((thing symbol) (kb ok-back:clos-only-okbc-mixin) (error-p t)
     (kb-local-only-p t))
  (let ((class (find-class (coerce-clos-class-name thing) nil)))
    (if (and class (not (subtypep class 'frame-forward-reference)))
	(values class t)
	(if error-p
	    (error 'not-coercible-to-frame :kb kb :frame thing)
	    nil))))

(defmethod coerce-to-frame-internal
    ((thing standard-object) (kb ok-back:clos-only-okbc-mixin) (error-p t)
     (kb-local-only-p t))
  (values thing t))

(defmethod coerce-to-frame-internal
    ((thing t) (kb ok-back:clos-only-okbc-mixin) (error-p t)
     (kb-local-only-p t))
  (if error-p
      (error 'not-coercible-to-frame :kb kb :frame thing)
      (values nil nil)))

(defmethod get-frame-in-kb-internal
    ((thing t) (kb ok-back:clos-only-okbc-mixin) (error-p t)
     (kb-local-only-p t))
  (coerce-to-frame-internal thing kb error-p kb-local-only-p))

(defmethod get-kb-frames-internal
    ((kb ok-back:clos-only-okbc-mixin) (kb-local-only-p t))
  (append (get-kb-classes-internal kb :frames kb-local-only-p)
	  (get-kb-individuals-internal kb :frames kb-local-only-p)))

(defun get-all-clos-classes (class ht)
  (or (gethash class ht)
      (unless #+excl (eq (clos::class-name class) 'structure-object) #-excl nil
        (progn (setf (gethash class ht) t)
               (loop for sub in (class-direct-subclasses class)
		   do (get-all-clos-classes sub ht))))))

(defvar *clos-kb-roots*  '(standard-object structure-object))
 
(defmethod get-kb-roots-internal
    ((kb ok-back:clos-only-okbc-mixin) (selector t) (kb-local-only-p t))
  (mapcar #'find-class *clos-kb-roots*))

(defmethod get-kb-classes-internal
    ((kb ok-back:clos-only-okbc-mixin) (selector t) (kb-local-only-p t))
  (let ((ht (make-hash-table :test #'eq))
	(result nil))
    (get-all-clos-classes (find-class t) ht)
    (maphash #'(lambda (k v) (declare (ignore v)) (push k result)) ht)
    result))

(defmethod get-kb-individuals-internal
    ((kb ok-back:clos-only-okbc-mixin) (selector t) (kb-local-only-p t))
  nil)

(defmethod get-kbs-of-type-internal
    ((kb-type ok-back:clos-only-okbc-mixin) (connection t))
  (let ((meta-kb (meta-kb-internal connection)))
    (ok-back:relation-transitive-closure
     (class-of kb-type) meta-kb
     #'tuple-kb::get-class-instances-internal-implementation
     (list meta-kb :direct :all t)
     #'get-class-subclasses-internal
     (list meta-kb :direct :all t)
     t)))

(defparameter *clos-supported-back-end-behaviors*
  '((:constraint-checking-time :never)
    (:constraint-report-time :immediate)
    (:constraints-checked)
    (:defaults :override)
    (:compliance :read-only :monotonic)
    (:class-slot-types :template :own)
    (:collection-types :none)
    (:frame-names-required nil)
    (:are-frames :class :individual :instance)))

(defmethod get-behavior-values-internal
    ((behavior t) (kb ok-back:clos-only-okbc-mixin))
  (rest (assoc behavior *clos-supported-back-end-behaviors*)))

(defmethod get-behavior-supported-values-internal
    ((behavior t) (kb ok-back:clos-only-okbc-mixin))
  (rest (assoc behavior *clos-supported-back-end-behaviors*)))

(defmethod get-kb-behaviors-internal
    ((kb-type-or-kb ok-back:clos-only-okbc-mixin) (connection t))
  (mapcar #'first *clos-supported-back-end-behaviors*))

(defmethod delete-facet-internal
    ((facet t) (kb ok-back:clos-only-okbc-mixin) (kb-local-only-p t))
  (error 'okbc:method-missing :kb kb :okbcop 'okbc:delete-facet))

(defmethod attach-slot-internal
    (frame slot (kb ok-back:clos-only-okbc-mixin) (slot-type t)
	   (kb-local-only-p t))
  (let ((class (coerce-to-class-internal frame kb t kb-local-only-p)))
    (attach-slot-internal class slot kb slot-type kb-local-only-p)))

(defmethod attach-slot-internal
    ((frame structure-class) (slot t) (kb ok-back:clos-only-okbc-mixin)
     (slot-type t) (kb-local-only-p t))
  (error 'okbc:method-missing :kb kb :okbcop 'okbc:attach-slot))

(defmethod attach-slot-internal ((frame standard-class) (slot symbol)
				 (kb ok-back:clos-only-okbc-mixin) (slot-type t)
				 (kb-local-only-p t))
  (generic-attach-slot-to-standard-class slot frame slot-type kb))

(defmethod detach-slot-internal
    ((frame t) (slot t) (kb ok-back:clos-only-okbc-mixin) (slot-type t)
     (kb-local-only-p t))
  (error 'okbc:method-missing :kb kb :okbcop 'okbc:detach-slot))

(defmethod attach-facet-internal
    ((frame t) (slot t) (facet t) (kb ok-back:clos-only-okbc-mixin)
     (slot-type t) (kb-local-only-p t))
  (error 'okbc:method-missing :kb kb :okbcop 'okbc:attach-facet))

(defmethod detach-facet-internal
    ((frame t) (slot t) (facet t) (kb ok-back:clos-only-okbc-mixin)
     (slot-type t) (kb-local-only-p t))
  (error 'okbc:method-missing :kb kb :okbcop 'okbc:detach-facet))

(defmethod get-frame-pretty-name-internal
   ((frame t) (kb ok-back:clos-only-okbc-mixin) (kb-local-only-p t))
 (let ((frame (coerce-to-frame-internal frame kb t kb-local-only-p)))
   (implement-with-kb-io-syntax-internal
    #'(lambda () (princ-to-string frame)) kb :user-interface kb-local-only-p)))

(defmethods get-frame-pretty-name-internal
   ((frame (standard-class structure-class)) (kb ok-back:clos-only-okbc-mixin)
    (kb-local-only-p t))
  (let ((cn (class-name frame)))
    (typecase cn
      ((or string symbol) (string cn))
      (null (call-next-method))
      (otherwise
       (implement-with-kb-io-syntax-internal
	#'(lambda () (princ-to-string cn))
	kb :user-interface kb-local-only-p)))))

(defmethod put-frame-pretty-name-internal
    ((frame t) (name t) (kb ok-back:clos-only-okbc-mixin) (kb-local-only-p t))
  (warn "Cannot put the pretty name of clos frames!")
  nil)

(defmethod put-frame-name-internal
    ((frame t) (new-name t) (kb ok-back:clos-only-okbc-mixin)
     (kb-local-only-p t))
  (error 'okbc:method-missing :kb kb :okbcop 'okbc:put-frame-name))

(defmethods put-frame-name-internal
    ((frame (standard-class structure-class)) (new-name t)
     (kb ok-back:clos-only-okbc-mixin) (kb-local-only-p t))
  (let ((coerced-name (typecase new-name
			(symbol new-name)
			(string
			 (implement-with-kb-io-syntax-internal
			  #'(lambda () (intern new-name *package*))
			  kb :file kb-local-only-p))
			(otherwise
			 (implement-with-kb-io-syntax-internal
			  #'(lambda ()
			      (intern (princ-to-string new-name) *package*))
			  kb :file kb-local-only-p)))))
    (setf (class-name frame) coerced-name)))

(defmethod rename-slot-internal ((slot t) (new-name t)
				  (kb ok-back:clos-only-okbc-mixin)
				  (kb-local-only-p t))
  (error 'okbc:method-missing :kb kb :okbcop 'okbc:rename-slot))

(defmethod rename-facet-internal ((facet t) (new-name t)
				   (kb ok-back:clos-only-okbc-mixin)
				   (kb-local-only-p t))
  (error 'okbc:method-missing :kb kb :okbcop 'okbc:rename-facet))

(defmethod openable-kbs-internal ((kb-type ok-back:clos-only-okbc-mixin)
				   (connection t) (place t))
  nil)

(defmethod open-kb-internal
    ((kb-locator t) (kb-type ok-back:clos-only-okbc-mixin) (connection t)
     (error-p t))
  (error 'okbc:method-missing :kb kb-type :okbcop 'okbc:open-kb))

(defmethod put-behavior-values-internal
    ((behavior t) (values t) (kb ok-back:clos-only-okbc-mixin))
  (error 'okbc:illegal-behavior-values
	 :behavior behavior :proposed-values values))

(defmethod save-kb-as-internal ((new-name-or-locator t)
				(kb ok-back:clos-only-okbc-mixin))
  (error 'okbc:method-missing :kb kb :okbcop 'okbc:save-kb-as))

(defmethod slot-p-internal
    ((thing t) (kb ok-back:clos-only-okbc-mixin) (kb-local-only-p t))
  nil)

(defmethod decontextualize-internal
    ((value t) (from-context t) (kb ok-back:clos-only-okbc-mixin))
  (ok-back:decontextualize-aux value from-context kb))

(defmethods decontextualize-aux
    ((value (kb structure-kb procedure frame-handle)) (from-context t)
     (kb ok-back:clos-only-okbc-mixin))
  value)

(defmethods decontextualize-aux
    ((value (standard-object standard-class
	     structure-class structure-object))
     (from-context t) (kb ok-back:clos-only-okbc-mixin))
  (ok-back:frs-independent-frame-handle-internal value kb nil))

(defstruct (clos-kb-locator (:include ok-back:abstract-kb-locator)))

(defmethod create-kb-locator-internal ((thing clos-kb) (kb-type clos-kb)
				       (connection t))
  (let ((instance (make-clos-kb-locator
		   :name (name thing)
		   :kb-type kb-type)))
    (put-instance-types-internal instance :kb-locator
				 (meta-kb-internal connection) t)
    instance))

(defmethod find-kb-locator-internal
    ((thing clos-kb) (kb-type clos-kb) (connection t))
  (let ((locators (get-class-instances-internal
		   :kb-locator (meta-kb-internal connection)
		   :taxonomic :all nil)))
    (loop for locator in locators
	  when (and (typep locator 'clos-kb-locator)
		    (eq (name locator) (name thing)))
	  return locator
	  finally (return (create-kb-locator-internal
			   thing kb-type connection)))))

(defmethods abstract-kb-class-name-from-kb ((instance clos-kb))
  (intern (concatenate 'string "ABSTRACT-"
		       (symbol-name (type-of-name instance))
		       "-KB")
	  :ok-back))

(defmethods concrete-kb-class-from-abstract-kb-class-name
    ((name (eql 'ok-back::abstract-clos-kb-kb)))
  'clos-kb)

(defmethod shared-initialize :after
 ((kb clos-kb) (slot-names t) &rest inits &key (parent-kbs nil))
 (declare (ignore inits))
 (when parent-kbs
   (warn "KBs of type CLOS-KB do not understand the :parent-kbs initarg")))


;==============================================================================

(defmethod delete-frame-internal :before
  ((frame t) (kb ok-back:instance-recording-clos-kb) (kb-local-only-p t))
  (let ((frame (or (coerce-to-frame-internal frame kb nil kb-local-only-p)
		   frame)))
    (setf (recorded-instances kb) (remove frame (recorded-instances frame)))))

(defmethod delete-frame-internal
    ((frame t) (kb ok-back:instance-recording-clos-kb) (kb-local-only-p t))
  nil)

(defmethod get-class-instances-internal
    ((class symbol) (kb ok-back:instance-recording-clos-kb)
     (inference-level (eql :direct)) (number-of-values t) (kb-local-only-p t))
  (let ((class (find-class (coerce-clos-class-name class) nil)))
    (if class
	(get-class-instances-internal class kb :direct number-of-values
				kb-local-only-p)
	(error 'not-coercible-to-frame :kb kb :frame class))))

(defmethod get-class-instances-internal
    ((class class) (kb ok-back:instance-recording-clos-kb)
     (inference-level (eql :direct)) (number-of-values t) (kb-local-only-p t))
  (values
   (loop for instance in (recorded-instances kb)
	 when (eq class (class-of instance))
	 collect class)
   t nil))

(defmethod coerce-to-frame-internal
    ((thing t) (kb ok-back:instance-recording-clos-kb) (error-p t)
     (kb-local-only-p t))
  (or (loop for instance in (recorded-instances kb)
	    when (or (eq thing instance)
		     (eq thing (get-frame-name-internal instance kb
							kb-local-only-p)))
	    return (values instance t))
      (if error-p
	  (error 'not-coercible-to-frame :kb kb :frame thing)
	  nil)))

(defmethod get-kb-individuals-internal
    ((kb ok-back:instance-recording-clos-kb) (selector t) (kb-local-only-p t))
  (copy-list (recorded-instances kb)))


(defmethods abstract-kb-class-name-from-kb
    ((instance ok-back:instance-recording-clos-kb))
  (intern (concatenate 'string "ABSTRACT-" (symbol-name (type-of-name instance))
		       "-KB")
	  :ok-back))

(defmethods concrete-kb-class-from-abstract-kb-class-name
    ((name (eql 'ok-back::abstract-instance-recording-clos-kb-kb)))
  'ok-back:instance-recording-clos-kb)

;==============================================================================

;==============================================================================

