(in-package :ok-kernel)

(defun member-transitive-closure-p
    (test-frame frame kb relation-fn inference-level number-of-values
		kb-local-only-p)
  (ok-utils:without-recursion-in-stack
   (member-transitive-closure-p frame nil)
   (let ((elements (funcall relation-fn frame kb inference-level
			    number-of-values kb-local-only-p)))
     (if (member-frame-list test-frame elements kb kb-local-only-p)
	 (values t t)
	 (let ((inexact-p nil))
	   (values (loop with res = nil
			 with exact-p = nil
			 for x in elements
			 when (not (eq frame x));; detect trivial circularities
			 do (multiple-value-setq
				(res exact-p)
			      (member-transitive-closure-p
			       test-frame x kb relation-fn inference-level
			       number-of-values kb-local-only-p))
			 when (not exact-p) do (setq inexact-p t)
			 thereis res)
		   (not inexact-p)))))))

(defvar *visited-table*)

(defun relation-transitive-closure (frame kb relation-fn rel-fn-restargs
					  &optional (link-fn relation-fn)
					  (link-fn-restargs rel-fn-restargs)
					  call kb-local-only-p)
  "Computes the transitive closure of values by starting at <code>frame</code>
   and applying <code>(relation-fn frame . relation-fn-restargs)</code> to
   get the values.  The transitive closure it computed by following links
   identified by applying <code>(link-fn frame . link-fn-restargs)</code>.
   <code>Call</code> is a flag, which is <code>:recursive</code> when we enter
   this function recursively."
  (macrolet
      ((doit ()
	 `(progn (multiple-value-bind (res exact-p)
		     (apply relation-fn frame rel-fn-restargs)
		   (when (not exact-p) (setq *inexact-p* t))
		   (loop for x in res
			 do (unless (gethash x *closure-table*) t
				    (push x *closure*)
				    (setf (gethash x *closure-table*) t))))
	   (multiple-value-bind (res exact-p)
	       (apply link-fn frame link-fn-restargs)
	     (when (not exact-p) (setq *inexact-p* t))
	     (loop for y in res
		   do (if (gethash y *visited-table*)
			  nil
			  (relation-transitive-closure
			   (or (coerce-to-frame-internal
				y kb nil kb-local-only-p) y)
			   kb relation-fn rel-fn-restargs link-fn
			   link-fn-restargs :recursive kb-local-only-p)))))))
    (cond ((eq :recursive call)
	   ;; Record that we have visited this guy to prevent cycles.
	   (setf (gethash frame *visited-table*) t)
	   (multiple-value-bind (real-frame found-p)
	     (coerce-to-frame-internal frame kb nil kb-local-only-p)
	     (if found-p
		 (setf (gethash (get-frame-handle-internal
				 real-frame kb kb-local-only-p)
				*visited-table*)
		       t)
		 nil))
	   (doit))
	  (t (let ((*closure* nil)
		   (*inexact-p* nil)
		   (*closure-table* (allocate-closure-table))
		   (*visited-table* (allocate-closure-table)))
	       ;;In the initial version of this function, a new hashtable was
	       ;;created or each non-recursive call.  That was found to be
	       ;;much slower than re-using the same table, and clearing it as
	       ;;being done now.  VKC 1/3/96.
	       ;; JPR:  Yes, but this is not thread-safe, so changed to
	       ;; something less consy, but thread-safe.  Note: clrhash can
	       ;; be expensive on some lisp implementations, so the clrhash
	       ;; trick may not be a global optimisation anyway.
	       
	       ;; Record that we have visited this guy to prevent cycles.
	       (setf (gethash frame *visited-table*) t)
	       (multiple-value-bind (real-frame found-p)
		 (coerce-to-frame-internal frame kb nil kb-local-only-p)
		 (if found-p
		     (setf (gethash (get-frame-handle-internal
				     real-frame kb kb-local-only-p)
				    *visited-table*)
			   t)
		     nil))
	       (doit)
	       (deallocate-closure-table *closure-table*)
	       (deallocate-closure-table *visited-table*)
	       (values *closure* (not *inexact-p*)))))))

(defvar *count*)

(defun limited-relation-transitive-closure
    (frame kb number-of-values relation-fn rel-fn-restargs
	   &optional (link-fn relation-fn)
	   (link-fn-restargs rel-fn-restargs)
	   call kb-local-only-p)
  (if (eq number-of-values :all)
      (relation-transitive-closure frame kb relation-fn rel-fn-restargs
				   link-fn link-fn-restargs call
				   kb-local-only-p)
      (macrolet
	  ((doit ()
	     `(progn (multiple-value-bind (res exact-p)
		       (apply relation-fn frame rel-fn-restargs)
		       (when (not exact-p) (setq *inexact-p* t))
		       (loop for x in res
			     do (unless (gethash x *closure-table*) t
					(push x *closure*)
					(incf *count*)
					(when (>= *count* number-of-values)
					  (return nil))
					(setf (gethash x *closure-table*) t))))
	       (when (< *count* number-of-values)
		 (multiple-value-bind (res exact-p)
		   (apply link-fn frame link-fn-restargs)
		   (when (not exact-p) (setq *inexact-p* t))
		   (loop for y in res
			 do (if (gethash y *visited-table*)
				nil
				(limited-relation-transitive-closure
				 (or (coerce-to-frame-internal
				      y kb nil kb-local-only-p) y)
				 kb number-of-values relation-fn
				 rel-fn-restargs link-fn
				 link-fn-restargs :recursive
				 kb-local-only-p))))))))
	(cond ((eq :recursive call)
	       ;; Record that we have visited this guy to prevent cycles.
	       (setf (gethash frame *visited-table*) t)
	       (multiple-value-bind (real-frame found-p)
		 (coerce-to-frame-internal frame kb nil kb-local-only-p)
		 (if found-p
		     (setf (gethash (get-frame-handle-internal
				     real-frame kb kb-local-only-p)
				    *visited-table*)
			   t)
		     nil))
	       (doit))
	      (t (let ((*closure* nil)
		       (*inexact-p* nil)
		       (*count* 0)
		       (*closure-table* (allocate-closure-table))
		       (*visited-table* (allocate-closure-table)))
		   (setf (gethash frame *visited-table*) t)
		   (multiple-value-bind (real-frame found-p)
		     (coerce-to-frame-internal frame kb nil kb-local-only-p)
		     (if found-p
			 (setf (gethash (get-frame-handle-internal
					 real-frame kb kb-local-only-p)
					*visited-table*)
			       t)
			 nil))
		   (doit)
		   (deallocate-closure-table *closure-table*)
		   (deallocate-closure-table *visited-table*)
		   (values *closure* (not *inexact-p*)
			   (if (>= *count* number-of-values)
			       :more
			       nil))))))))

;==============================================================================

;;; Now define the methods for default inheritance.

;==============================================================================
;;; First for Slots

(defokbcgeneric directly-get-frame-slots
    (frame kb overall-inference-level slot-type kb-local-only-p)
  (:documentation "A generic function that provides a hook into OKBC's default
   inheritance scheme.  This generic function is called during the inherited
   computation of okbc:get-frame-slots for each class encountered.
   <code>overall-inference-level</code> is the inference level that was used
   in the outermost call to <code>okbc:get-frame-slots</code>.  This is
   useful because, for example, you might want to perform inferences on
   slot domains at higher inference levels.  You may not want to handle these
   in the <code>:direct</code> method for
   <code>ok-back:get-slot-values-internal</code> because this is more than
   just a direct inference."))

(defmethod directly-get-frame-slots
    (frame (kb t) (overall-inference-level t) slot-type kb-local-only-p)
  (get-frame-slots-internal frame kb :direct slot-type kb-local-only-p))


(defun maybe-coerce-to-frame-fun (kb kb-local-only-p)
  #'(lambda (x)
      (multiple-value-bind (frame found-p)
	  (coerce-to-frame-internal x kb nil kb-local-only-p)
	(if found-p
	    frame
	    x))))

(defun get-inherited-slots (frame kb inference-level slot-type kb-local-only-p)
  (let ((class-p (class-p-internal frame kb kb-local-only-p))
	(inexact-p nil))
    (let ((all
	   (remove-duplicates-using-trie-and-coercion
	    (append (if class-p
			(if (member slot-type '(:template :all))
			    (multiple-value-bind (superclasses exact-p)
				(get-class-superclasses-internal
				 frame kb inference-level :all
				 kb-local-only-p)
			      (when (not exact-p) (setq inexact-p t))
			      (loop with slots = nil
				    with exact-p = nil
				    for class in superclasses
				    for frame-p = (not (eql-in-kb-internal
							class frame kb
							kb-local-only-p))
				    ;; Be safe
				    when frame-p
				    do (multiple-value-setq (slots exact-p)
					 (directly-get-frame-slots
					  class kb inference-level :template
					  kb-local-only-p))
				    (when (not exact-p) (setq inexact-p t))
				    when frame-p append slots))
			    nil)
			nil)
		    (if (member slot-type '(:own :all))
			;; Then we inherit the own slots from the
			;; template slots on the classes of which
			;; we are an instance.
			(multiple-value-bind (types exact-p)
			  (get-instance-types-internal
			   frame kb inference-level :all
			   kb-local-only-p)
			  (when (not exact-p) (setq inexact-p t))
			  (loop with slots = nil
				with exact-p = nil
				for class in types
				for frame-p = (not (eql-in-kb-internal
						    class frame kb
						    kb-local-only-p))
				;; Be safe
				when frame-p
				do (multiple-value-setq (slots exact-p)
				     (directly-get-frame-slots
				      class kb inference-level :template
				      kb-local-only-p))
				(when (not exact-p) (setq inexact-p t))
				when frame-p append slots))
			nil)
		    (multiple-value-bind (slots exact-p)
			(directly-get-frame-slots
			 frame kb inference-level slot-type kb-local-only-p)
		      (when (not exact-p) (setq inexact-p t))
		      slots))
	    (maybe-coerce-to-frame-fun kb kb-local-only-p))))
      (values all (not inexact-p)))))

(defun inherited-specs (specs)
  (loop for spec in specs
	for (value direct-p default-p) = spec
	collect (if direct-p
		    (list value nil default-p)
		    spec)))

(defun default-inheritance-for-gsv/gfv-default-only-1
    (frame slot facet kb inference-level slot-type number-of-values 
	   value-selector kb-local-only-p closure-table facet-op-p)
  (if (gethash frame closure-table)
      (values nil t nil nil)
      (let ((class-p (class-p-internal frame kb kb-local-only-p))
	    (inexact-p nil))
	(setf (gethash frame closure-table) t) ;; without recursion
	(multiple-value-bind 
	 (local-values exact-p more-status default-found-p)
	    (if facet-op-p
		(get-direct-facet-values-in-detail
		 frame slot facet kb inference-level slot-type
		 number-of-values value-selector
		 kb-local-only-p)
		(get-direct-slot-values-in-detail
		 frame slot kb inference-level slot-type
		 number-of-values value-selector
		 kb-local-only-p))
	 (declare (ignore more-status))
	 (when (not exact-p) (setq inexact-p t))
	 (values
	  (remove-duplicates-using-trie-and-coercion
	   (append
	    (if (or default-found-p
		    (loop for spec in local-values thereis (third spec)))
		nil
		(append
		 (if class-p
		     (if (member slot-type '(:template :all))
			 (multiple-value-bind
			     (superclasses exact-p)
			   ;; ignore default-found-p flag here so that we
			   ;; can go on to other paths.
			   (get-class-superclasses-internal
			    frame kb :direct :all
			    kb-local-only-p)
			   (when (not exact-p) (setq inexact-p t))
			   (loop with values = nil
				 with exact-p = nil
				 for class in superclasses
				 for frame-p = (not (eql-in-kb-internal
						     class frame kb
						     kb-local-only-p))
				 ;; Be safe
				 when frame-p
				 do (multiple-value-bind (class-frame found-p)
				      (coerce-to-class-internal
				       class kb nil kb-local-only-p)
				      (if found-p
					  (multiple-value-setq
					      (values exact-p)
					    (default-inheritance-for-gsv/gfv-default-only-1
						class-frame slot facet kb
						inference-level :template
						number-of-values value-selector
						kb-local-only-p closure-table
						facet-op-p))
					  (progn (setq values nil)
						 (setq exact-p nil))))
				 (when (not exact-p) (setq inexact-p t))
				 when frame-p append (inherited-specs values)
				 until values))
			 nil)
		     nil)
		 (if (member slot-type '(:own :all))
		     ;; Then we inherit the own slots from the template
		     ;; slots on the classes of which we are an instance.
		     (multiple-value-bind 
			 (types exact-p)
		       (get-instance-types-internal
			frame kb :direct :all kb-local-only-p)
		       (when (not exact-p) (setq inexact-p t))
		       (loop
			with values = nil
			with exact-p = nil
			for class in types
			for frame-p = (not (eql-in-kb-internal
					    class frame kb
					    kb-local-only-p))
			;; Be safe
			when frame-p
			do
			(multiple-value-bind (class-frame found-p)
			  (coerce-to-class-internal
			   class kb nil kb-local-only-p)
			  (if found-p
			      (multiple-value-setq
				  (values exact-p)
				(default-inheritance-for-gsv/gfv-default-only-1
				    class-frame slot facet kb inference-level
				    :template number-of-values value-selector
				    kb-local-only-p closure-table facet-op-p))
			      (progn (setq values nil)
				     (setq exact-p nil))))
			(when (not exact-p) (setq inexact-p t))
			when frame-p append (inherited-specs values)
			until values))
		     nil)))
	    local-values)
	   (maybe-coerce-to-frame-fun kb kb-local-only-p))
	  (not inexact-p)
	  nil
	  t)))))

(defun default-inheritance-for-gsv-default-only-1
  (frame slot kb inference-level slot-type number-of-values value-selector
	 kb-local-only-p closure-table)
  (default-inheritance-for-gsv/gfv-default-only-1
    frame slot nil kb inference-level slot-type number-of-values 
    value-selector kb-local-only-p closure-table nil))

(defun default-inheritance-for-gfv-default-only-1
  (frame slot facet kb inference-level slot-type number-of-values 
	 value-selector kb-local-only-p closure-table)
  (default-inheritance-for-gsv/gfv-default-only-1
    frame slot facet kb inference-level slot-type number-of-values 
    value-selector kb-local-only-p closure-table t))

(defun default-inheritance-for-gsv-default-only
  (frame slot kb inference-level slot-type number-of-values value-selector
	 kb-local-only-p)
  (let ((closure-table nil))
    (unwind-protect
	(progn (setq closure-table (allocate-closure-table))
	       (default-inheritance-for-gsv-default-only-1
		 frame slot kb inference-level slot-type number-of-values 
		 value-selector kb-local-only-p closure-table))
      (deallocate-closure-table closure-table))))

(defun default-inheritance-for-gfv-default-only
  (frame slot facet kb inference-level slot-type number-of-values 
	 value-selector kb-local-only-p)
  (let ((closure-table nil))
    (unwind-protect
	(progn (setq closure-table (allocate-closure-table))
	       (default-inheritance-for-gfv-default-only-1
		 frame slot facet kb inference-level slot-type 
		 number-of-values value-selector kb-local-only-p
		 closure-table))
      (deallocate-closure-table closure-table))))

(defun basic-default-inheritance-gsv/gfv-known-true-only
    (frame slot facet kb inference-level slot-type number-of-values 
	 value-selector kb-local-only-p facet-op-p)
  (let ((class-p (class-p-internal frame kb kb-local-only-p))
	(inexact-p nil))
    (multiple-value-bind 
     (local-values exact-p)
	(if facet-op-p
	    (get-direct-facet-values-in-detail
	     frame slot facet kb inference-level slot-type
	     number-of-values value-selector kb-local-only-p)
	    (get-direct-slot-values-in-detail
	     frame slot kb inference-level slot-type
	     number-of-values value-selector kb-local-only-p))
     (when (not exact-p) (setq inexact-p t))
     (values
      (remove-duplicates-using-trie-and-coercion
       (append
	(if class-p
	    (if (member slot-type '(:template :all))
		(multiple-value-bind
		 (superclasses exact-p)
		 (get-class-superclasses-internal
		  frame kb inference-level :all
		  kb-local-only-p)
		 (when (not exact-p) (setq inexact-p t))
		 (loop with values = nil
		       with exact-p = nil
		       for class in superclasses
		       for frame-p = (not (eql-in-kb-internal
					   class frame kb
					   kb-local-only-p))
		       ;; Be safe
		       when frame-p
		       do (multiple-value-bind (class-frame found-p)
			    (coerce-to-class-internal
			     class kb nil kb-local-only-p)
			    (if found-p
				(multiple-value-setq
				    (values exact-p)
				  (if facet-op-p
				      (get-direct-facet-values-in-detail
				       class-frame slot facet kb
				       inference-level :template
				       number-of-values value-selector
				       kb-local-only-p)
				      (get-direct-slot-values-in-detail
				       class-frame slot kb inference-level
				       :template number-of-values
				       value-selector kb-local-only-p)))
				(progn (setq values nil)
				       (setq exact-p nil))))
		       (when (not exact-p) (setq inexact-p t))
		       when frame-p append (inherited-specs values)))
	      nil)
	    nil)
	(if (member slot-type '(:own :all))
	    ;; Then we inherit the own slots from the template
	    ;; slots on the classes of which we are an instance.
	    (multiple-value-bind 
		(types exact-p)
	      (get-instance-types-internal
	       frame kb inference-level :all kb-local-only-p)
	      (when (not exact-p) (setq inexact-p t))
	      (loop with values = nil
		    with exact-p = nil
		    for class in types
		    for frame-p = (not (eql-in-kb-internal
					class frame kb
					kb-local-only-p))
		    ;; Be safe
		    when frame-p
		    do (multiple-value-bind (class-frame found-p)
			 (coerce-to-class-internal
			  class kb nil kb-local-only-p)
			 (if found-p
			     (multiple-value-setq
				 (values exact-p)
			       (if facet-op-p
				   (get-direct-facet-values-in-detail
				    class-frame slot facet kb inference-level
				    :template
				    number-of-values value-selector
				    kb-local-only-p)
				   (get-direct-slot-values-in-detail
				    class-frame slot kb inference-level
				    :template number-of-values value-selector
				    kb-local-only-p)))
			     (progn (setq values nil)
				    (setq exact-p nil))))
		    (when (not exact-p) (setq inexact-p t))
		    when frame-p append (inherited-specs values)))
	    nil)
	local-values)
       (maybe-coerce-to-frame-fun kb kb-local-only-p))
      (not inexact-p)
      nil
      nil))))

(defun basic-default-inheritance-gsv-known-true-only
    (frame slot kb inference-level slot-type number-of-values value-selector
	   kb-local-only-p)
  (basic-default-inheritance-gsv/gfv-known-true-only
   frame slot nil kb inference-level slot-type number-of-values 
   value-selector kb-local-only-p nil))

(defun basic-default-inheritance-gfv-known-true-only
  (frame slot facet kb inference-level slot-type number-of-values 
	 value-selector kb-local-only-p)
  (basic-default-inheritance-gsv/gfv-known-true-only
   frame slot facet kb inference-level slot-type number-of-values 
   value-selector kb-local-only-p t))

(defmacro basic-default-inheritance-shfp/fhsp
    (predicate-function-name (frame &rest initial-args))
  `(let ((predicate-value
	  (,predicate-function-name ,frame ,@initial-args kb :direct slot-type
				    kb-local-only-p)))
    (or predicate-value
     (let ((class-p (class-p-internal frame kb kb-local-only-p)))
       (if class-p
	   (if (member slot-type '(:template :all) :test #'eq)
	       (let ((superclasses
		      (get-class-superclasses-internal
		       ,frame kb inference-level :all
		       kb-local-only-p)))
		 (loop for super in superclasses
		       for frame-p = (not (eql-in-kb-internal super ,frame kb
							      kb-local-only-p))
		       ;; Be safe
		       thereis (and frame-p
				    (coercible-to-frame-p-internal
				     super kb kb-local-only-p)
				    (,predicate-function-name
				     super ,@initial-args kb :direct :template
				     kb-local-only-p))))
	       nil)
	   (if (member slot-type '(:own :all) :test #'eq)
	       ;; Then we inherit the own slots from the template
	       ;; slots on the classes of which we are an instance.
	       (let ((types (get-instance-types-internal
			     ,frame kb inference-level :all kb-local-only-p)))
		 (loop for class in types
		       for frame-p = (not (eql-in-kb-internal class ,frame kb
							      kb-local-only-p))
		       ;; Be safe
		       thereis (and frame-p
				    (coercible-to-frame-p-internal
				     class kb kb-local-only-p)
				    (,predicate-function-name
				     class ,@initial-args kb :direct :template
				     kb-local-only-p))))
	       nil))))))

(defun basic-default-inheritance-fhsp
    (frame slot kb inference-level slot-type kb-local-only-p)
  (basic-default-inheritance-shfp/fhsp
   frame-has-slot-p-internal (frame slot)))

(defun basic-default-inheritance-shfp
  (frame slot facet kb inference-level slot-type kb-local-only-p)
  (basic-default-inheritance-shfp/fhsp
   slot-has-facet-p-internal (frame slot facet)))

(defokbcgeneric ok-utils:get-direct-slot-values-in-detail
    (frame slot kb overall-inference-level slot-type
	   number-of-values value-selector kb-local-only-p)
  (:documentation "An internal hook used in the default inheritance code.
   It is called whenever a direct slot value is being fetched and gives access
   to the overall inference level that the user specified."))

(defmethod get-direct-slot-values-in-detail
    (frame slot kb (overall-inference-level t) slot-type
	   number-of-values value-selector kb-local-only-p)
  (get-slot-values-in-detail-internal
   frame slot kb :direct slot-type number-of-values 
   value-selector kb-local-only-p))

(defmethod get-direct-facet-values-in-detail
    (frame slot facet kb (overall-inference-level t) slot-type
	   number-of-values value-selector kb-local-only-p)
  (get-facet-values-in-detail-internal
   frame slot facet kb :direct slot-type number-of-values 
   value-selector kb-local-only-p))

(defun default-inheritance-gsv/gfv-either-class
  (frame slot facet kb inference-level slot-type number-of-values
         value-selector kb-local-only-p facet-op-p)
   (let ((inexact-p nil)
	 (vals nil)
	 (exact-p nil)
	 (more-status nil)
	 (found-this-call-p nil)
	 (default-p nil)
	 (all-values nil)
	 (defaults nil)
	 (default-found-p nil))
    (values
     (remove-duplicates-using-trie-and-coercion
      (cond ((member slot-type '(:template :all))
	     (multiple-value-setq (all-values exact-p)
	       (if facet-op-p
		   (get-direct-facet-values-in-detail
		    frame slot facet kb inference-level slot-type
		    number-of-values :known-true
		    kb-local-only-p)
		   (get-direct-slot-values-in-detail
		    frame slot kb inference-level slot-type
		    number-of-values :known-true
		    kb-local-only-p)))
	     (multiple-value-bind
		   (parents exact-p)
		 (get-class-superclasses-internal
		  frame kb :direct :all kb-local-only-p)
	       (when (not exact-p) (setq inexact-p t))
	       (loop for class in parents
		     for frame-p = (not (eql-in-kb-internal
					 class frame kb kb-local-only-p))
		     ;; Be safe
		     when frame-p
		     do (multiple-value-bind (class-frame found-p)
			  (coerce-to-class-internal
			   class kb nil kb-local-only-p)
			  (if found-p
			      (multiple-value-setq 
				  (vals exact-p more-status default-p)
				(if facet-op-p
				    (get-facet-values-in-detail-internal
				     class-frame slot facet kb inference-level
				     :template number-of-values
				     (if all-values :known-true value-selector)
				     kb-local-only-p)
				    (get-slot-values-in-detail-internal
				     class-frame slot kb inference-level
				     :template number-of-values 
				     (if all-values :known-true value-selector)
				     kb-local-only-p)))
			      (progn (setq vals nil)
				     (setq exact-p nil))))
		     (when (not exact-p) (setq inexact-p t))
		     when frame-p
		     do (cond (default-p 
				  (setq default-found-p t)
				  (setq defaults (inherited-specs vals)))
			      (t (setq all-values 
				       (append (inherited-specs vals)
					       all-values))))))
	     (when (not all-values)
	       (multiple-value-setq
		   (vals exact-p more-status found-this-call-p)
		 (if facet-op-p
		     (get-direct-facet-values-in-detail
		      frame slot facet kb inference-level
		      slot-type number-of-values
		      :default-only
		      kb-local-only-p)
		   (get-direct-slot-values-in-detail
		    frame slot kb inference-level
		    slot-type number-of-values
		    :default-only
		    kb-local-only-p)))
	       (when (not exact-p) (setq inexact-p t))
	       (when (or found-this-call-p
			 (loop for spec in vals thereis (third spec)))
		 (setq defaults vals)
		 (setq default-found-p t)))
	     (or all-values
		 (and default-found-p defaults)))
	    (t nil))
      (maybe-coerce-to-frame-fun kb kb-local-only-p))
     (not inexact-p)
     nil
     (and (not all-values) default-found-p)
     more-status)))


(defun default-inheritance-gsv-either-class
  (frame slot kb inference-level slot-type number-of-values value-selector
	 kb-local-only-p)
  (default-inheritance-gsv/gfv-either-class
    frame slot nil kb inference-level slot-type number-of-values
    value-selector kb-local-only-p nil))

(defun default-inheritance-gfv-either-class
  (frame slot facet kb inference-level slot-type number-of-values 
	 value-selector kb-local-only-p)
  (default-inheritance-gsv/gfv-either-class
    frame slot facet kb inference-level slot-type number-of-values
    value-selector kb-local-only-p t))

(defun default-inheritance-gsv/gfv-either-individual
  (frame slot facet kb inference-level slot-type number-of-values
         value-selector kb-local-only-p facet-op-p)
  (let ((inexact-p nil)
	(vals nil)
	(more-status nil)
	(found-p nil)
	(default-p nil)
	(all-values nil)
	(defaults nil)
	(default-found-p nil))
    (values
     (remove-duplicates-using-trie-and-coercion
      (cond ((member slot-type '(:own :all))
	     (multiple-value-bind (vals exact-p)
		 (if facet-op-p
		     (get-direct-facet-values-in-detail
		      frame slot facet kb inference-level slot-type
		      number-of-values :known-true kb-local-only-p)
		     (get-direct-slot-values-in-detail
		      frame slot kb inference-level slot-type
		      number-of-values :known-true kb-local-only-p))
	       (setq all-values vals)
	       (when (not exact-p) (setq inexact-p t)))
	     ;; Then we inherit the own slots from the template
	     ;; slots on the classes of which we are an instance.
	     (multiple-value-bind
	      (types exact-p)
	      (get-instance-types-internal
	       frame kb :direct :all kb-local-only-p)
	       (when (not exact-p) (setq inexact-p t))
	      (loop for class in types
		    for frame-p = (not (eql-in-kb-internal
					class frame kb
					kb-local-only-p))
		    ;; Be safe
		    when frame-p
		    do (multiple-value-bind (class-frame found-p)
			 (coerce-to-class-internal
			  class kb nil kb-local-only-p)
			 (if found-p
			     (multiple-value-setq
				 (vals exact-p more-status default-p)
			       (if facet-op-p
				   (get-facet-values-in-detail-internal
				    class-frame slot facet kb inference-level
				    :template number-of-values 
				    (if all-values :known-true value-selector)
				    kb-local-only-p)
				   (get-slot-values-in-detail-internal
				    class-frame slot kb inference-level
				    :template number-of-values 
				    (if all-values :known-true value-selector)
				    kb-local-only-p)))
			     (progn (setq vals nil)
				    (setq exact-p nil))))
		    (when (not exact-p) (setq inexact-p t))
		    when frame-p
		    do (cond ((or default-p
				  (loop for spec in vals thereis (third spec)))
			       (setq default-found-p t)
			       (setq defaults (inherited-specs vals)))
			     (t (setq all-values 
				      (append (inherited-specs vals)
					      all-values)))))
	      (when (not all-values)
		    (multiple-value-setq (vals exact-p more-status found-p)
		      (if facet-op-p
			  (get-direct-facet-values-in-detail
			   frame slot facet kb inference-level
			   slot-type number-of-values
			   :default-only kb-local-only-p)
			  (get-direct-slot-values-in-detail
			   frame slot kb inference-level
			   slot-type number-of-values
			   :default-only kb-local-only-p)))
		    (when (not exact-p) (setq inexact-p t))
		    (when (or found-p
			      (loop for spec in vals thereis (third spec)))
			  (setq defaults vals)
			  (setq default-found-p t)))
	      (or all-values
		  (and default-found-p defaults)))))
      (maybe-coerce-to-frame-fun kb kb-local-only-p))
     (not inexact-p)
     nil
     (and (not all-values) default-found-p)
     more-status)))

(defun default-inheritance-gsv-either-individual
    (frame slot kb inference-level slot-type number-of-values value-selector
	   kb-local-only-p)
  (default-inheritance-gsv/gfv-either-individual
      frame slot nil kb inference-level slot-type number-of-values
      value-selector kb-local-only-p nil))

(defun default-inheritance-gfv-either-individual
    (frame slot facet kb inference-level slot-type number-of-values 
	   value-selector kb-local-only-p)
  (default-inheritance-gsv/gfv-either-individual
      frame slot facet kb inference-level slot-type number-of-values
      value-selector kb-local-only-p t))

(defun default-inheritance-gsv-either
  (frame slot kb inference-level slot-type number-of-values value-selector
	 kb-local-only-p)
  (let ((class-p (class-p-internal frame kb kb-local-only-p)))
    (if (and class-p (eq slot-type :template))
	(default-inheritance-gsv-either-class
	  frame slot kb inference-level slot-type number-of-values
	  value-selector kb-local-only-p)
	(default-inheritance-gsv-either-individual
	  frame slot kb inference-level slot-type number-of-values
	  value-selector kb-local-only-p))))

(defun default-inheritance-gfv-either
  (frame slot facet kb inference-level slot-type number-of-values 
	 value-selector kb-local-only-p)
  (let ((class-p (class-p-internal frame kb kb-local-only-p)))
    (if (and class-p (eq slot-type :template))
	(default-inheritance-gfv-either-class
	  frame slot facet kb inference-level slot-type number-of-values
	  value-selector kb-local-only-p)
	(default-inheritance-gfv-either-individual
	  frame slot facet kb inference-level slot-type number-of-values
	  value-selector kb-local-only-p))))


(defun get-inherited-frames-with-slot-or-facet-value-known-true
    (slot facet value kb inference-level slot-type value-selector
	  kb-local-only-p facet-op-p)
  (let ((inexact-p nil))
    (multiple-value-bind (local-matches exact-p)
	(if facet-op-p
	    (get-frames-with-facet-value-internal
	     slot facet value kb :direct slot-type value-selector
	     kb-local-only-p)
	    (get-frames-with-slot-value-internal
	     slot value kb :direct slot-type value-selector kb-local-only-p))
      (when (not exact-p) (setq inexact-p t))
      (let ((all
	     (remove-duplicates-using-trie-and-coercion
	      (append local-matches
		      (loop for frame in local-matches
			    for class-p = (class-p-internal
					   frame kb kb-local-only-p)
			    append
			    (if class-p
				(if (member slot-type '(:template :all))
				    (append
				     (if (eq slot-type :all)
					 (multiple-value-bind
					       (instances exact-p)
					     (get-class-instances-internal
					      frame kb inference-level :all
					      kb-local-only-p)
					   (when (not exact-p)
					     (setq inexact-p t))
					   instances)
					 nil)
				     (multiple-value-bind
					   (subclasses exact-p)
					 (get-class-subclasses-internal
					  frame kb inference-level :all
					  kb-local-only-p)
				       (when (not exact-p)
					 (setq inexact-p t))
				       subclasses)))
				nil)))
	      (maybe-coerce-to-frame-fun kb kb-local-only-p))))
	(if (eq :own slot-type)
	    ;; Step up to classes and look down.
	    (multiple-value-bind (local-matches exact-p)
		(if facet-op-p
		    (get-frames-with-facet-value-internal
		     slot facet value kb :direct :template value-selector
		     kb-local-only-p)
		    (get-frames-with-slot-value-internal
		     slot value kb :direct :template value-selector
		     kb-local-only-p))
	      (when (not exact-p) (setq inexact-p t))
	      (let ((all-own
		     (remove-duplicates-using-trie-and-coercion
		      (append all
			      (loop for frame in local-matches
				    ;; the frames are all classes because they
				    ;; have SLOT as a template slot.
				    append
				    (multiple-value-bind (instances exact-p)
					(get-class-instances-internal
					 frame kb inference-level :all
					 kb-local-only-p)
				      (when (not exact-p)
					(setq inexact-p t))
				      instances)))
		      (maybe-coerce-to-frame-fun kb kb-local-only-p))))
		(values all-own (not inexact-p))))
	    (values all (not inexact-p)))))))

(defun check-down-until-blocked
    (frame slot facet value kb inference-level slot-type value-selector
	   kb-local-only-p facet-op-p)
  (without-recursion-in-stack
   (check-down-until-blocked frame (values nil nil))
   (multiple-value-bind (member-p member-exact-p)
     (member-slot-or-facet-value-p
      frame slot facet value kb inference-level slot-type value-selector
      kb-local-only-p facet-op-p)
     (let ((inexact-p nil))
       (values
	(if member-p
	    (cons frame
		  (let ((class-p (class-p-internal frame kb kb-local-only-p)))
		    (if class-p
			(if (member slot-type '(:template :all))
			    (append
			     (if (eq slot-type :all)
				 (multiple-value-bind
				     (instances exact-p)
				   (get-class-instances-internal
				    frame kb :direct :all
				    kb-local-only-p)
				   (when (not exact-p)
				     (setq inexact-p t))
				   (loop with res = nil
					 with exact-p = nil
					 for instance in instances
					 do (multiple-value-setq
						(res exact-p)
					      (check-down-until-blocked
					       instance slot facet value kb
					       inference-level
					       :own value-selector
					       kb-local-only-p facet-op-p))
					 when (not exact-p)
					 do (setq inexact-p t)
					 append res))
				 nil)
			     (multiple-value-bind
				 (subclasses exact-p)
			       (get-class-subclasses-internal
				frame kb inference-level :all
				kb-local-only-p)
			       (when (not exact-p)
				 (setq inexact-p t))
			       (loop with res = nil
				     with exact-p = nil
				     for subclass in subclasses
				     do (multiple-value-setq
					    (res exact-p)
					  (check-down-until-blocked
					   subclass slot facet value kb
					   inference-level
					   slot-type value-selector
					   kb-local-only-p facet-op-p))
				     when (not exact-p)
				     do (setq inexact-p t)
				     append res))))
			nil)))
	    nil)
	(and member-exact-p (not inexact-p)))))))
  
(defun get-frames-with-slot-or-facet-value-default-or-either
    (slot facet value kb inference-level slot-type value-selector
	  kb-local-only-p facet-op-p)
  (let ((inexact-p nil))
    (multiple-value-bind (local-matches exact-p)
	(if facet-op-p
	    (get-frames-with-facet-value-internal
	     slot facet value kb :direct slot-type value-selector
	     kb-local-only-p)
	    (get-frames-with-slot-value-internal
	     slot value kb :direct slot-type value-selector kb-local-only-p))
      (when (not exact-p) (setq inexact-p t))
	(let ((all (append local-matches
			   (loop with res = nil
				 with exact-p = nil
				 for frame in local-matches
				 do (multiple-value-setq (res exact-p)
				      (check-down-until-blocked
				       frame slot facet value kb
				       inference-level slot-type value-selector
				       kb-local-only-p facet-op-p))
				 when (not exact-p) do (setq inexact-p t)
				 append res))))
	  (if (eq :own slot-type)
	      ;; Step up to classes and look down.
	      (multiple-value-bind (local-matches exact-p)
		  (if facet-op-p
		      (get-frames-with-facet-value-internal
		       slot facet value kb :direct :template value-selector
		       kb-local-only-p)
		      (get-frames-with-slot-value-internal
		       slot value kb :direct :template value-selector
		       kb-local-only-p))
		(when (not exact-p) (setq inexact-p t))
		(let ((all-own
		       (append
			all
			(loop for frame in local-matches
			      ;; the frames are all classes because they
			      ;; have SLOT as a template slot.
			      append
			      (multiple-value-bind (instances exact-p)
				  (get-class-instances-internal
				   frame kb inference-level :all
				   kb-local-only-p)
				(when (not exact-p)
				  (setq inexact-p t))
				(loop with member-p = nil
				      for i in instances
				      do (multiple-value-setq
					     (member-p exact-p)
					   (member-slot-or-facet-value-p
					    i slot facet value kb
					    inference-level slot-type
					    value-selector kb-local-only-p
					    facet-op-p))
				      when (and member-p (not exact-p))
				      do (setq inexact-p t)
				      when member-p
				      collect i))))))
		  (values (remove-duplicates-using-trie-and-coercion
			   all-own
			   (maybe-coerce-to-frame-fun kb kb-local-only-p))
			  (not inexact-p))))
	      (values (remove-duplicates-using-trie-and-coercion
		       all
		       (maybe-coerce-to-frame-fun kb kb-local-only-p))
		      (not inexact-p)))))))

(defun member-slot-or-facet-value-p
    (frame slot facet value kb inference-level slot-type value-selector
	   kb-local-only-p facet-op-p)
  (if (eq :all slot-type)
      (multiple-value-bind (res exact-p)
			   (member-slot-or-facet-value-p
			    frame slot facet value kb inference-level :own
			    value-selector kb-local-only-p facet-op-p)
	  (if res
	      (values res exact-p)
	      (if (class-p-internal frame kb kb-local-only-p)
		  (multiple-value-bind (res2 exact-p2)
                     (member-slot-or-facet-value-p
		      frame slot facet value kb inference-level :template
		      value-selector kb-local-only-p facet-op-p)
		    (values res2 (and exact-p exact-p2)))
		  (values nil exact-p))))
      (if facet-op-p
	  (member-facet-value-p-internal
	   frame slot facet value kb inference-level :equal slot-type
	   value-selector kb-local-only-p)
	  (member-slot-value-p-internal
	   frame slot value kb inference-level :equal slot-type value-selector
	   kb-local-only-p))))

(defmethods default-direct-get-frames-with-slot-value
    (slot value (kb (kb structure-kb)) (inference-level t)
	  (slot-type t) (value-selector t) (kb-local-only-p t))
  (let ((inexact-p nil)
	(frames nil))
    (loop for frame in (get-kb-frames-internal kb kb-local-only-p)
	  when (frame-has-slot-p-internal frame slot kb inference-level
					  slot-type kb-local-only-p)
	  do (multiple-value-bind (res exact-p)
		 (member-slot-or-facet-value-p
		  frame slot nil value kb inference-level slot-type
		  value-selector kb-local-only-p nil)
	       (when res (push frame frames))
	       (when (not exact-p) (setq inexact-p t))))
    (values (remove-duplicates-using-trie-and-coercion
	     frames (maybe-coerce-to-frame-fun kb kb-local-only-p))
	    (not inexact-p))))

(defmethods default-direct-get-frames-with-facet-value
    (slot facet value (kb (kb structure-kb)) (inference-level t)
	  (slot-type t) (value-selector t) (kb-local-only-p t))
  (let ((inexact-p nil)
	(frames nil))
    (loop for frame in (get-kb-frames-internal kb kb-local-only-p)
	  when (and (frame-has-slot-p-internal frame slot kb inference-level
					       slot-type kb-local-only-p)
		    (slot-has-facet-p-internal frame slot facet kb
					       inference-level slot-type
					       kb-local-only-p))
	  do (multiple-value-bind (res exact-p)
		 (member-slot-or-facet-value-p
		  frame slot facet value kb inference-level slot-type
		  value-selector kb-local-only-p t)
	       (when res (push frame frames))
	       (when (not exact-p) (setq inexact-p t))))
    (values (remove-duplicates-using-trie-and-coercion
	     frames (maybe-coerce-to-frame-fun kb kb-local-only-p))
	    (not inexact-p))))

(defun get-inherited-facets
	(frame slot kb inference-level slot-type kb-local-only-p)
  (let ((class-p (class-p-internal frame kb kb-local-only-p))
	(inexact-p nil))
    (values
     (remove-duplicates-using-trie-and-coercion
      (append (if class-p
		  (if (member slot-type '(:template :all))
		      (multiple-value-bind (superclasses exact-p)
			  (get-class-superclasses-internal
			   frame kb inference-level :all
			   kb-local-only-p)
			(when (not exact-p) (setq inexact-p t))
			(loop with facets = nil
			      with exact-p = nil
			      for class in superclasses
			      for frame-p = (not (eql-in-kb-internal
						  class frame kb
						  kb-local-only-p))
			      ;; Be safe
			      when frame-p
			      do (multiple-value-setq (facets exact-p)
				   (get-slot-facets-internal
				    class slot kb :direct :template
				    kb-local-only-p))
			      (when (not exact-p) (setq inexact-p t))
			      when frame-p append facets))
		      nil)
		  nil)
	      (if (member slot-type '(:own :all))
		  ;; Then we inherit the own slots from the template
		  ;; slots on the classes of which we are an instance.
		  (multiple-value-bind (types exact-p)
		    (get-instance-types-internal
		     frame kb inference-level :all kb-local-only-p)
		    (when (not exact-p) (setq inexact-p t))
		    (loop with facets = nil
			  with exact-p = nil
			  for class in types
			  for frame-p = (not (eql-in-kb-internal
					      class frame kb
					      kb-local-only-p))
			  ;; Be safe
			  when frame-p
			  do (multiple-value-setq (facets exact-p)
			       (get-slot-facets-internal
				class slot kb :direct :template
				kb-local-only-p))
			  (when (not exact-p) (setq inexact-p t))
			  when frame-p append facets))
		  nil)
	      (multiple-value-bind (facets exact-p)
		  (get-slot-facets-internal frame slot kb :direct slot-type
					    kb-local-only-p)
		(when (not exact-p) (setq inexact-p t))
		facets))
      (maybe-coerce-to-frame-fun kb kb-local-only-p))
     (not inexact-p))))


(defmacro ok-back:define-default-inheritance-methods
    ((&rest exclude) &rest classes)
  "Defines a collection of default inheritance methods for the specified
   <code>classes</code>.  The methods generated are functionally equivalent to
   those generated for <code>default-inheritance-mixin</code>.  This macro
   is useful either if you are defining your own KB class and it is
   inconvenient to mix in <code>default-inheritance-mixin</code> and still
   get the right method combination, or for some reason some of the
   default inheritance methods are undesirable.  If this latter case applies,
   the <code>exclude</code> option can be used.  Any back end generic function
   named in the <code>exclude</code> list will not have a default
   inheritance method defined for the specified classes.  The
   <code>exclude</code> list can contain any of the following symbols:<pre>
   frame-has-slot-p-internal
   get-class-instances-internal
   get-class-subclasses-internal
   get-class-superclasses-internal
   get-facet-values-in-detail-internal
   get-frame-slots-internal
   get-frames-with-facet-value-internal
   get-frames-with-slot-value-internal
   get-instance-types-internal
   get-slot-facets-internal
   get-slot-values-in-detail-internal
   slot-has-facet-p-internal
   subclass-of-p-internal</PRE>

   In addition, the following symbols may also be provided.  These will
   inhibit the generation of methods to compute the <code>:direct</code>
   inference-level versions of <code>get-frames-with-slot-value-internal</code>
   and <code>get-frames-with-facet-value-internal</code> respectively.  These
   latter options are useful for sentential systems that have an efficiently
   indexed way to perform the direct check.<PRE>
   get-frames-with-slot-value-internal-direct
   get-frames-with-facet-value-internal-direct</PRE>

   For example,<PRE>
     (define-default-inheritance-methods
       (ok-back:get-frames-with-slot-value-internal-direct
        ok-back:get-frames-with-facet-value-internal-direct)
       tuple-kb
       structure-tuple-kb)</PRE>
   defines inheritance mthods for the classes <code>tuple-kb</code> and
   <code>structure-tuple-kb</code> except for the direct inference-level
   versions of <code>get-frames-with-slot-value-internal</code> and
   <code>get-frames-with-facet-value-internal</code>."
  (remove nil
  `(progn
    ,(unless
      (member 'subclass-of-p-internal exclude)
      `(defmethods subclass-of-p-internal
	((subclass t) (superclass t) (kb ,classes)
	 (inference-level ((eql :taxonomic) (eql :all-inferable)))
	 (kb-local-only-p t))
	(member-transitive-closure-p
	 superclass subclass kb #'get-class-superclasses-internal
	 :direct :all kb-local-only-p)))

    ,(unless
      (member 'get-instance-types-internal exclude)
      `(defmethods get-instance-types-internal
	((frame t) (kb ,classes)
	 (inference-level ((eql :taxonomic) (eql :all-inferable)))
	 (number-of-values t) (kb-local-only-p t))
	(multiple-value-bind (typeclasses exact-p)
	  (get-instance-types-internal
	   frame kb :direct number-of-values kb-local-only-p)
	  (let ((inexact-p (not exact-p)))
	    (values (union (loop with all-types = nil
				 with exact-p = nil
				 for typeclass in typeclasses
				 do (multiple-value-setq (all-types exact-p)
				      (get-class-superclasses-internal
				       typeclass kb inference-level
				       number-of-values kb-local-only-p))
				 when (not exact-p) do (setq inexact-p t)
				 when all-types
				 append all-types)
			   typeclasses)
		    (not inexact-p))))))

    ,(unless
      (member 'get-class-superclasses-internal exclude)
      `(defmethods get-class-superclasses-internal
	((class t) (kb ,classes)
	 (inference-level ((eql :taxonomic) (eql :all-inferable)))
	 (number-of-values t) (kb-local-only-p t))
	(limited-relation-transitive-closure class kb number-of-values
	 #'get-class-superclasses-internal
	 (list kb :direct number-of-values kb-local-only-p)
	 #'get-class-superclasses-internal
	 (list kb :direct number-of-values kb-local-only-p)
	 kb-local-only-p)))
    
    ,(unless
      (member 'get-class-subclasses-internal exclude)
      `(defmethods get-class-subclasses-internal
	((class t) (kb ,classes)
	 (inference-level ((eql :taxonomic) (eql :all-inferable)))
	 (number-of-values t) (kb-local-only-p t))
	(limited-relation-transitive-closure
	 class kb number-of-values
	 #'get-class-subclasses-internal
	 (list kb :direct number-of-values kb-local-only-p)
	 #'get-class-subclasses-internal
	 (list kb :direct number-of-values kb-local-only-p)
	 kb-local-only-p)))
    
    ,(unless
      (member 'get-class-instances-internal exclude)
      `(defmethods get-class-instances-internal
	((class t) (kb ,classes)
	 (inference-level ((eql :taxonomic) (eql :all-inferable)))
	 (number-of-values t) (kb-local-only-p t))
	(limited-relation-transitive-closure
	 class kb number-of-values
	 #'get-class-instances-internal
	 (list kb :direct number-of-values kb-local-only-p)
	 #'get-class-subclasses-internal
	 (list kb :direct number-of-values kb-local-only-p)
	 kb-local-only-p)))

    ,@(unless
      (member 'get-frame-slots-internal exclude)
      `((defmethods get-frame-slots-internal
	    (frame (kb ,classes)
	     (inference-level ((eql :taxonomic) (eql :all-inferable)))
	     (slot-type t) (kb-local-only-p t))
	  (get-inherited-slots frame kb inference-level slot-type
	   kb-local-only-p))

	(defmethods get-frame-slots-internal
	    (frame (kb ,classes)
	     (inference-level t) (slot-type (eql :all)) (kb-local-only-p t))
	  (multiple-value-bind (own-slots own-exact-p)
	    (get-frame-slots-internal frame kb inference-level :own
				      kb-local-only-p)
	    (multiple-value-bind (template-slots template-exact-p)
	      (get-frame-slots-internal frame kb inference-level :template
					kb-local-only-p)
	      (values (remove-duplicates-using-trie-and-coercion
		       (append own-slots template-slots)
		       (maybe-coerce-to-frame-fun kb kb-local-only-p))
		      (and own-exact-p template-exact-p)))))))

    ,(unless
      (member 'frame-has-slot-p-internal exclude)
      `(defmethods frame-has-slot-p-internal
	((frame t) (slot t) (kb ,classes)
	 (inference-level ((eql :taxonomic) (eql :all-inferable)))
	 (slot-type t) (kb-local-only-p t))
	(basic-default-inheritance-fhsp
	 frame slot kb inference-level slot-type kb-local-only-p)))

    ,(unless
      (member 'slot-has-facet-p-internal exclude)
      `(defmethods slot-has-facet-p-internal
	((frame t) (slot t) (facet t) (kb ,classes)
	 (inference-level ((eql :taxonomic) (eql :all-inferable)))
	 (slot-type t) (kb-local-only-p t))
	(basic-default-inheritance-shfp
	 frame slot facet kb inference-level slot-type kb-local-only-p)))

    ,@(unless
      (member 'get-slot-values-in-detail-internal exclude)
      `((defmethods get-slot-values-in-detail-internal
	    ((frame t) (slot t) (kb ,classes)
	     (inference-level ((eql :taxonomic) (eql :all-inferable)))
	     (slot-type t) (number-of-values t) 
	     (value-selector (eql :default-only))
	     (kb-local-only-p t))
	  (default-inheritance-for-gsv-default-only
	      frame slot kb inference-level slot-type number-of-values
	      value-selector kb-local-only-p))

	(defmethods get-slot-values-in-detail-internal
	    ((frame t) (slot t) (kb ,classes)
	     (inference-level ((eql :taxonomic) (eql :all-inferable)))
	     (slot-type t) (number-of-values t) 
	     (value-selector (eql :known-true))
	     (kb-local-only-p t))
	  (basic-default-inheritance-gsv-known-true-only
	   frame slot kb inference-level slot-type number-of-values
	   value-selector kb-local-only-p))

	(defmethods get-slot-values-in-detail-internal
	    ((frame t) (slot t) (kb ,classes)
	     (inference-level ((eql :taxonomic) (eql :all-inferable)))
	     (slot-type t) (number-of-values t) 
	     (value-selector (eql :either)) (kb-local-only-p t))
	  (default-inheritance-gsv-either
	      frame slot kb inference-level slot-type number-of-values 
	      value-selector kb-local-only-p))))

    ,@(unless
      (member 'get-frames-with-slot-value-internal exclude)
      `((defmethods get-frames-with-slot-value-internal
	    (slot value (kb ,classes)
	     (inference-level ((eql :taxonomic) (eql :all-inferable)))
	     (slot-type t) (value-selector (eql :known-true))
	     (kb-local-only-p t))
	  (get-inherited-frames-with-slot-or-facet-value-known-true
	   slot nil value kb inference-level slot-type value-selector
	   kb-local-only-p nil))

	(defmethods get-frames-with-slot-value-internal
	    (slot value (kb ,classes)
	     (inference-level ((eql :taxonomic) (eql :all-inferable)))
	     (slot-type t) (value-selector ((eql :default-only) (eql :either)))
	     (kb-local-only-p t))
	  (get-frames-with-slot-or-facet-value-default-or-either
	   slot nil value kb inference-level slot-type value-selector
	   kb-local-only-p nil))))

    ,@(unless
      (member 'get-frames-with-slot-value-internal-direct exclude)
      `((defmethods get-frames-with-slot-value-internal
	    (slot value (kb ,classes)
	     (inference-level (eql :direct))
	     (slot-type t) (value-selector t) (kb-local-only-p t))
	  (default-direct-get-frames-with-slot-value
	      slot value kb inference-level slot-type value-selector
	      kb-local-only-p))

	(defmethods get-frames-with-slot-value-internal
	    (slot value (kb ,classes)
	     (inference-level (eql :direct))
	     (slot-type (eql :all)) (value-selector t) (kb-local-only-p t))
	  (multiple-value-bind (own own-exact-p)
	    (default-direct-get-frames-with-slot-value
		slot value kb inference-level :own value-selector
		kb-local-only-p)
	    (multiple-value-bind (template template-exact-p)
	      (default-direct-get-frames-with-slot-value
		  slot value kb inference-level :template value-selector
		  kb-local-only-p)
	      (values (append own template) (and own-exact-p
						 template-exact-p)))))))
    ;;=========================================================================
    ;; Now for Facets

    ,@(unless
      (member 'get-slot-facets-internal exclude)
      `((defmethods get-slot-facets-internal
	    (frame slot (kb ,classes)
	     (inference-level ((eql :taxonomic) (eql :all-inferable)))
	     (slot-type t) (kb-local-only-p t))
	  (get-inherited-facets
	   frame slot kb inference-level slot-type kb-local-only-p))

	(defmethods get-slot-facets-internal
	    (frame slot (kb ,classes) (inference-level t)
	     (slot-type (eql :all)) (kb-local-only-p t))
	  (multiple-value-bind (own-facets own-exact-p)
	    (get-slot-facets-internal frame slot kb inference-level :own
				      kb-local-only-p)
	    (multiple-value-bind (template-facets template-exact-p)
	      (get-slot-facets-internal frame slot kb inference-level
					:template kb-local-only-p)
	      (values (remove-duplicates-using-trie-and-coercion
		       (append own-facets template-facets)
		       (maybe-coerce-to-frame-fun kb kb-local-only-p))
		      (and own-exact-p template-exact-p)))))))

    ,@(unless
      (member 'get-facet-values-in-detail-internal exclude)
      `((defmethods get-facet-values-in-detail-internal
	    ((frame t) (slot t) (facet t) (kb ,classes)
	     (inference-level ((eql :taxonomic) (eql :all-inferable)))
	     (slot-type t) (number-of-values t) 
	     (value-selector (eql :default-only))
	     (kb-local-only-p t))
	  (default-inheritance-for-gfv-default-only
	      frame slot facet kb inference-level slot-type number-of-values
	      value-selector kb-local-only-p))

	(defmethods get-facet-values-in-detail-internal
	    ((frame t) (slot t) (facet t) (kb ,classes)
	     (inference-level ((eql :taxonomic) (eql :all-inferable)))
	     (slot-type t) (number-of-values t) 
	     (value-selector (eql :known-true))
	     (kb-local-only-p t))
	  (basic-default-inheritance-gfv-known-true-only
	   frame slot facet kb inference-level slot-type number-of-values
	   value-selector kb-local-only-p))

	(defmethods get-facet-values-in-detail-internal
	    ((frame t) (slot t) (facet t) (kb ,classes)
	     (inference-level ((eql :taxonomic) (eql :all-inferable)))
	     (slot-type t) (number-of-values t) 
	     (value-selector (eql :either)) (kb-local-only-p t))
	  (default-inheritance-gfv-either
	      frame slot facet kb inference-level slot-type number-of-values 
	      value-selector kb-local-only-p))))

    ,@(unless
      (member 'get-frames-with-facet-value-internal exclude)
      `((defmethods get-frames-with-facet-value-internal
	    (slot facet value (kb ,classes)
	     (inference-level ((eql :taxonomic) (eql :all-inferable)))
	     (slot-type t) (value-selector (eql :known-true))
	     (kb-local-only-p t))
	  (get-inherited-frames-with-slot-or-facet-value-known-true
	   slot facet value kb inference-level slot-type value-selector
	   kb-local-only-p t))

	(defmethods get-frames-with-facet-value-internal
	    (slot facet value (kb ,classes)
	     (inference-level ((eql :taxonomic) (eql :all-inferable)))
	     (slot-type t) (value-selector ((eql :default-only) (eql :either)))
	     (kb-local-only-p t))
	  (get-frames-with-slot-or-facet-value-default-or-either
	   slot facet value kb inference-level slot-type value-selector
	   kb-local-only-p t))))

    ,@(unless
      (member 'get-frames-with-facet-value-internal-direct exclude)
      `((defmethods get-frames-with-facet-value-internal
	    (slot facet value (kb ,classes)
	     (inference-level (eql :direct))
	     (slot-type t) (value-selector t) (kb-local-only-p t))
	  (default-direct-get-frames-with-facet-value
	      slot facet value kb inference-level slot-type value-selector
	      kb-local-only-p))

	(defmethods get-frames-with-facet-value-internal
	    (slot facet value (kb ,classes)
	     (inference-level (eql :direct))
	     (slot-type (eql :all)) (value-selector t) (kb-local-only-p t))
	  (multiple-value-bind (own own-exact-p)
	    (default-direct-get-frames-with-facet-value
		slot facet value kb inference-level :own
		value-selector kb-local-only-p)
	    (multiple-value-bind (template template-exact-p)
	      (default-direct-get-frames-with-facet-value
		  slot facet value kb inference-level :template value-selector
		  kb-local-only-p)
	      (values (append own template)
		      (and own-exact-p template-exact-p))))))))))

(define-default-inheritance-methods ()
    default-inheritance-structure-kb
    default-inheritance-mixin)

