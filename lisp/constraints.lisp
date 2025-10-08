(in-package :ok-kernel)

;==============================================================================

(defun ok-utils:enforce-slot-constraints
    (frame slot current-values future-values kb
	   inference-level slot-type
	   value-selector kb-local-only-p)
  "An interface function for OKBC's default constraint checker.  For a given
   <code>frame</code> and <code>slot</code> it checks all of the applicable
   constraints supported by the <code>kb</code>, both that are imposed by
   facets on the slot in question and by constraint slots on the slot if
   appropriate.<br>
   <code>Current-values</code> is a list of the current slot values and
   <code>future-values</code> is a putative list of the values that the slot
   would contain after the proposed side-effect.  <code>Inference-level</code>,
   etc. are used to constrain how hard and far the constraint checker goes in
   checking constraints."
  (declare (special *okbc-standard-facet-names* *okbc-standard-slot-names*))
  (check-assertion-of-constraint-slot-values
   frame slot current-values future-values kb inference-level slot-type
   value-selector kb-local-only-p)
  (let ((facets (get-slot-facets-internal
		 frame slot kb inference-level slot-type kb-local-only-p)))
    (loop for facet-name in *okbc-standard-facet-names*
	  do (multiple-value-bind 
		   (facet found-p)
		 (coerce-to-facet-internal facet-name kb nil kb-local-only-p)
	       (when (and found-p (member facet facets :test
					  #'(lambda (x y)
					      (eql-in-kb-internal
					       x y kb kb-local-only-p))))
		 (let ((facet-values (get-facet-values-internal
				      frame slot facet kb inference-level
				      slot-type :all value-selector
				      kb-local-only-p)))
		   (setq future-values
			 (check-slot-constraint-for-facet 
			  frame slot facet-name facet facet-values
			  current-values future-values kb inference-level
			  slot-type value-selector kb-local-only-p)))))))
  (let ((slots (get-frame-slots-internal
		 slot kb inference-level slot-type kb-local-only-p)))
    (loop for slot-name in *okbc-standard-slot-names*
	  do (multiple-value-bind 
		   (constraint-slot found-p)
		 (coerce-to-slot-internal slot-name kb nil kb-local-only-p)
	       (when (and found-p (member constraint-slot slots :test
					  #'(lambda (x y)
					      (eql-in-kb-internal
					       x y kb kb-local-only-p))))
		 (let ((slot-values (get-slot-values-internal
				     slot constraint-slot kb inference-level
				     :own :all value-selector kb-local-only-p))
		       (facet (equivalent-constraint-facet slot-name)))
		   (if facet
		       (setq future-values
			     (check-slot-constraint-for-facet
			      frame slot facet nil slot-values current-values
			      future-values kb inference-level slot-type
			      value-selector kb-local-only-p))
		       (setq future-values
			     (check-slot-constraint-for-slot
			      frame slot slot-name constraint-slot slot-values
			      current-values future-values kb inference-level
			      slot-type value-selector kb-local-only-p))))))))
  future-values)

(defun ok-utils:check-assertion-of-constraint-slot-values
   (frame slot current-values future-values kb inference-level slot-type
	  value-selector kb-local-only-p)
  "An interface function for OKBC's default constraint checker.  For a given
   <code>frame</code> and <code>slot</code> it checks all of the applicable
   slot constraints supported by the <code>kb</code>.<br>
   <code>Current-values</code> is a list of the current slot values and
   <code>future-values</code> is a putative list of the values that the slot
   would contain after the proposed side-effect.  <code>Inference-level</code>,
   etc. are used to constrain how hard and far the constraint checker goes in
   checking constraints."
  (declare (special *okbc-standard-slot-names*))
   ;; Special case hard wire in the constraints for the handled constraint
   ;; slots themselves.
  (loop for slot-name in *okbc-standard-slot-names*
	do (multiple-value-bind 
	    (constraint-slot found-p)
	    (coerce-to-slot-internal slot-name kb nil kb-local-only-p)
	    (when (and found-p 
		       (or (eq slot slot-name)
			   (eql-in-kb-internal slot constraint-slot
					       kb kb-local-only-p)))
	      (let ((test-pairs
		     (case slot-name
		       ((:documentation)
			'((:slot-value-type :string)))
		       ((:slot-value-type :domain)
			'((:slot-value-type :class)))
		       (:slot-inverse '((:slot-value-type :slot)))
		       ((:slot-cardinality :slot-maximum-cardinality
					   :slot-minimum-cardinality)
			'((:slot-value-type :integer)
			  (:slot-maximum-cardinality 1)
			  (:slot-numeric-minimum 0)))
		       ((:slot-same-values :slot-not-same-values
					   :slot-subset-of-values)
			'((:slot-value-type :slot-chain)))
		       ((:slot-numeric-minimum :slot-numeric-maximum)
			'((:slot-value-type :number)))
		       (:slot-some-values nil)
		       (:slot-collection-type
			'((:slot-value-type (:setof :set :bag :list)))))))
		(loop for (constraint . constraint-values) in test-pairs
		      for facet = (equivalent-constraint-facet constraint)
		      do (setq future-values
			       (check-slot-constraint-for-facet
				frame constraint-slot facet nil
				constraint-values
				current-values future-values kb inference-level
				slot-type value-selector kb-local-only-p)))))))
  future-values)

(defun ok-utils:check-assertion-of-constraint-facet-values
   (frame slot facet current-values future-values kb inference-level slot-type
	  value-selector kb-local-only-p)
  "An interface function for OKBC's default constraint checker.  For a given
   <code>frame</code>, <code>slot</code>, and <code>facet</code> it checks all
   of the applicable facet constraints supported by the <code>kb</code>.<br>
   <code>Current-values</code> is a list of the current facet values and
   <code>future-values</code> is a putative list of the values that the facet
   would contain after the proposed side-effect.  <code>Inference-level</code>,
   etc. are used to constrain how hard and far the constraint checker goes in
   checking constraints."
  (declare (special *okbc-standard-facet-names*))
   ;; Special case hard wire in the constraints for the handled constraint
   ;; facets themselves.
  (loop for facet-name in *okbc-standard-facet-names*
	do (multiple-value-bind 
	    (constraint-facet found-p)
	    (coerce-to-facet-internal facet-name kb nil kb-local-only-p)
	    (when (and found-p
		       (or (eq facet-name facet)
			   (eql-in-kb-internal facet constraint-facet
					       kb kb-local-only-p)))
	      (let ((test-pairs
		     (ecase facet-name
		       ((:value-type)
			'((:value-type :class)))
		       (:inverse '((:value-type :slot)))
		       ((:cardinality)
			'((:value-type :integer)
			  (:maximum-cardinality 1)
			  (:numeric-minimum 0)))
		       ((:maximum-cardinality :minimum-cardinality)
			'((:value-type :integer)
			  (:numeric-minimum 0)))
		       ((:same-values :not-same-values :subset-of-values)
			'((:value-type :slot-chain)))
		       ((:numeric-minimum :numeric-maximum)
			'((:value-type :number)))
		       (:some-values nil)
		       (:collection-type
			'((:value-type (:setof :set :bag :list)))))))
		(loop for (constraint . constraint-values) in test-pairs
		      do (setq future-values
			       (check-slot-constraint-for-facet
				frame slot constraint nil constraint-values
				current-values future-values kb inference-level
				slot-type value-selector kb-local-only-p)))))))
  future-values)

(defmethod check-slot-constraint-for-facet 
  ((frame t) (slot t) (facet-name t) (facet t) (facet-values t)
   (current-values t) (future-values t) (kb t) (inference-level t) 
   (slot-type t) (value-selector t) (kb-local-only-p t))
  (continuable-error "Unsupported facet constraint method for ~S"
			 facet-name))

(defmethod check-slot-constraint-for-facet 
  ((frame t) (slot t) (facet-name (eql :documentation-in-frame)) (facet t)
   (facet-values t) (current-values t) (future-values t) (kb t)
   (inference-level t) (slot-type t) (value-selector t) (kb-local-only-p t))
  future-values)

(defmethod coerce-maybe-union-or-set (v kb kb-local-only-p)
  (typecase v
    (cons (cond ((eql-in-kb-internal (first v) :union kb kb-local-only-p)
		 (cons (first v)
		       (loop for arg in (rest v)
			     collect (multiple-value-bind (frame found-p)
					 (coerce-to-class-internal
					  arg kb nil kb-local-only-p)
				       (continuable-assert
					found-p not-coercible-to-frame
					:frame frame :kb kb)
				       (get-frame-handle-internal
					frame kb kb-local-only-p)))))
		((eql-in-kb-internal (first v) :setof kb kb-local-only-p)
		 (cons (first v)
		       (loop for arg in (rest v)
			     collect (multiple-value-bind (frame found-p)
					 (coerce-to-frame-internal
					  arg kb nil kb-local-only-p)
				       (if found-p
					   (get-frame-handle-internal
					    frame kb kb-local-only-p)
					   arg)))))
		(t v)))
    (otherwise (multiple-value-bind (value-frame found-p)
		   (coerce-to-frame-internal v kb nil kb-local-only-p)
		 (continuable-assert found-p not-coercible-to-frame
				     :frame v :kb kb)
		 value-frame))))

(defmethod check-slot-constraint-for-facet 
    ((frame t) (slot t) (facet-name (eql :inverse)) (facet t) (facet-values t)
     (current-values t) (future-values t) (kb t) (inference-level t)
     (slot-type t) (value-selector t) (kb-local-only-p t))
  (cond (facet-values
	 (continuable-assert
	  (<= (length facet-values) 1) cardinality-violation
	  :frame frame :slot slot :facet facet :kb kb
	  :constraint "Single valued facet"
	  :error-message "Cardinality should be 1.")
	 (loop for v in future-values
	       collect (coerce-maybe-union-or-set v kb kb-local-only-p)))
	(t future-values)))

(defvar ok-utils:*getting-better-is-ok-p* nil
  "This variable controls the way that errors are signalled when KB constraint
   violations are detected in the OKBC default constraint checker.  The
   constraint checker detects any violations of the constraints, but some
   side effects to the KB, even though strictly violations will leave the KB
   in a state that is closer to being compliant than before.  For example, if
   a slot has a minimum-cardinality constraint of 2 (it should have at least
   two slot values), then clearly putting a single value to this slot will
   still leave it in violation of the constraint.  However, if there were
   previously no values, the state of the KB can reasonably be said to be
   closer to compliant than in the previous state.<P>

   If this variable is false (the default) then constraints are checked as
   strictly as possible.  If true, then violations such as in the above
   example will be permitted.<P>

   This variable may be useful to bind in some back ends during the loading
   of KBs, since there may be transient violations whilst loading certain
   frames.")

(defmethod check-slot-constraint-for-facet 
  ((frame t) (slot t) (facet-name (eql :cardinality)) (facet t)
   (facet-values t) (current-values t) (future-values t) (kb t)
   (inference-level t) (slot-type t) (value-selector t) (kb-local-only-p t))
  (loop for facet-value in facet-values
	do (continuable-assert
	    (and (integerp facet-value) (>= facet-value 0))
	    value-type-violation
	    :frame frame :slot slot :kb kb
	    :constraint "Value type"
	    :error-message
	    (format nil "Cardinality should have a non-negative ~
                         integer value, not ~S." 
		    facet-value))
	   (cond ((ecase slot-type
		    (:template (<= (length future-values) facet-value))
		    (:own (= (length future-values) facet-value)))
		  nil)
		 ((and *getting-better-is-ok-p*
		       (< (abs (- (length future-values)
				  facet-value))
			  (abs (- (length current-values)
				  facet-value))))
		  (warn "In slot ~S of ~S, cardinality should be ~D."
			frame slot facet-value))
		 (t (continuable-assert
		     (ecase slot-type
		       (:template (<= (length future-values) facet-value))
		       (:own (= (length future-values) facet-value)))
		     cardinality-violation
		     :frame frame :slot slot :kb kb
		     :constraint "Slot cardinality"
		     :error-message (format nil "Cardinality should be ~D." 
					    facet-value)))))
  future-values)

(defmethod check-slot-constraint-for-facet 
  ((frame t) (slot t) (facet-name (eql :maximum-cardinality)) (facet t)
   (facet-values t) (current-values t) (future-values t) (kb t)
   (inference-level t) (slot-type t) (value-selector t) (kb-local-only-p t))
  (loop for facet-value in facet-values
	do (continuable-assert
	    (and (integerp facet-value) (>= facet-value 0))
	    value-type-violation
	    :frame frame :slot slot :kb kb
	    :constraint "Value type"
	    :error-message
	    (format nil "Maximum-Cardinality should have a non-negative ~
                         integer value, not ~S." 
		    facet-value))
	   (cond ((<= (length future-values) facet-value)
		  nil)
		 ((and *getting-better-is-ok-p*
		       (< (length future-values) (length current-values)))
		  (warn "In slot ~S of ~S, cardinality should be at most ~D."
			frame slot facet-value))
		 (t (continuable-assert
		     (<= (length future-values) facet-value)
		     cardinality-violation
		     :frame frame :slot slot :kb kb
		     :constraint "Maximum slot cardinality"
		     :error-message
		     (format nil "Cardinality should be at most ~D." 
			     facet-value)))))
  future-values)

(defmethod check-slot-constraint-for-facet 
  ((frame t) (slot t) (facet-name (eql :minimum-cardinality)) (facet t)
   (facet-values t) (current-values t) (future-values t) (kb t)
   (inference-level t) (slot-type t) (value-selector t) (kb-local-only-p t))
  (when (eq slot-type :own)
    (loop for facet-value in facet-values
	  do (continuable-assert
	      (and (integerp facet-value) (>= facet-value 0))
	      value-type-violation
	      :frame frame :slot slot :kb kb
	      :constraint "Value type"
	      :error-message 
	      (format nil "Minimum-Cardinality should have a non-negative ~
                           integer value, not ~S." 
		      facet-value))
	   (cond ((>= (length future-values) facet-value)
		  nil)
		 ((and *getting-better-is-ok-p*
		       (> (length future-values) (length current-values)))
		  (warn "In slot ~S of ~S, cardinality should be at least ~D."
			frame slot facet-value))
		 (t (continuable-assert
		     (>= (length future-values) facet-value)
		     cardinality-violation
		     :frame frame :slot slot :kb kb
		     :constraint "Minimum slot cardinality"
		     :error-message
		     (format nil "Cardinality should be at least ~D." 
			     facet-value))))))
  future-values)

(defmethod check-slot-constraint-for-facet 
  ((frame t) (slot t) (facet-name (eql :numeric-minimum)) (facet t)
   (facet-values t) (current-values t) (future-values t) (kb t)
   (inference-level t) (slot-type t) (value-selector t) (kb-local-only-p t))
  (loop for facet-value in facet-values
	do (loop for value in future-values
		 do (continuable-assert
		     (numberp facet-value)
		     value-type-violation
		     :frame frame :slot slot :kb kb
		     :constraint "Value type"
		     :error-message (format nil "Numeric minimum should have ~
                                                 a numerical value, not ~S." 
					    facet-value))
		    (continuable-assert
		     (and (numberp value) (>= value facet-value))
		     constraint-violation
		     :frame frame :slot slot :kb kb
		     :slot-type slot-type
		     :constraint "Numeric Minimum"
		     :error-message
		     (format nil "Value should be at least ~D"
			     facet-value))))
  future-values)

(defmethod check-slot-constraint-for-facet 
  ((frame t) (slot t) (facet-name (eql :numeric-maximum)) (facet t)
   (facet-values t) (current-values t) (future-values t) (kb t)
   (inference-level t) (slot-type t) (value-selector t) (kb-local-only-p t))
  (loop for facet-value in facet-values
	do (loop for value in future-values
		 do (continuable-assert
		     (numberp facet-value)
		     value-type-violation
		     :frame frame :slot slot :kb kb
		     :slot-type slot-type
		     :constraint "Value type"
		     :error-message (format nil "Numeric maximum should have ~
                                                 a numerical value, not ~S." 
					    facet-value))
		    (continuable-assert
		     (and (numberp value) (<= value facet-value))
		     constraint-violation
		     :frame frame :slot slot :kb kb
		     :slot-type slot-type
		     :constraint "Numeric Maximum"
		     :error-message
		     (format nil "Value should be at most ~D"
			     facet-value))))
  future-values)

(defmethods check-slot-constraint-for-facet 
  ((frame t) (slot t)
   (facet-name ((eql :some-values)
		(eql :collection-type)))
   (facet t) (facet-values t) (current-values t) (future-values t) (kb t)
   (inference-level t) (slot-type t) (value-selector t) (kb-local-only-p t))
  future-values)

(defun validate-slot-chain-syntax (frame slot kb facet-value)
  (continuable-assert
   (or (atom facet-value)
       (and (symbolp (first facet-value))
	    (string-equal :listof (first facet-value))))
   value-type-violation
   :frame frame :slot slot :kb kb
   :constraint "Value type"
   :error-message
   (format nil "Slot chain should be either a slot or (listof ...), not ~S"
	   facet-value)))

(defmethod check-slot-constraint-for-facet 
  ((frame t) (slot t) (facet-name (eql :same-values)) (facet t)
   (facet-values t) (current-values t) (future-values t) (kb t)
   (inference-level t) (slot-type t) (value-selector t) (kb-local-only-p t))
  (when (eq :own slot-type)
    (loop for facet-value in facet-values
	  do (validate-slot-chain-syntax frame slot kb facet-value)
	     (continuable-assert
	      (not (set-exclusive-or
		    future-values
		    (follow-slot-chain-internal
		     frame (if (consp facet-value)
			       (rest facet-value)
			       (list facet-value)) 
		     kb t inference-level value-selector kb-local-only-p)
		    :test #'(lambda (x y)
			      (equal-in-kb-internal 
			       x y kb kb-local-only-p))))
	      constraint-violation
	      :frame frame :slot slot :kb kb
	      :slot-type slot-type
	      :constraint "Same values"
	      :error-message
	      (format nil "Slot values should be the same as in ~S"
		      facet-value))))
  future-values)

(defmethod check-slot-constraint-for-facet 
  ((frame t) (slot t) (facet-name (eql :not-same-values)) (facet t)
   (facet-values t) (current-values t) (future-values t) (kb t)
   (inference-level t) (slot-type t) (value-selector t) (kb-local-only-p t))
  (when (eq :own slot-type)
    (loop for facet-value in facet-values
	  do (validate-slot-chain-syntax frame slot kb facet-value)
	     (continuable-assert
	      (set-exclusive-or
	       future-values
	       (follow-slot-chain-internal
		frame (if (consp facet-value)
			  (rest facet-value)
			  (list facet-value)) 
		kb t inference-level value-selector kb-local-only-p)
	       :test #'(lambda (x y)
			 (equal-in-kb-internal 
			  x y kb kb-local-only-p)))
	      constraint-violation
	      :frame frame :slot slot :kb kb
	      :slot-type slot-type
	      :constraint "Not same values"
	      :error-message
	      (format nil "Slot values should not be the same as in ~S"
		      facet-value))))
  future-values)

(defmethod check-slot-constraint-for-facet 
  ((frame t) (slot t) (facet-name (eql :subset-of-values)) (facet t)
   (facet-values t) (current-values t) (future-values t) (kb t)
   (inference-level t) (slot-type t) (value-selector t) (kb-local-only-p t))
  (when (eq :own slot-type)
    (loop for facet-value in facet-values
	  do (loop for value in future-values
		   do (validate-slot-chain-syntax frame slot kb facet-value)
		      (continuable-assert
		       (member value 
			       (follow-slot-chain-internal
				frame (if (consp facet-value) 
					  (rest facet-value)
					  (list facet-value))
				kb t inference-level value-selector
				kb-local-only-p)
			       :test #'(lambda (x y)
					 (equal-in-kb-internal 
					  x y kb kb-local-only-p)))
		       constraint-violation
		       :frame frame :slot slot :kb kb
		       :slot-type slot-type
		       :constraint "Subset of values"
		       :error-message
		       (format nil "Slot value should be in the list ~S"
			       facet-value)))))
  future-values)

(defun matches-union-p (thing kb kb-local-only-p)
  ;; We do this more complex test because Union is actually a function 
  ;; in KIF, not a KIF operator as is SETOF.
  (or (and (symbolp thing) (string-equal thing :union))
      (eql-in-kb-internal thing :union kb kb-local-only-p)))

(defun ok-utils:value-matches-type-constraint-p
    (value constraint kb inference-level kb-local-only-p)
  "This predicate is true if the <code>value</code> is consistent with the
   specified type <code>constraint</code>.  This funciton is used in OKBC's
   default constraint checker, but it can also be used, for example, to
   validate values entered by users.<P>

   The <code>constraint</code> can be any OKBC compliant class-denoting
   form, including class identifications, <code>SETOF</code>and
   <code>UNION</code> expressions.  For example,<BR>
   <code>(value-matches-type-constraint-p 42 :number ....)</code> is true,<BR>
   <code>(value-matches-type-constraint-p 42 '(setof 0 32 42) ....)</code>
   is true,<BR>
   <code>(value-matches-type-constraint-p 42 `(:union :number ,camel) ....)
   </code> is true,<BR>
   but <code>(value-matches-type-constraint-p 42 `(:union :string ,camel) ....)
   </code> is false."
  (declare (special *okbc-standard-class-names*))
  (typecase constraint
    (cons
     (cond ((and (symbolp (first constraint))
		 (string-equal (first constraint) :setof))
	    (loop for v in (rest constraint)
		  thereis (equal-in-kb-internal value v kb kb-local-only-p)))
	   ((matches-union-p (first constraint) kb kb-local-only-p)
	    (loop for v in (rest constraint)
		  thereis (value-matches-type-constraint-p 
			   value v kb inference-level kb-local-only-p)))
	   (t (continuable-error
	       "Illegal value ~S in type constraint" constraint))))
    (otherwise;; some atom
     (cond
      ((or (eq constraint :thing)
	   (eql-in-kb-internal constraint :thing kb kb-local-only-p))
       t)
      ((or (eq constraint :class)
	   (eql-in-kb-internal constraint :class kb kb-local-only-p))
       (or (member value *okbc-standard-class-names* :test #'eq)
	   (class-p-internal value kb kb-local-only-p)
	   (and (consp value)
		(cond ((and (symbolp (first value))
			    (string-equal (first value) :setof))
		       t)
		      ((matches-union-p (first value) kb kb-local-only-p)
		       (loop for v in (rest value)
			     thereis (value-matches-type-constraint-p 
				      v :class kb inference-level
				      kb-local-only-p)))
		      (t nil)))))
      ((or (eq constraint :individual)
	   (eql-in-kb-internal constraint :individual kb kb-local-only-p))
       (not (value-matches-type-constraint-p 
	     value :class kb inference-level kb-local-only-p)))
      ((or (eq constraint :slot)
	   (eql-in-kb-internal constraint :slot kb kb-local-only-p))
       (slot-p-internal value kb kb-local-only-p))
      ((or (eq constraint :slot-chain)
	   (eql-in-kb-internal constraint :slot-chain kb kb-local-only-p))
       (or (slot-p-internal value kb kb-local-only-p)
	   (and (consp value)
		(loop for v in value
		      always (slot-p-internal
			      v kb kb-local-only-p)))))
      ((or (eq constraint :number)
	   (eql-in-kb-internal constraint :number kb kb-local-only-p))
       (numberp value))
      ((or (eq constraint :integer)
	   (eql-in-kb-internal constraint :integer kb kb-local-only-p))
       (integerp value))
      ((or (eq constraint :string)
	   (eql-in-kb-internal constraint :string kb kb-local-only-p))
       (stringp value))
      ((or (eq constraint :list)
	   (eql-in-kb-internal constraint :list kb kb-local-only-p))
       (listp value))
      (t (instance-of-p-internal
	  value constraint kb inference-level
	  kb-local-only-p))))))

(defmethod check-slot-constraint-for-facet 
  ((frame t) (slot t) (facet-name (eql :value-type)) (facet t)
   (facet-values t) (current-values t) (future-values t) (kb t)
   (inference-level t) (slot-type t) (value-selector t) (kb-local-only-p t))
  (loop for facet-value in facet-values
	do (loop for value in future-values
		 do (continuable-assert
		     (value-matches-type-constraint-p 
		      value facet-value kb inference-level kb-local-only-p)
		     constraint-violation
		     :frame frame :slot slot :kb kb
		     :slot-type slot-type
		     :constraint "Value type"
		     :error-message
		     (format nil "Value: ~S should match value-type ~
                                  constraint ~S" value facet-value))))
  future-values)

(defun equivalent-constraint-facet (key)
  (second (assoc key
		 '((:slot-value-type :value-type)
		   (:slot-inverse :inverse)
		   (:slot-cardinality :cardinality)
		   (:slot-maximum-cardinality :maximum-cardinality)
		   (:slot-minimum-cardinality :minimum-cardinality)
		   (:slot-same-values :same-values)
		   (:slot-not-same-values :not-same-values)
		   (:slot-subset-of-values :subset-of-values)
		   (:slot-numeric-minimum :numeric-minimum)
		   (:slot-numeric-maximum :numeric-maximum)
		   (:slot-some-values :some-values)
		   (:slot-collection-type :collection-type)))))

(defmethod check-slot-constraint-for-slot
  ((frame t) (slot t) (slot-name (eql :documentation)) (constraint-slot t)
   (slot-values t) (current-values t) (future-values t) (kb t)
   (inference-level t) (slot-type t) (value-selector t) (kb-local-only-p t))
  future-values)

(defmethod check-slot-constraint-for-slot
  ((frame t) (slot t) (slot-name (eql :domain)) (constraint-slot t)
   (slot-values t) (current-values t) (future-values t) (kb t)
   (inference-level t) (slot-type t) (value-selector t) (kb-local-only-p t))
  (when (eq :own slot-type)
    (loop for slot-value in slot-values
	  do (continuable-assert
	      (value-matches-type-constraint-p 
	       frame slot-value kb inference-level kb-local-only-p)
	      constraint-violation
	      :frame frame :slot slot :kb kb
	      :slot-type slot-type
	      :constraint "Domain"
	      :error-message
	      (format nil "Frame should match domain ~
                           constraint ~S" slot-value))))
  future-values)

(defun ok-utils:enforce-domain-constraint 
  (frame slot kb slot-type inference-level value-selector kb-local-only-p)
  "An interface function for OKBC's default constraint checker.  For a given
   <code>frame</code> and <code>slot</code> it checks to see that the slot
   is consistent with any domain constraints on that frame.
   <code>Inference-level</code>,
   etc. are used to constrain how hard and far the constraint checker goes in
   checking constraints."
   (multiple-value-bind 
    (slot-frame slot-found-p)
    (coerce-to-frame-internal slot kb nil kb-local-only-p)
    (multiple-value-bind 
     (constraint-slot found-p)
     (coerce-to-slot-internal :domain kb nil kb-local-only-p)
     (when (and slot-found-p found-p
		(frame-has-slot-p-internal
		 slot-frame constraint-slot kb inference-level :own
		 kb-local-only-p))
	   (let ((slot-values (get-slot-values-internal
			       slot-frame constraint-slot kb inference-level
			       :own :all value-selector kb-local-only-p)))
	     (check-slot-constraint-for-slot
	      frame slot-frame :domain nil slot-values nil nil kb
	      inference-level slot-type :either kb-local-only-p))))))