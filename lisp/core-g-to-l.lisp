;;; -*- MODE :Lisp; Syntax:Common-Lisp; Package:OK-kernel; Base:10  -*- 

(in-package :ok-kernel)

(defokbcop okbc:get-behavior-supported-values
    ((behavior :value) &key (kb (current-kb)))
  :returned-values behavior-values
  :manual-category :behavior
  :doc-string
  "Returns a list of the supported values of the \\karg{behavior} 
   the KB is capable of supporting.  For example, the KB might support both
   the \\karg{:immediate} and \\karg{:never} variants of the behavior
   \\karg{:constraint-checking-time}.  These two options would be returned
   as a list.  The returned value \\karg{behavior-values} is always a list,
   even when no variants are supported -- that is, it is \\emptylist."
  :compliance-classes :read)

(defokbcop okbc:get-behavior-values ((behavior :value) &key (kb (current-kb)))
  :returned-values behavior-values
  :manual-category :behavior
  :doc-string
  "Returns a list of active values of the \\karg{behavior} under
   which the KB is currently operating.  For example, the KB might support
   both the \\karg{:immediate} and \\karg{:never} variants of the behavior
   \\karg{:constraint-checking-time}, but only one of these modes can be
   enabled at a given time.  A list containing, for example, just
   \\karg{:never} would be returned.
   The returned value \\karg{behavior-values} is always a list, even when
   no variants are active -- that is, it is the \\emptylist."
  :compliance-classes :read)

(defokbcop okbc:get-class-instances (class &key (kb (current-kb))
					   (inference-level :taxonomic)
					   (number-of-values :all)
					   (kb-local-only-p nil))
  :enumerator t
  :doc-string
  "Returns a \\karg{list-of-instances} for \\karg{class}."
  :compliance-classes :read
  :tell&ask-default-body
  (ask-internal `(:instance-of ?x ,class) kb '?x
		inference-level number-of-values
		t nil (timeout-for-tell&ask-defaults kb)
		:known-true kb-local-only-p)
  :returned-values (list-of-instances exact-p more-status)
  :manual-category :class
  :monitor-body
  (record-reference class nil t nil kb))

(defokbcop okbc:get-class-subclasses (class &key (kb (current-kb))
					    (inference-level :taxonomic)
					    (number-of-values :all)
					    (kb-local-only-p nil))
  :enumerator t
  :doc-string
  "Returns the \\karg{list-of-subclasses} of \\karg{class}."
  :compliance-classes :read
  :tell&ask-default-body
  (ask-internal `(:subclass-of ?x ,class) kb '?x
		inference-level number-of-values
		t nil (timeout-for-tell&ask-defaults kb) :known-true
		kb-local-only-p)
  :returned-values (list-of-subclasses exact-p more-status)
  :manual-category :class
  :monitor-body
  (record-reference class nil t nil kb))


(defokbcop okbc:get-class-superclasses (class &key (kb (current-kb))
					      (inference-level :taxonomic)
					      (number-of-values :all)
					      (kb-local-only-p nil))
  :enumerator t
  :doc-string
  "Returns the \\karg{list-of-superclasses} of \\karg{class}."
  :compliance-classes :read
  :tell&ask-default-body
  (ask-internal `(:subclass-of ,class ?x) kb '?x
		inference-level number-of-values
		t nil (timeout-for-tell&ask-defaults kb) :known-true
		kb-local-only-p)
  :returned-values (list-of-superclasses exact-p more-status)
  :manual-category :class
  :monitor-body
  (record-reference class nil t nil kb))

;------------------------------------------------------------------------------

(defokbcop okbc:get-classes-in-domain-of
    (slot &key (kb (current-kb)) (frame-attachment nil)
	  (inference-level :taxonomic) (kb-local-only-p nil))
  :returned-values classes
  :manual-category :slot
  :doc-string
  "Returns a list of \\karg{classes} that are known to be in the domain of 
   \\karg{slot} with respect to \\karg{frame-attachment} (if supplied).  If
   \\karg{frame-attachment} is supplied, it may be used as a hint to the KRS
   to limit the amount of computation performed by constraining the search
   for classes to the superclasses or types of \\karg{frame-attachment}.  
   Each class returned (and any subclass) is guaranteed to be a legal
   \\karg{frame} argument for a slot operation on \\karg{slot} with
   \\karg{slot-type} {\\tt :template}, e.g., \\kfn{put-slot-values}."
  :default-body
  (if (and (member :slot (get-behavior-values-internal :are-frames kb))
	   (slot-p-internal :domain kb kb-local-only-p))
      ;; We are in the land of reified slots and :domain actually exists
      ;; as a slot
      (let ((domains (get-slot-values-internal
		      slot :domain kb inference-level
		      :own :all :either kb-local-only-p)))
	;; we've got the domains, so now filter out redundant subclasses
	(let ((filtered-domains
	       (remove-classes-with-subclasses-in-list
		domains kb inference-level kb-local-only-p)))
	  (if (rest filtered-domains)
	      ;; We have a list of domains with length > 1.
	      ;; We have no way to compute the intersection of this list
	      ;; so as far as we're concerned, there are no classes that are
	      ;; known to be in the domain of Slot.
	      nil
	      (if filtered-domains
		  ;; There is exacrtly one domain.  We understand this, so it
		  ;; is what we return
		  filtered-domains
		  ;; There are no known domains, so we are unrestricted.
		  ;; That means that anyTHING makes sense.
		  (if (class-p-internal :thing kb kb-local-only-p)
		      (list (coerce-to-class-internal
			     :thing kb t kb-local-only-p))
		      nil)))))
      ;; We have no :domain slot
      (multiple-value-bind (frame found-p)
	  (coerce-to-frame-internal
	   frame-attachment kb nil kb-local-only-p)
	(remove-classes-with-subclasses-in-list
	 (if found-p
	     ;; We have been given a frame hint, so only look transitively
	     ;; from there.
	     (search-up-for-slot-attachments
	      slot frame kb inference-level kb-local-only-p)
	     ;; We have no frame hint, so use all of the known classes to
	     ;; figure it out.
	     (loop for class in (get-kb-classes-internal
				 kb :all kb-local-only-p)
		   when (frame-has-slot-p-internal
			 class slot kb inference-level :template
			 kb-local-only-p)
		   collect class))
	 kb inference-level kb-local-only-p))))

(defun remove-classes-with-subclasses-in-list
    (classes kb inference-level kb-local-only-p)
  (remove-duplicates
   (loop for x in classes
	 unless (find x classes
		      :test #'(lambda (x y)
				(subclass-of-p-internal
				 x y kb inference-level kb-local-only-p)))
	 collect x)))

(defun search-up-for-slot-attachments
    (slot frame kb inference-level kb-local-only-p)
  (let ((class-p (class-p-internal frame kb kb-local-only-p)))
    (let ((superclasses
	   (if class-p
	       (get-class-superclasses-internal
		frame kb inference-level :all kb-local-only-p)
	       nil))
	  (types (get-instance-types-internal
		  frame kb inference-level :all kb-local-only-p))
	  (local-result (if class-p
			    (and (frame-has-slot-p-internal
				  frame slot kb inference-level :template
				  kb-local-only-p)
				 frame)
			    nil)))
      (let ((super-result
	     ;; Note that we got all of the specified superclasses above,
	     ;; so we must restrict if we are :direct and prevent the
	     ;; recursion.
	     (case inference-level
	       (:direct nil)
	       (otherwise
		(loop for superclass in superclasses
		      append (search-up-for-slot-attachments
			      slot superclass kb inference-level
			      kb-local-only-p)))))
	    (type-result
	     (loop for type in types
		   append (search-up-for-slot-attachments
			   slot type kb inference-level kb-local-only-p))))
	(if super-result ;; then we know that any local result must be
	    ;; subsumed.
	    (append super-result type-result)
	    (if local-result
		(cons local-result type-result)
		type-result))))))

;------------------------------------------------------------------------------

(defokbcop okbc:get-facet-value
    (frame slot facet &key (kb (current-kb))
	   (inference-level :taxonomic)
	   (slot-type :own) (value-selector :either)
	   (kb-local-only-p nil))
  :returned-values (value-or-false exact-p)
  :manual-category :facet
  :doc-string
  "Returns the sole member of the set of values
   of the specified facet.  It is most commonly used when that set is 
   expected to have only one member.  When the facet has no value,
   \\karg{value-or-false} is \\false.  It is an error to
   call this operation on a non-single-valued facet; if it is called, a
   \\kcond{cardinality-violation} error should be signaled."
  :standard-default-body
  (multiple-value-bind (values exact-p)
      (get-facet-values-internal
       frame slot facet kb inference-level slot-type 2 value-selector
       kb-local-only-p)
    (when (rest values)
      (error 'cardinality-violation
	     :frame frame :slot slot :facet facet :kb kb
	     :constraint "Single valued facet"
	     :error-message
	     (format nil "Cardinality should be 1 during ~
                          (get-facet-value ~S ~S ~S ...)"
		     frame slot facet)))
    (values (first values) exact-p))
  :monitor-body
  (record-reference frame slot t nil kb))



(defokbcop okbc:get-facet-values (frame slot facet &key (kb (current-kb))
					(inference-level :taxonomic)
					(slot-type :own)
					(number-of-values :all)
					(value-selector :either)
					(kb-local-only-p nil))
  :enumerator t
  :doc-string
  "Returns the set of values of the specified facet,
   in no guaranteed order.  It always returns a (possibly empty) list
   of values."
  :standard-default-body
  (multiple-value-bind (list-of-specs exact-p more-status)
      (get-facet-values-in-detail-internal frame slot facet kb inference-level
					   slot-type number-of-values
					   value-selector kb-local-only-p)
    ;; We need to remove-duplicates because get-slot-values-in-detail
    ;; may return default values subsumed by true values, and also
    ;; inherited values that are considered distinct from direct ones.
    (values (remove-duplicates-using-trie-and-coercion
	     (mapcar #'first list-of-specs)
	     (maybe-coerce-to-frame-fun kb kb-local-only-p))
	    exact-p more-status))
  :tell&ask-default-body
  ((ask-internal (ecase slot-type
		   (:own `(,facet ,slot ,frame ?x))
		   (:template `(:template-facet-value ,facet ,slot ,frame ?x)))
		 kb '?x inference-level number-of-values
		 t nil (timeout-for-tell&ask-defaults kb) value-selector
		 kb-local-only-p))
  :compliance-classes (:read :facets)
  :returned-values (values exact-p more-status)
  :manual-category :facet
  :monitor-body
  (record-reference frame slot t nil kb))

(defokbcop okbc:get-facet-values-in-detail
    (frame slot facet
	   &key (kb (current-kb))
	   (inference-level :taxonomic)
	   (slot-type :own) (number-of-values :all)
	   (value-selector :either)
	   (kb-local-only-p nil))
  :enumerator t
  :doc-string
  "Returns the \\karg{list-of-specs} describing the values
   of the \\karg{facet} of \\karg{slot} within \\karg{frame}, in no guaranteed
   order.   It always returns a list of specifications as values.  If the
   specified slot has no values, \\emptylist\\ is returned.

   Each spec is a 3-tuple of the form (value direct-p default-p).
   \\bitem
   \\item value -- a value of the facet
   \\item direct-p -- a flag that is \\true\\ if the value is known to be
                      directly asserted for the facet in the \\karg{frame} and
                      \\false\\ otherwise
   \\item default-p -- a flag that is \\true\\ if the value is known to be
                       a default value, and \\false\\ otherwise
   \\eitem
   The fourth returned value (\\karg{default-p}) is true if the
   \\karg{list-of-specs} is \\emptylist, and the fact that there are no values
   is itself a default."
  :compliance-classes :read
  :tell&ask-default-body
  (multiple-value-bind (list-of-specs exact-p more-status)
      (ask-internal
       (ecase slot-type
	 (:own `(,facet ,slot ,frame ?x))
	 (:template `(:template-facet-value ,facet ,slot ,frame ?x)))
       kb `(?x ,(eq inference-level :direct) nil)
       inference-level number-of-values
       t nil (timeout-for-tell&ask-defaults kb) value-selector kb-local-only-p)
    (values list-of-specs exact-p more-status nil))
  :returned-values (list-of-specs exact-p more-status default-p)
  :manual-category :facet
  :monitor-body
  (record-reference frame slot t nil kb))

;------------------------------------------------------------------------------

(defokbcop okbc:get-frame-details (frame &key (kb (current-kb))
					 (inference-level :taxonomic)
					 (number-of-values :all)
					 (kb-local-only-p nil))
  :returned-values (details exact-p)
  :manual-category :frame
  :doc-string
  "Returns a property list (list of alternating keywords and values)
   describing the \\karg{frame}.  The properties of the frame are computed
   using the \\karg{inference-level}, \\karg{number-of-values-p}, and
   \\karg{kb-local-only-p} arguments, whenever applicable to the appropriate
   OKBC operator used to compute any given property.  The set of properties
   computed is at least the following:

   \\begin{tabular}{ll}
   {\\em Property}         & {\\em Operation(s) used to compute property} \\\\
   {\\tt :handle}          & \\kfn{get-frame-handle}      \\\\
   {\\tt :name}            & \\kfn{get-frame-name}        \\\\
   {\\tt :pretty-name}     & \\kfn{get-frame-pretty-name} \\\\
   {\\tt :frame-type}      & \\kfn{get-frame-type}        \\\\
   {\\tt :primitive-p}     & \\kfn{primitive-p}           \\\\
   {\\tt :superclasses}    & \\kfn{get-class-superclasses}      \\\\
   {\\tt :subclasses}      & \\kfn{get-class-subclasses}        \\\\
   {\\tt :types}           & \\kfn{get-instance-types}             \\\\
   {\\tt :own-slots}       & \\kfn{get-frame-slots}, \\kfn{get-slot-values}\\\\
   {\\tt :template-slots}  & \\kfn{get-frame-slots}, \\kfn{get-slot-values}\\\\
   {\\tt :own-facets}      & \\kfn{get-frame-slots}, \\kfn{get-slot-values}, \\kfn{get-slot-facets}, \\kfn{get-facet-values} \\\\
   {\\tt :template-facets} & \\kfn{get-frame-slots}, \\kfn{get-slot-values}, \\kfn{get-slot-facets}, \\kfn{get-facet-values} \\\\
   {\\tt :sentences}       & \\kfn{get-frame-sentences}   \\\\
   \\end{tabular}

   The {\\tt :own-slots}, {\\tt :own-facets}, {\\tt :template-slots}, and
   {\\tt :template-facets} properties returned are slot and facet
   specifications as defined for \\kfn{create-frame}.  This operation is most
   useful in low-bandwidth or high-latency applications.  A single call to
   \\kfn{get-frame-details} is often sufficient to display all the
   interesting features of a frame.  The value of the {\\tt :sentences}
   component is a set of non-OKBC sentences, i.e. what would be returned by
   \\kfn{get-frame-sentences} with the {\\tt :okbc-sentences-p} argument set
   to \\false\\."
  :monitor-body
  (progn (record-reference frame nil t nil kb))
  :default-body
  (multiple-value-bind (frame found-p)
    (coerce-to-frame-internal frame kb nil kb-local-only-p)
    (if found-p
	(let ((handle (get-frame-handle-internal frame kb kb-local-only-p))
	      (name (get-frame-name-internal frame kb kb-local-only-p))
	      (pretty-name
	       (get-frame-pretty-name-internal frame kb kb-local-only-p))
	      (type (get-frame-type-internal frame kb kb-local-only-p))
	      (inexact-p nil))
	  (multiple-value-bind (own-slots exact-p)
	      (get-frame-slots-internal
	       frame kb inference-level :own kb-local-only-p)
	    (when (not exact-p) (setq inexact-p t))
	    (multiple-value-bind (template-slots exact-p)
		(if (eq :class type)
		    (get-frame-slots-internal
		     frame kb inference-level
		     :template kb-local-only-p)
		    (values nil t))
	      (when (not exact-p) (setq inexact-p t))
	      (multiple-value-bind (superclasses exact-p)
		  (if (eq :class type)
		      (get-class-superclasses-internal
		       frame kb inference-level number-of-values
		       kb-local-only-p)
		      (values nil t))
		(when (not exact-p) (setq inexact-p t))
		(multiple-value-bind (subclasses exact-p)
		    (if (eq :class type)
			(get-class-subclasses-internal
			 frame kb inference-level number-of-values
			 kb-local-only-p)
			(values nil t))
		  (when (not exact-p) (setq inexact-p t))
		  (multiple-value-bind (types exact-p)
		      (get-instance-types-internal
		       frame kb inference-level number-of-values
		       kb-local-only-p)
		    (when (not exact-p) (setq inexact-p t))
		    (multiple-value-bind (own-slot-specs exact-p)
			(get-slot-specification
			 frame own-slots :own kb inference-level
			 number-of-values kb-local-only-p)
		      (when (not exact-p) (setq inexact-p t))
		      (multiple-value-bind (template-slot-specs exact-p)
			  (get-slot-specification
			   frame template-slots :template kb inference-level
			   number-of-values kb-local-only-p)
			(when (not exact-p) (setq inexact-p t))
			(multiple-value-bind (own-facet-specs exact-p)
			    (get-facet-specification frame own-slots :own kb
						     inference-level
						     number-of-values
						     kb-local-only-p)
			  (when (not exact-p) (setq inexact-p t))
			(multiple-value-bind (template-facet-specs exact-p)
			    (get-facet-specification
			     frame template-slots :template kb inference-level
			     number-of-values kb-local-only-p)
			  (when (not exact-p) (setq inexact-p t))
			  (multiple-value-bind (sentences exact-p)
			      (get-frame-sentences-internal
			       frame kb number-of-values nil :either
			       kb-local-only-p)
			    (when (not exact-p) (setq inexact-p t))
			    (values 
			     (list
			      :frame frame
			      :handle handle
			      :name name
			      :pretty-name pretty-name
			      :frame-type type
			      :primitive-p
			      (if (and (eq :class type)
				       (primitive-p-internal
					frame kb kb-local-only-p))
				  t nil)
			      :superclasses
			      (as-list-of-frame-handles
			       superclasses kb kb-local-only-p)
			      :subclasses
			      (as-list-of-frame-handles
			       subclasses kb kb-local-only-p)
			      :types (as-list-of-frame-handles
				      types kb kb-local-only-p)
			      :own-slots own-slot-specs
			      :template-slots template-slot-specs
			      :own-facets own-facet-specs
			      :template-facets template-facet-specs
			      :sentences sentences)
			     (not inexact-p)))))))))))))
	(values nil nil))))

(defun as-list-of-frame-handles (list kb kb-local-only-p)
  (let ((result nil))
    (loop for x in list
	  do (multiple-value-bind (frame found-p)
		 (coerce-to-frame-internal x kb nil kb-local-only-p)
	       (if found-p
		   (let ((handle (get-frame-handle-internal
				  frame kb kb-local-only-p)))
		     (if (and frame handle)
			 (push handle result)
			 (error "Where is frame ~S?" (list x frame handle))))
		   (push x result))))
    result))

(defun encache-slot-and-facet-specs
    (slots facets frame kb slot-type inference-level kb-local-only-p)
  (let ((slot-list nil))
    (loop for (slot . values) in slots
	  do (let ((vals nil)
		   (dvals nil)
		   (values-for-slot (list :values slot t)))
	       (loop for v in values
		     do (if (and (consp v) (eq :default (first v)))
			    (push (second v) dvals)
			    (push v vals)))
	       (ok-cache::encache-get-slot-values-internal
		(list :values vals t nil)
		frame slot kb inference-level slot-type :all :known-true
		kb-local-only-p)
	       (ok-cache::encache-get-slot-values-internal
		(list :values dvals t nil)
		frame slot kb inference-level slot-type :all :default-only
		kb-local-only-p)
	       (ok-cache::encache-get-slot-type-internal
		slot-type frame slot kb inference-level kb-local-only-p)
	       (cond ((ok-back:member-behavior-values-p-internal
		       :are-frames :slot kb)
		      ;; I really don't think that these are guaranteed. JPR
;                      (ok-cache::encache-coerce-to-frame-internal
;                       values-for-slot slot kb nil kb-local-only-p)
;                      (ok-cache::encache-coerce-to-frame-internal
;                       values-for-slot slot kb t kb-local-only-p)
;                      (ok-cache::encache-coercible-to-frame-p-internal
;                       t slot kb  kb-local-only-p)
;                      (ok-cache::encache-get-frame-handle-internal
;                       slot slot kb  kb-local-only-p)
		      )
		     (t (ok-cache::encache-coercible-to-frame-p-internal
			 nil slot kb  kb-local-only-p)
			(ok-cache::encache-coerce-to-frame-internal
			 (list :values nil nil) slot kb nil kb-local-only-p)))
	       (ok-cache::encache-coerce-to-slot-internal
		values-for-slot slot kb nil kb-local-only-p)
	       (ok-cache::encache-coerce-to-slot-internal
		values-for-slot slot kb t kb-local-only-p))
	  ;; We may change our mind below.
	  (ok-cache::encache-get-slot-facets-internal
	   (list :values () t) frame slot kb inference-level slot-type
	   kb-local-only-p)
	  (pushnew slot slot-list))
    (let ((facet-list nil))
      (loop for (slot . facet-spec) in facets
	    do (pushnew slot slot-list)
	    (loop for (facet . values) in facet-spec
		  do (pushnew facet facet-list)
		  (let ((fvals nil)
			(fdvals nil)
			(values-for-facet (list :values facet t)))
		    (loop for v in values
			  do (if (and (consp v) (eq :default (first v)))
				 (push (second v) fdvals)
				 (push v fvals)))
		    (ok-cache::encache-get-facet-values-internal
		     (list :values fvals t nil) frame slot facet kb
		     inference-level slot-type :all :known-true
		     kb-local-only-p)
		    (ok-cache::encache-get-facet-values-internal
		     (list :values fdvals t nil) frame slot facet kb
		     inference-level slot-type :all
		     :default-only kb-local-only-p)
		    ;; Might not be mentioned in slot list
		    (ok-cache::encache-get-slot-type-internal
		     slot-type frame slot kb inference-level kb-local-only-p)
		    (cond ((ok-back:member-behavior-values-p-internal
			    :are-frames :facet kb)
		      ;; I really don't think that these are guaranteed. JPR
;                           (ok-cache::encache-coerce-to-frame-internal
;                            values-for-facet facet kb nil kb-local-only-p)
;                           (ok-cache::encache-coerce-to-frame-internal
;                            values-for-facet facet kb t kb-local-only-p)
;                           (ok-cache::encache-coercible-to-frame-p-internal
;                            t facet kb  kb-local-only-p)
;                           (ok-cache::encache-get-frame-handle-internal
;                            facet facet kb  kb-local-only-p)
			   )
			  (t (ok-cache::encache-coercible-to-frame-p-internal
			      nil facet kb  kb-local-only-p)
			     (ok-cache::encache-coerce-to-frame-internal
			      (list :values nil nil) facet kb nil
			      kb-local-only-p)))
		    (ok-cache::encache-coerce-to-facet-internal
		     values-for-facet facet kb nil kb-local-only-p)
		    (ok-cache::encache-coerce-to-facet-internal
		     values-for-facet facet kb t kb-local-only-p)))
	    (ok-cache::encache-get-slot-facets-internal
	     (list :values facet-list t) frame slot kb inference-level
	     slot-type kb-local-only-p)))
    (ok-cache::encache-get-frame-slots-internal
     (list :values slot-list t) frame kb inference-level slot-type
     kb-local-only-p)))

(defmethod ok-cache:cache-fill-hook
 ((function (eql 'ok-back:get-frame-details-internal)) (key t) (kb t)
  (new-results t) (multiple-value-p t))
 (let ((names-required-p (not (member nil (get-behavior-values-internal
					   :frame-names-required kb)))))
   (destructuring-bind (frame-from-caller kb inference-level number-of-values
					  kb-local-only-p)
       (rest key)
     (destructuring-bind
	   (&key frame handle name pretty-name frame-type primitive-p
		 superclasses subclasses types own-slots template-slots
		 own-facets template-facets &allow-other-keys)
	 (first new-results);; blow away the exact-p
       (ok-cache::encache-get-frame-handle-internal
	handle frame-from-caller kb kb-local-only-p)
       (ok-cache::encache-get-frame-name-internal name frame-from-caller kb
						  kb-local-only-p)
       (ok-cache::encache-get-frame-pretty-name-internal
	pretty-name frame-from-caller kb kb-local-only-p)
       (ok-cache::encache-get-frame-type-internal
	frame-type frame-from-caller kb kb-local-only-p)
       (ok-cache::encache-get-instance-types-internal
	(list :values types t nil) frame-from-caller kb inference-level
	number-of-values
	kb-local-only-p)
       (when (eq :class frame-type)
	 (ok-cache::encache-get-class-superclasses-internal
	  (list :values superclasses t nil)
	  frame-from-caller kb inference-level number-of-values
	  kb-local-only-p)
	 (ok-cache::encache-get-class-subclasses-internal
	  (list :values subclasses t nil) frame-from-caller kb inference-level
	  number-of-values kb-local-only-p)
	 (ok-cache::encache-primitive-p-internal
	  primitive-p frame-from-caller kb kb-local-only-p))
       (encache-slot-and-facet-specs
	own-slots own-facets frame-from-caller kb :own inference-level
	kb-local-only-p)
       (encache-slot-and-facet-specs
	template-slots template-facets frame-from-caller kb :template
	inference-level kb-local-only-p)
       ;;new ones - JFT 3/5/98
       (ok-cache::encache-get-frame-handle-internal
	handle frame-from-caller kb  kb-local-only-p)
       (ok-cache::encache-get-frame-handle-internal
	handle handle kb  kb-local-only-p)
       (let ((frame-coercion-spec (list :values frame t)))
	 (ecase frame-type
	   (:class (ok-cache::encache-coerce-to-class-internal
		    frame-coercion-spec frame-from-caller kb nil
		    kb-local-only-p)
		   (ok-cache::encache-coerce-to-class-internal
		    frame-coercion-spec frame-from-caller kb t kb-local-only-p)
		   (ok-cache::encache-class-p-internal
		    t  frame-from-caller kb kb-local-only-p)
		   (ok-cache::encache-class-p-internal
		    t handle kb kb-local-only-p)
		   ;; We know it can't be an individual because these are
		   ;; disjoint
		   (ok-cache::encache-coerce-to-individual-internal
		    nil frame-from-caller kb nil kb-local-only-p)
		   (ok-cache::encache-individual-p-internal
		    nil frame-from-caller kb  kb-local-only-p)
		   (ok-cache::encache-individual-p-internal
		    nil handle kb  kb-local-only-p))
	   (:slot (ok-cache::encache-coerce-to-slot-internal
		   frame-coercion-spec frame-from-caller kb nil
		   kb-local-only-p)
		  (ok-cache::encache-coerce-to-slot-internal
		   frame-coercion-spec frame-from-caller kb t kb-local-only-p)
		  (ok-cache::encache-slot-p-internal
		   t  frame-from-caller kb kb-local-only-p)
		  (ok-cache::encache-slot-p-internal
		   t handle kb kb-local-only-p))
	   (:individual (ok-cache::encache-coerce-to-individual-internal
			 frame-coercion-spec frame-from-caller kb nil
			 kb-local-only-p)
			(ok-cache::encache-coerce-to-individual-internal
			 frame-coercion-spec frame-from-caller kb t
			 kb-local-only-p)
			(ok-cache::encache-individual-p-internal
			 t frame-from-caller kb kb-local-only-p)
			(ok-cache::encache-individual-p-internal
			 t handle kb kb-local-only-p)
			;; We know it can't be a class because these are
			;; disjoint
			(ok-cache::encache-coerce-to-class-internal
			 nil frame-from-caller kb nil kb-local-only-p)
			(ok-cache::encache-class-p-internal
			 nil  frame-from-caller kb kb-local-only-p)
			(ok-cache::encache-class-p-internal
			 nil handle kb kb-local-only-p))
	   (:facet (ok-cache::encache-coerce-to-facet-internal
		    frame-coercion-spec frame-from-caller kb nil
		    kb-local-only-p)
		   (ok-cache::encache-coerce-to-facet-internal
		    frame-coercion-spec frame-from-caller kb t kb-local-only-p)
		   (ok-cache::encache-facet-p-internal
		    t frame-from-caller kb kb-local-only-p)
		   (ok-cache::encache-facet-p-internal
		    t handle kb kb-local-only-p)))
	 (ok-cache::encache-coercible-to-frame-p-internal
	  (not (null handle)) frame-from-caller kb  kb-local-only-p) 
	 (ok-cache::encache-coerce-to-frame-internal
	  frame-coercion-spec frame-from-caller kb nil kb-local-only-p)
	 (ok-cache::encache-coerce-to-frame-internal
	  frame-coercion-spec frame-from-caller kb   t kb-local-only-p)
	 (ok-cache::encache-coerce-to-frame-internal
	  frame-coercion-spec handle kb nil kb-local-only-p)
	 (ok-cache::encache-coerce-to-frame-internal
	  frame-coercion-spec handle kb  t kb-local-only-p)
	 (when (and name names-required-p)
	   (ok-cache::encache-coerce-to-frame-internal
	    frame-coercion-spec name kb nil kb-local-only-p)
	   (ok-cache::encache-coerce-to-frame-internal
	    frame-coercion-spec name kb   t kb-local-only-p)
	   (ok-cache::encache-coercible-to-frame-p-internal
	    (not (null handle)) name kb kb-local-only-p)
	   (ecase frame-type
	     (:class (ok-cache::encache-coerce-to-class-internal
		      frame-coercion-spec name kb nil kb-local-only-p)
		     (ok-cache::encache-coerce-to-class-internal
		      frame-coercion-spec name kb   t kb-local-only-p)
		     (ok-cache::encache-class-p-internal
		      t name kb kb-local-only-p)
		     ;; We know it can't be an individual because these are
		     ;; disjoint
		     (ok-cache::encache-coerce-to-individual-internal
		      nil name kb nil kb-local-only-p)
		     (ok-cache::encache-individual-p-internal
		      nil name kb kb-local-only-p))
	     (:slot (ok-cache::encache-coerce-to-slot-internal
		     frame-coercion-spec name kb nil kb-local-only-p)
		    (ok-cache::encache-coerce-to-slot-internal
		     frame-coercion-spec name kb   t kb-local-only-p)
		    (ok-cache::encache-slot-p-internal
		     t name kb kb-local-only-p))
	     (:individual (ok-cache::encache-coerce-to-individual-internal
			   frame-coercion-spec name kb nil kb-local-only-p)
			  (ok-cache::encache-coerce-to-individual-internal
			   frame-coercion-spec name kb   t kb-local-only-p)
			  (ok-cache::encache-individual-p-internal
			   t name kb kb-local-only-p))
	     (:facet (ok-cache::encache-coerce-to-facet-internal
		      frame-coercion-spec name kb nil kb-local-only-p)
		     (ok-cache::encache-coerce-to-facet-internal
		      frame-coercion-spec name kb   t kb-local-only-p)
		     (ok-cache::encache-facet-p-internal
		      t name kb kb-local-only-p)))))))))

;------------------------------------------------------------------------------

(defokbcop okbc:get-frame-handle (frame &key (kb (current-kb))
					(kb-local-only-p nil))
  :returned-values frame-handle
  :manual-category :frame
  :doc-string
  "Returns a \\karg{frame-handle} that uniquely identifies the \\karg{frame}
   argument in \\karg{kb}."
  :standard-default-body (coerce-to-frame-internal frame kb t kb-local-only-p)
  :tell&ask-default-body
  (first (ask-internal `(:handle ,frame ?x) kb '?x
		       (inference-level-for-tell&ask-defaults kb) :all
		       t nil (timeout-for-tell&ask-defaults kb)
		       :known-true kb-local-only-p))
  :monitor-body
  (record-reference frame nil t nil kb))


(defokbcop okbc:get-frame-in-kb (thing &key (kb (current-kb)) (error-p t)
				       (kb-local-only-p nil))
  :doc-string
  "Returns two values.  The first value is the \\karg{frame}
   identified by \\karg{thing} if such a frame is found, or \\false.
   The second value (\\karg{frame-found-p}) is \\true\\ iff \\karg{thing} is
   coercible to a frame, and that frame is resident in \\karg{KB}.  In
   all cases it is verified that the frame does, in fact, reside in \\karg{kb}.
   Otherwise, the \\karg{frame-found-p} value is {\\tt nil} (unless 
   \\karg{error-p} is \\true, in which case the operation signals a
   \\kcond{not-coercible-to-frame} error because
   \\karg{thing} is not a valid frame in \\karg{kb})."
  :compliance-classes :read
  :returned-values (frame frame-found-p)
  :manual-category :frame
  :monitor-body
  (record-reference thing nil t nil kb) )

(defokbcop okbc:get-frame-name (frame &key (kb (current-kb))
				      (kb-local-only-p nil))
  :returned-values frame-name
  :manual-category :frame
  :doc-string
  "Returns \\karg{frame-name}, an entity that is the name of the frame
   identified by \\karg{frame}, usually a symbol or string."
  ;; Does no coersion so that this fn will work with standard frame
  ;; names such as :integer.
  :compliance-classes :read
  :tell&ask-default-body
  (first (ask-internal `(:name ,frame ?x) kb '?x
		       (inference-level-for-tell&ask-defaults kb) 1
		       t nil (timeout-for-tell&ask-defaults kb)
		       :known-true kb-local-only-p))
  :monitor-body
  (record-reference frame nil t nil kb) )


(defokbcop okbc:get-frame-pretty-name (frame &key (kb (current-kb))
					     (kb-local-only-p nil))
  :returned-values string
  :manual-category :frame
  :doc-string
  "Returns a string that is a pretty, printed representation for \\karg{frame}
   -- that is, the name is suitable for use within a user interface for
   display purposes.

   There is no guarantee that it will be possible to find a unique frame
   given only its pretty-name, but \\kfn{get-frames-matching} can be used to
   find frames matching such strings when possible."
  :compliance-classes :read
  :tell&ask-default-body
  (first (ask-internal `(:pretty-name ,frame ?x) kb '?x
		       (inference-level-for-tell&ask-defaults kb) 1
		       t nil (timeout-for-tell&ask-defaults kb)
		       :known-true kb-local-only-p))
  :monitor-body
  (record-reference frame nil t nil kb))


(defokbcop okbc:get-frame-sentences (frame &key (kb (current-kb))
					   (number-of-values :all)
					   (okbc-sentences-p t)
					   (value-selector :either)
					   (kb-local-only-p nil))
  :returned-values (list-of-sentences exact-p more-status)
  :manual-category :tell-ask
  :doc-string
  "Returns a list of all the logical sentences associated with a \\karg{frame}.
   The sentences may have been asserted using \\karg{tell}, or any other
   OKBC update operation.  If \\karg{okbc-sentences-p} is \\true, then all
   sentences are returned, including the ones that are equivalent to
   basic OKBC operations.  The sentences equivalent to OKBC operations are
   defined in Table~\\ref{tab:tell-semantics}.  If \\karg{okbc-sentences-p} is
   \\false, sentences that are equivalent to OKBC operations are not
   returned.  This is very useful for user interface applications that do not
   want to present redundant information.  If no matching sentences are
   found, \\karg{list-of-sentences} will be \\emptylist."
  :compliance-classes :read
  :standard-default-body
  (if okbc-sentences-p
      (let ((frame (coerce-to-frame-internal frame kb t kb-local-only-p)))
	(let ((details (get-frame-details-internal frame kb :direct
						   number-of-values
						   kb-local-only-p))
	      (sentences nil)
	      (count 0)
	      (more-status nil))
	  (macrolet ((psh (x place)
		       `(progn (push ,x ,place)
			       (incf count)
			       (when (and (not (eq number-of-values :all))
					  (>= count number-of-values))
				 (setq more-status :more)
				 (throw :stop nil)))))
	    (catch :stop
	      (loop for (key value) on details by #'cddr
		    do
		    (case key
		      (:handle (psh `(:handle ,frame ,value) sentences))
		      (:name (psh `(:name ,frame ,value) sentences))
		      (:pretty-name (psh `(:pretty-name ,frame ,value) 
					 sentences))
		      (:frame-type (psh `(,value ,frame) sentences))
		      (:primitive-p (when value 
				      (psh `(:primitive ,frame) sentences)))
		      (:superclasses (loop for cl in value
					   do (psh `(:subclass-of ,frame ,cl)
						   sentences)))
		      (:subclasses (loop for cl in value
					 do (psh `(:subclass-of ,cl ,frame)
						 sentences)))
		      (:types (loop for cl in value
				    do (psh `(:instance-of ,frame ,cl)
					    sentences)))
		      ((:own-slots :template-slots)
		       (loop for spec in value
			     for slot = (first-if-list spec)
			     for values = (if (consp spec) (rest spec) nil)
			     for slot-of-key = (if (eq key :own-slots)
						   :slot-of
						 :template-slot-of)
			     do (psh `(,slot-of-key ,slot ,frame) sentences)
			     (loop for v in values
				   for default-p 
				   = (and (consp v)
					  (eq :default (first v)))
				   when (or (not default-p)
					    (member value-selector
						    '(:either :default-only)))
				   do (when default-p (setq v (second v)))
				      (psh (if (eq key :own-slots)
					       `(,slot ,frame ,v)
					     `(:template-slot-of ,slot ,frame
								 ,v))
					   sentences))))
		      ((:own-facets :template-facets)
		       (loop for spec in value
			     for slot = (first-if-list spec)
			     for fspecs = (if (consp spec) (rest spec) nil)
			     for slot-of-key = (if (eq key :own-slots)
						   :slot-of
						 :template-slot-of)
			     do (psh `(,slot-of-key ,slot ,frame) sentences)
			     (loop for fspec in fspecs
				   for facet = (first-if-list fspec)
				   for values = (if (consp fspec)
						    (rest fspec)
						  nil)
				   for facet-of-key = (if (eq key :own-facets)
							  :facet-of
							:template-facet-of)
				   do (psh `(,facet-of-key ,facet ,slot
							   ,frame) 
					   sentences)
				   (loop for v in values
					 for default-p 
					 = (and (consp v)
						(eq :default (first v)))
					 when (or (not default-p)
						  (member value-selector
							  '(:either 
							    :default-only)))
					 do (when default-p
					      (setq v (second v)))
					    (psh (if (eq key :own-facets)
						     `(,facet ,slot ,frame ,v)
						   `(:template-facet-of
						     ,facet ,slot ,frame
						     ,v))
						 sentences)))))))))
	  (values sentences nil more-status)))
      (values nil t nil)))

(defokbcop okbc:get-frame-slots (frame &key (kb (current-kb))
				       (inference-level :taxonomic)
				       (slot-type :all) (kb-local-only-p nil))
  :returned-values (list-of-slots exact-p)
  :manual-category :slot
  :enumerator t
  :doc-string
  "Returns \\karg{list-of-slots}, a list of all the own, template, or own
   and template slots that are associated with \\karg{frame}, depending on the
   value of \\karg{slot-type}."
  :compliance-classes :read
  :tell&ask-default-body
  (ecase slot-type
    (:own (ask-internal `(:slot-of ?x ,frame) kb '?x
			inference-level :all
			t nil (timeout-for-tell&ask-defaults kb)
			:known-true kb-local-only-p))
    (:template (ask-internal `(:template-slot-of ?x ,frame) kb '?x
			     inference-level :all
			     t nil (timeout-for-tell&ask-defaults kb)
			     :known-true kb-local-only-p))
    ;; Don't assume that the tell-and-ask supports :or
    (:all (multiple-value-bind (ownv own-exact-p)
	      (ask-internal `(:slot-of ?x ,frame) kb '?x
			    inference-level :all
			    t nil (timeout-for-tell&ask-defaults kb)
			    :known-true kb-local-only-p)
	    (multiple-value-bind (templatev template-exact-p)
		(ask-internal `(:template-slot-of ?x ,frame) kb '?x
			      inference-level :all
			      t nil (timeout-for-tell&ask-defaults kb)
			      :known-true kb-local-only-p)
	      (values (remove-duplicates (append ownv templatev))
		      (and own-exact-p template-exact-p))))))
  :monitor-body
  (record-reference frame nil t nil kb))

(defokbcop okbc:get-frame-type
    (thing &key (kb (current-kb)) (kb-local-only-p nil))
  :returned-values frame-type
  :manual-category :frame
  :doc-string
  "When \\karg{thing} identifies a frame, returns either
   {\\tt :slot}, {\\tt :facet}, {\\tt :class}, or {\\tt :individual},
   depending on the type of the frame.
   When \\karg{thing} does not identify a frame, \\karg{frame-type} is 
   \\false.  {\\tt :Slot} and {\\tt :facet} will be returned only in
   those systems that support the values {\\tt :slot} and {\\tt :facet},
   respectively, for the {\\tt :are-frames} behavior."
  :default-body
  (multiple-value-bind (frame found-p)
      (coerce-to-frame-internal thing kb nil kb-local-only-p)
    (let ((frame (if found-p frame thing)))
      (or (and found-p
	       (cond ((slot-p-internal frame kb kb-local-only-p)
		      :SLOT)
		     ((facet-p-internal frame kb kb-local-only-p)
		      :FACET)
		     ((class-p-internal frame kb kb-local-only-p)
		      :CLASS)
		     ((individual-p-internal frame kb kb-local-only-p)
		      :INDIVIDUAL)
		     (t nil)))
	  (cond ((slot-p-internal thing kb kb-local-only-p)
		 :SLOT)
		((facet-p-internal thing kb kb-local-only-p)
		 :FACET)
		((class-p-internal thing kb kb-local-only-p) :CLASS)
		((individual-p-internal thing kb kb-local-only-p)
		 :INDIVIDUAL)
		(t nil)))))
  :monitor-body
  (record-reference thing nil t nil kb))


;------------------------------------------------------------------------------

(defokbcop okbc:get-frames-matching
    ((pattern :value) &key (kb (current-kb)) (wildcards-allowed-p t)
     (selector :all) (force-case-insensitive-p nil) (kb-local-only-p nil))
  :enumerator t
  :default-body
  (default-get-frames-matching pattern kb wildcards-allowed-p selector
			       force-case-insensitive-p kb-local-only-p)
  :returned-values (matching-frames longest-matching-substring)
  :manual-category :frame
  :doc-string
  "Given a \\karg{pattern}, which is a string or a symbol,
  finds a set of matching frames for that pattern.
  The match of a frame to a pattern could take into account the frame's name
  (if meaningful), printed representation, pretty-name, or any KB-specific
  feature such as a list of synonyms.

  Returns the following two values:
  \\begin{enumerate}
  \\item \\karg{matching-frames} -- The list of matching frames (which is
         \\emptylist\\ if no matches are found).
  \\item \\karg{longest-matching-substring} -- The longest matching initial
         substring.  This returned value is useful in applications that use
         get-frames-matching to implement a completion facility, or prompt
         users for frames (\\false\\ if no matches are found).
  \\end{enumerate}
  \\karg{Wildcards-allowed-p}
     --- When \\true, the pattern may contain * (zero or more characters)
         and ? (exactly one character) wildcards.  Wildcard characters are
         escaped with the backslash character.  If this argument is \\false,
         the * and ? characters simply denote themselves and need not be
         escaped.
  \\karg{Selector}
     --- May be a procedure (see Section~\\ref{ch:funspecs}) of
         signature
         (candidate-name, kb, kb-local-only-p)
         that returns \\true\\ if the candidate name is to be
         accepted and \\false\\ otherwise, or one of the following keywords:
         \\bitem
           \\item {\\tt :all} -- Select all frames
           \\item {\\tt :class} -- Select only class frames
           \\item {\\tt :individual} -- Select only individual frames
           \\item {\\tt :slot} -- Select only slot frames
           \\item {\\tt :facet} -- Select only facet frames
         \\eitem
  \\karg{Force-Case-Insensitive-P}
     --- When \\true, cause the comparison is to be case-insensitive, 
         irrespective of the IO syntax of the KB.")

(defun default-get-frames-matching (pattern kb wildcards-allowed-p selector
					    force-case-insensitive-p
					    kb-local-only-p)
  (if (and (not wildcards-allowed-p)
	   (or (stringp pattern) (symbolp pattern) (numberp pattern))
	   (not (member nil (get-behavior-values-internal
			     :frame-names-required kb))))
      (get-frames-matching-for-frame-names-required
       pattern kb selector force-case-insensitive-p kb-local-only-p)
      (get-frames-matching-the-hard-way
       pattern kb wildcards-allowed-p selector force-case-insensitive-p
       kb-local-only-p)))

(defokbcgeneric get-frames-matching-the-hard-way
    (pattern kb wildcards-allowed-p selector force-case-insensitive-p
	     kb-local-only-p)
  (:documentation
   "A back end protocol hook to allow back ends to specialize
    <code>get-frames-matching</code> in the hard cases of either the KB
    not supporting the <code>:frame-names-required</code> behavior, or the
    pattern having wildcards.  This function is called when the
    <code>get-frames-matching</code> handler determines that it is dealing with
    the difficult case.  If this is not the case then
    <code>get-frames-matching-for-frame-names-required</code> is called
    instead."))

(defmethod get-frames-matching-the-hard-way
    (pattern kb wildcards-allowed-p selector
	     force-case-insensitive-p
	     kb-local-only-p)
  (let ((matches nil)
	(are-frames (get-behavior-values-internal :are-frames kb))
	(selector-allows-non-frames-p
	 (let ((are-frames (get-behavior-values-internal :are-frames kb)))
	   (or (and (eq selector :all)
		    (loop for type in '(:class :slot :facet :individual)
			  thereis (not (member type are-frames))))
	       (member selector are-frames))))
	(canonical-pattern (canonicalize-pattern pattern)))
    (flet ((doit (frame)
	     (when (or (keywordp selector)
		       (call-procedure-internal selector kb (list frame)))
	       (when (frame-matches-pattern-p
		      frame pattern kb wildcards-allowed-p
		      force-case-insensitive-p kb-local-only-p
		      canonical-pattern)
		 (push frame matches)))))
      (loop for frame in
	    (case selector
	      (:all (if selector-allows-non-frames-p
			nil
			(get-kb-frames-internal kb kb-local-only-p)))
	      (:facet
	       (get-kb-facets-internal      kb :all kb-local-only-p))
	      (:slot
	       (get-kb-slots-internal       kb :all kb-local-only-p))
	      (:class
	       (get-kb-classes-internal     kb :all kb-local-only-p))
	      (:individual
	       (get-kb-individuals-internal kb :all kb-local-only-p))
	      (otherwise   (get-kb-frames-internal kb kb-local-only-p)))
	    when (or (coercible-to-frame-p-internal
		      frame kb kb-local-only-p)
		     selector-allows-non-frames-p)
	    do (doit frame))
      (when (and (eq selector :all) selector-allows-non-frames-p)
	(when (not (member :slot are-frames))
	  (loop for thing in (get-kb-slots-internal
			      kb :all kb-local-only-p)
		do (doit thing)))
	(when (not (member :facet are-frames))
	  (loop for thing
		in (get-kb-facets-internal kb :all kb-local-only-p)
		do (doit thing)))
	(when (not (member :class are-frames))
	  (loop for thing
		in (get-kb-classes-internal kb :all kb-local-only-p)
		do (doit thing)))
	(when (not (member :individual are-frames))
	  (loop for thing
		in (get-kb-individuals-internal kb :all kb-local-only-p)
		do (doit thing))))
      (values matches
	      (if wildcards-allowed-p
		  (longest-common-substring matches kb kb-local-only-p)
		  (if matches pattern ""))))))

(defokbcgeneric get-frames-matching-for-frame-names-required
    (pattern kb selector force-case-insensitive-p kb-local-only-p)
  (:documentation
   "A back end protocol hook to allow back ends to specialize
    <code>get-frames-matching</code> in the case of the KB supporting the
    <code>:frame-names-required</code> behavior.  This function is called
    when the <code>get-frames-matching</code> handler determines that
    it has been called with a non-wildcarded simple frame name reference.
    If this is not the case then <code>get-frames-matching-the-hard-way</code>
    is called instead."))

(defmethod get-frames-matching-for-frame-names-required
    ((pattern t) (kb t) (selector t) (force-case-insensitive-p t)
     (kb-local-only-p t))
  (let ((match (ecase selector
		 (:all
		  (coerce-to-frame-internal pattern kb nil kb-local-only-p))
		 (:slot
		  (coerce-to-slot-internal  pattern kb nil kb-local-only-p))
		 (:facet
		  (coerce-to-facet-internal pattern kb nil kb-local-only-p))
		 (:class
		  (coerce-to-class-internal pattern kb nil kb-local-only-p))
		 (:individual
		  (coerce-to-individual-internal
		   pattern kb nil kb-local-only-p)))))
    (if match
	(values (list match) pattern)
	(if force-case-insensitive-p
	    (get-frames-matching-the-hard-way
	     pattern kb nil selector t kb-local-only-p)
	    (values nil "")))))

(defun pattern-matches-p (canonical-pattern string force-case-insensitive-p)
  (word-matches-pattern
   string canonical-pattern 0
   (if force-case-insensitive-p
       nil
       (not (eq :upcase (user::readtable-case *readtable*))))
   t))

(defparameter *wildcard-alist* '((#\? :single) (#\* :multiple)))

(defmacro base-string-element-type ()
  "A Lisp implementation-independent macro that evaluates to the appropriate
   element type to use to get a base string composed of simple 8-bit
   characters.  This is useful if large strings are to be consed for
   some reason, using a call such as:<br>
   <code>(make-array 10000 :element-type (base-string-element-type))</code>"
  #+Lucid (progn #-dbcs ''string-char
		 #+dbcs ''base-character)
  #+Allegro ''character
  #-(or Allegro Lucid) ''character)

(defun ok-utils:canonicalize-pattern (pattern-string)
  "This function is used by the default wildcard matching code in OKBC.  It
   takes a <code>pattern-string</code> with single or multiple wildcard
   characters such as <code>\"Hell?o *\"</code> and returns a parsed version
   of this string <code>(\"Hell\" :single \"o \" :multiple)</code>"
  (if (symbolp pattern-string)
      (canonicalize-pattern (string pattern-string))
      (if (equal "" pattern-string)
	  nil
	  (let ((initial-chars nil))
	  (multiple-value-bind (wildcard-index type)
	      (loop for index from 0 below (length pattern-string)
		    for char = (aref pattern-string index)
		    for entry = (assoc char *wildcard-alist* :test #'char=)
		    when entry
		    return (values index (second entry))
		    do (if (char= char #\\)
			   (progn (incf index) ;; step past
				  (if (>= index (length pattern-string))
				      nil
				      (push (aref pattern-string index)
					    initial-chars)))
			   (push char initial-chars)))
	    (let ((initial-string
		   (make-array (length initial-chars)
			       :element-type (base-string-element-type)
			       :initial-contents (reverse initial-chars))))
	      (if type
		  (if (> wildcard-index 0)
		      (cons initial-string
			    (cons type (canonicalize-pattern
					(subseq pattern-string
						(+ wildcard-index 1)))))
		      (cons type
			    (canonicalize-pattern
			     (subseq pattern-string (+ wildcard-index 1)))))
		  (list initial-string))))))))

(defun word-matches-pattern
    (string pattern &optional (start 0) (case-sensitive-p nil)
	    (force-match-to-end-p nil))
  "This predicate is true if a <code>string</code> matches the supplied
   <code>pattern</code>, which must be a canonical pattern as returned by
   <code>canonicalize-pattern</code>.  Matching is started at the index
   <code>start</code>, and is case-sensitive if <code>case-sensitive-p</code>
   is true.  If <code>force-match-to-end-p</code> is false, the pattern is
   taken to have an implicit <code>:multiple</code> at the end, otherwise
   the pattern must match the whole string.  Returns the index one past the
   first matching sequence."
  (if pattern
      (case (first pattern)
	(:single
	 (and (>= (length string) start)
	      (word-matches-pattern string (rest pattern) (+ start 1)
				    case-sensitive-p force-match-to-end-p)))
	(:multiple
	 (if (zerop (- (length string) start))
	     start
	     (loop for spread from 0 below (- (length string) start)
		   thereis (word-matches-pattern
			    string (rest pattern) (+ start spread)
			    case-sensitive-p force-match-to-end-p))))
	(otherwise
	 (if (and force-match-to-end-p (not (rest pattern)))
	     (funcall (if case-sensitive-p 'string= 'string-equal)
		      string (first pattern) :start1 start)
	     (and (>= (length string) (+ start (length (first pattern))))
		  (funcall (if case-sensitive-p 'string= 'string-equal)
			   string (first pattern)
			   :start1 start
			   :end1 (+ start (length (first pattern))))
		  (word-matches-pattern
		   string (rest pattern) (+ start (length (first pattern)))
		   case-sensitive-p force-match-to-end-p)))))
      start))

(defgeneric possibilities-for-pattern-matching (thing kb kb-local-only-p)
  (:documentation
   "Back end protocol used when specializing <code>get-frames-matching</code>.
    Given a <code>thing</code>, which may be a frame reference, returns a list
    of objects that may be used when matching against the frame.  The objects
    returned will be used for string comparison if they are generalized strings
    and will be printed to strings if they are not generalized strings."))

(defmethod-with-cache-method possibilities-for-pattern-matching
    (thing (kb (kb structure-kb)) kb-local-only-p)
  (multiple-value-bind (frame found-p)
      (coerce-to-frame-internal thing kb nil kb-local-only-p)
    (if found-p
	(let ((name (get-frame-name-internal frame kb kb-local-only-p))
	      (pretty (get-frame-pretty-name-internal
		       frame kb kb-local-only-p))
	      (handle (get-frame-handle-internal frame kb kb-local-only-p)))
	  (remove nil (list name pretty handle)))
	(list thing))))

(defun kb-prin1-to-string (thing kb kb-local-only-p)
  (implement-with-kb-io-syntax-internal
   #'(lambda () (let ((*print-readably* nil)) (prin1-to-string thing)))
   kb :file kb-local-only-p))

(defmethod-with-cache-method frame-matches-pattern-p
    (frame pattern (kb (kb structure-kb))
	   wildcards-allowed-p force-case-insensitive-p kb-local-only-p
	   &optional (canonical-pattern nil))
  (let ((reps (possibilities-for-pattern-matching frame kb kb-local-only-p)))
    (if (and wildcards-allowed-p
	     (or (not canonical-pattern)
		 (or (> (length canonical-pattern) 1)
		     (not (stringp (first canonical-pattern))))))
	(let ((canonical-pattern (or canonical-pattern
				     (canonicalize-pattern pattern))))
	  (loop for rep in reps
		thereis (typecase rep
			  ((or string symbol)
			   (pattern-matches-p canonical-pattern (string rep)
					      force-case-insensitive-p))
			  (otherwise
			   (pattern-matches-p
			    canonical-pattern
			    (kb-prin1-to-string rep kb kb-local-only-p)
			    force-case-insensitive-p)))))
	(let ((test (if force-case-insensitive-p
			#'string-equal
			(if (eq (user::readtable-case *readtable*) :upcase)
			    ;; This is the default for readtables.
			    #'string-equal
			    #'string=))))
	  (loop for rep in reps
		thereis (typecase rep
			  (string (funcall test pattern rep))
			  (symbol (funcall test pattern (symbol-name rep)))
			  (otherwise
			   (funcall test pattern
				    (kb-prin1-to-string
				     rep kb kb-local-only-p)))))))))

(defmethod-with-cache-method longest-common-substring
    (frames (kb (kb structure-kb)) kb-local-only-p)
  (let ((alist (loop for frame in frames
		     collect (possibilities-for-pattern-matching
			      frame kb kb-local-only-p))))
    (if (rest frames)
	(longest-common-substring-internal alist kb kb-local-only-p)
	(if frames
	    (first (possibilities-for-pattern-matching
		    (first frames) kb kb-local-only-p))
	    ""))))

(defun longest-common-substring-internal
    (alist kb kb-local-only-p)
  (let ((chars nil))
    (flet ((ensure-string (location)
	     (let ((thing (first location)))
	       (typecase thing
		 (null nil)
		 (string thing)
		 (symbol (setf (first location) (symbol-name thing)))
		 (otherwise
		  (setf (first location)
			(kb-prin1-to-string
			 thing kb kb-local-only-p)))))))
      (loop for index from 0
	    for char = nil
	    when (not (loop for posses in alist
			    always
			    (and posses
				 (loop with found-p = nil
				       for pos on posses
				       for string = (ensure-string pos)
				       for match-p
				       = (and string
					      (< index (length string))
					      (if char
						  (char= char (char string
								    index))
						  (progn
						    (setq char
							  (char string
								index))
						    t)))
				       when (not match-p)
				       do (setf (first pos) nil)
				       when match-p do (setq found-p t)
				       finally (return found-p) ))))
	    return index
	    do (push char chars))
      (make-array (length chars) :initial-contents (reverse chars)
		  :element-type (base-string-element-type)))))

;------------------------------------------------------------------------------

(defokbcop okbc:get-frames-with-facet-value (slot facet value
						  &key (kb (current-kb))
						  (inference-level :taxonomic)
						  (slot-type :own)
						  (value-selector :either)
						  (kb-local-only-p nil))
  :returned-values (frames exact-p)
  :manual-category :facet
  :doc-string
  "Returns the set of frames in which the specified facet value is accessible
   on the specified slot.
   If the system is unable to find any frame/slot/facet combinations with the
   specified value, \\emptylist\\ is returned.
   This operation allows user interfaces to take users from a value
   displayed as a facet value on a particular frame/slot to the place
   that asserted the value."
  :standard-default-body
  ;; This default default doesn't do any taxonomic inferences.  If you
  ;; want those you should use default-inheritance-mixin.  The default default
  ;; maps over all of the frame sin the KB, so you should probably optimise it.
  (default-direct-get-frames-with-facet-value
      slot facet value kb inference-level slot-type value-selector
      kb-local-only-p)
  :tell&ask-default-body
  (if (eql slot-type :all)
      (multiple-value-bind (own own-exact?)
	(get-frames-with-facet-value-internal
	 slot facet value kb inference-level
	 :own value-selector kb-local-only-p)
	(multiple-value-bind (template template-exact?)
	  (get-frames-with-facet-value-internal
	   slot facet value kb inference-level
	   :template value-selector kb-local-only-p)
	  (values
	   (append own template)
	   (and own-exact? template-exact?))))
      (ask-internal (ecase slot-type
		      (:own `(,facet ,slot ?frame ,value))
		      (:template
		       `(:template-facet-value ,facet ,slot ?frame ,value)))
		    kb '?frame inference-level :all
		    t nil (timeout-for-tell&ask-defaults kb)
		    value-selector kb-local-only-p))
  :monitor-body
  (record-reference frame slot t nil kb))

(defokbcop okbc:get-frames-with-slot-value (slot value
						 &key (kb (current-kb))
						 (inference-level :taxonomic)
						 (slot-type :own)
						 (value-selector :either)
						 (kb-local-only-p nil))
  :returned-values (frames exact-p)
  :manual-category :slot
  :doc-string
  "Returns the set of frames in which the specified slot value is accessible.
   If the system is unable to find any frame/slot combinations with the
   specified value, \\emptylist\\ is returned.
   This operation allows user interfaces to take users from a value
   displayed as a slot value on a particular frame to the place that
   asserted the value."
  :standard-default-body
  ;; This default default doesn't do any taxonomic inferences.  If you
  ;; want those you should use default-inheritance-mixin.  The default default
  ;; maps over all of the frame sin the KB, so you should probably optimise it.
  (default-direct-get-frames-with-slot-value
      slot value kb inference-level slot-type value-selector
      kb-local-only-p)
  :tell&ask-default-body
  (if (eql slot-type :all)
      (multiple-value-bind (own own-exact?)
	(get-frames-with-slot-value-internal
	 slot value kb inference-level :own value-selector kb-local-only-p)
	(multiple-value-bind (template template-exact?)
	  (get-frames-with-slot-value-internal
	   slot value kb inference-level :template
	   value-selector kb-local-only-p)
	  (values
	   (append own template)
	   (and own-exact? template-exact?))))
      (ask-internal
       (ecase slot-type
	 (:own `(,slot ?frame ,value))
	 (:template `(:template-slot-value ,slot ?frame ,value)))
       kb '?frame inference-level :all
       t nil (timeout-for-tell&ask-defaults kb) value-selector kb-local-only-p))
  :monitor-body
  (record-reference frame slot t nil kb))

(defokbcop okbc:get-instance-types
    (frame &key (kb (current-kb))
	   (inference-level :taxonomic)
	   (number-of-values :all) (kb-local-only-p nil))
  :enumerator t
  :doc-string
  "Returns the \\karg{list-of-types} of \\karg{frame}, that is, the list of 
   classes of which \\karg{frame} is an instance."
  :compliance-classes :read
  :returned-values (list-of-types exact-p more-status)
  :tell&ask-default-body
  (ask-internal `(:instance-of ,frame ?x) kb '?x
		inference-level number-of-values
		t nil (timeout-for-tell&ask-defaults kb)
		:known-true kb-local-only-p)
  :manual-category :instance
  :monitor-body
  (record-reference frame nil t nil kb))


(defokbcop okbc:get-kb-behaviors
    (&key (kb-type-or-kb (current-kb)) (connection (local-connection)))
  :returned-values list-of-behaviors
  :manual-category :behavior
  :doc-string
  "When \\karg{kb-type-or-kb} is either a KB or a kb-type, returns
   \\karg{list-of-behaviors}, which is a list of keywords naming all
   the behaviors recognized by this KB, or identified by the kb-type,
   respectively."
  :arguments-to-kb-specialize (kb-type-or-kb)
  :compliance-classes :read)

(defokbcop okbc:get-kb-classes
    (&key (kb (current-kb)) (selector :system-default)
	  (kb-local-only-p nil))
  :returned-values list-of-classes
  :manual-category :class
  :enumerator t
  :doc-string
  "Returns \\karg{list-of-classes}, a list of the classes in the KB.
   \\karg{Selector} can be one of the following:
   \\bitem
   \\item {\\tt :all} -- Returns all classes
   \\item {\\tt :frames} -- Returns classes that are represented as frames
   \\item {\\tt :system-default} -- Returns either all classes or
          only class frames, according to which is the KRS's default
   \\eitem"
  :standard-default-body
  ((declare (ignore selector))
   (loop for frame in (get-kb-frames-internal kb kb-local-only-p)
	when (class-p-internal frame kb kb-local-only-p)
	collect frame))
  :tell&ask-default-body
  (ask-internal (ecase selector
		  ((:all :system-default) `(:class ?x))
		  (:frames `(:and (:class ?x) (:frame ?x))))
		  kb '?x
		(inference-level-for-tell&ask-defaults kb) :all
		t nil (timeout-for-tell&ask-defaults kb)
		:known-true kb-local-only-p))


(defokbcop okbc:get-kb-direct-children (&key (kb (current-kb)))
  :returned-values list-of-child-kbs
  :enumerator t
  :manual-category :kb
  :default-body
  (loop for some-kb in (get-kbs-of-type-internal kb (connection kb))
	when (member kb (get-kb-direct-parents-internal some-kb) :test #'eq)
	collect some-kb)
  :doc-string
   "Returns the \\karg{list-of-child-kbs} -- that is, the list of KBs that
    directly include \\karg{kb}.  Note that certain KB implementations may
    allow circular inclusion dependencies in KBs.  The semantics of KB
    inclusion are not specified by OKBC, but where possible, processing can
    be limited to a particular KB by the use of the \\karg{kb-local-only-p}
    argument.")

(defokbcop okbc:get-kb-direct-parents (&key (kb (current-kb)))
  :returned-values list-of-parent-kbs
  :manual-category :kb
  :enumerator t
  :default-body nil
  :doc-string
   "Returns the \\karg{list-of-parent-kbs} -- that is, the list of KBs directly
    included by \\karg{kb}.  Note that certain KB implementations may allow
    circular inclusion dependencies in KBs.  The semantics of KB inclusion
    are not specified by OKBC, but where possible, processing can be limited
    to a particular KB by the use of the \\karg{kb-local-only-p} argument.")

(defokbcop okbc:get-kb-facets
    (&key (kb (current-kb)) (selector :system-default)
	  (kb-local-only-p nil))
  :returned-values list-of-facets
  :manual-category :facet
  :enumerator t
  :doc-string
  "Returns the \\karg{list-of-facets} in \\karg{kb}.
   \\karg{Selector} can be one of the following:
   \\bitem
   \\item {\\tt :all} -- Returns all facets
   \\item {\\tt :frames} -- Returns facets that are represented as frames
   \\item {\\tt :system-default} -- Returns either all facets or
          only facets represented as frames, according to which is the KRS's
          default
   \\eitem"
  :standard-default-body
  (let (all-facets)
    (loop for frame in (get-kb-frames-internal kb kb-local-only-p)
	  for these-facets = (get-frame-facets
			      frame kb :all-inferable :all kb-local-only-p)
	  for selected-facets = (ecase selector
				  ((:all :system-default) these-facets)
				  (:frames
				   (loop for facet in these-facets
					 when (coercible-to-frame-p-internal
					       facet kb kb-local-only-p)
					 collect facet)))
	  do (setq all-facets (union all-facets selected-facets))
	     (when (facet-p-internal frame kb kb-local-only-p)
	       (pushnew frame all-facets)))
    all-facets)
  :tell&ask-default-body
  (ask-internal (ecase selector
		  ((:all :system-default) `(:facet ?x))
		  (:frame `(:and (:facet ?x) (:frame ?x))))
		kb '?x
		(inference-level-for-tell&ask-defaults kb) :all
		t nil (timeout-for-tell&ask-defaults kb)
		:known-true kb-local-only-p))


(defokbcop okbc:get-kb-frames (&key (kb (current-kb)) (kb-local-only-p nil))
  :returned-values list-of-frames
  :manual-category :frame
  :enumerator t
  :doc-string
  "Returns the \\karg{list-of-frames} in the KB, including class, slot,
   facets and individual frames, when present."
  :tell&ask-default-body
  (ask-internal `(:frame ?x) kb '?x
		(inference-level-for-tell&ask-defaults kb) :all
		t nil (timeout-for-tell&ask-defaults kb)
		:known-true kb-local-only-p)
  :compliance-classes :read)

(defokbcop okbc:get-kb-individuals
    (&key (kb (current-kb)) (selector :system-default)
	  (kb-local-only-p nil))
  :returned-values list-of-individuals
  :manual-category :individual
  :enumerator t
  :doc-string
  "Returns \\karg{list-of-individuals}, a list of the individual frames in
   \\karg{kb}.  \\karg{Selector} can be one of the following:
   \\bitem
   \\item {\\tt :all} -- Returns all accessible individuals
   \\item {\\tt :frames} -- Returns only individuals that are frames
   \\item {\\tt :system-default} -- Returns either all individuals or
          only individual frames, according to which is the KRS's default
   \\eitem"
  :standard-default-body
  ((declare (ignore selector))
   (loop for frame in (get-kb-frames-internal kb kb-local-only-p)
		      when (not (class-p-internal frame kb kb-local-only-p))
		      collect frame))
  :tell&ask-default-body
  (ask-internal (ecase selector
		  ((:all :system-default) `(:individual ?x))
		  (:frames `(:and (:individual ?x) (:frame ?x))))
		kb '?x
		(inference-level-for-tell&ask-defaults kb) :all
		t nil (timeout-for-tell&ask-defaults kb)
		:known-true kb-local-only-p))


(defokbcop okbc:get-kb-roots
    (&key (kb (current-kb)) (selector :all) (kb-local-only-p nil))
  :returned-values list-of-roots
  :manual-category :class
  :enumerator t
  :doc-string
  "Every KB has one or more frames at the top (root) of the
   KB.  A frame $C$ is a root of the KB $K$ if there exists no class $D$ such
   that $D$ is a superclass of $C$ and $D$ is in the KB $K$ and if there
   exists no class $E$ such that $E$ is a type of $C$ and $E$ is in the
   KB $K$, or available in $K$ when \\karg{kb-local-only-p} is \\false.  This
   operation identifies and returns those roots, the \\karg{list-of-roots}.
   Note that this means that unparented individuals, slots and facets will
   also be returned.

   Some KRSs allow {\\em user-defined} classes to be roots of a KB, whereas
   other KRSs always import certain {\\em system-defined} classes (for example,
   {\\em thing}) into each KB and force all
   user classes to be subclasses of {\\em thing.} These system-defined classes
   may normally be invisible to the user in some KRSs.  The
   \\karg{selector} argument controls which root classes are returned as
   follows:

   \\bitem
   \\item {\\tt selector = :all} returns all the true root classes of the 
          KB, regardless of whether they are {\\em system-defined} or 
          {\\em user-defined}.
   \\item {\\tt selector = :user} returns the user-defined
   root classes of the KB, namely all classes $C$ available in the KB such that
   $C$ was defined by a user application as opposed to being a built-in
   part of every KB, and such that there exists no class $D$ that is both
   {\\em user-defined} and a superclass of $C$.  That is, there may
   exist {\\em system-defined} superclasses of $C$.
   \\eitem

   If \\karg{kb-local-only-p} is \\true, the list returned may return only
   the root classes defined in \\karg{kb} itself; classes that were
   inherited from other (included) KBs may be excluded.  This means
   that a class that has superclasses in some KB included by \\karg{kb},
   but has no superclasses defined in \\karg{kb}, may be returned as a
   root class if \\karg{kb-local-only-p} is \\true.

   %%%%Old definition:
   %%%%Returns the set of classes in \\karg{kb} that have no superclasses in
   %%%%the specified KB."
  :Default-Body
  ((declare (ignore selector))
   (let ((classes nil))
     (loop for frame in (get-kb-classes-internal kb :frames kb-local-only-p)
	   do (when (and (frame-in-kb-p-internal frame kb kb-local-only-p)
			 (let ((superclasses
				(get-class-superclasses-internal
				 frame kb :direct :all kb-local-only-p)))
			   (not (loop for class in superclasses
				      thereis (frame-in-kb-p-internal
					       class kb
					       kb-local-only-p)))))
		(push frame classes)))
     classes)))


(defokbcop okbc:get-kb-slots (&key (kb (current-kb)) (selector :system-default)
				   (kb-local-only-p nil))
  :returned-values list-of-slots
  :manual-category :slot
  :enumerator t
  :doc-string
  "Returns the \\karg{list-of-slots} that are defined in the KB.
   \\karg{Selector} can be one of the following:
   \\bitem
   \\item {\\tt :all} -- Returns all slots
   \\item {\\tt :frames} -- Returns slots that are represented frames
   \\item {\\tt :system-default} -- Returns either all slots or
          only slot frames, according to which is the KRS's default
   \\eitem"
  :standard-default-body
  (let (all-slots)
    (loop for frame in (get-kb-frames-internal kb kb-local-only-p)
	  for these-slots = (get-frame-slots-internal
			     frame kb :all-inferable :all
			     kb-local-only-p)
	  for selected-slots = (ecase selector
				 ((:all :system-default) these-slots)
				 (:frames
				  (loop for slot in these-slots
					when (coercible-to-frame-p-internal
					      slot kb kb-local-only-p)
					collect slot)))
	  do (setq all-slots (union all-slots selected-slots))
	     (when (slot-p-internal frame kb kb-local-only-p)
	       (pushnew frame all-slots)))
    all-slots)
  :tell&ask-default-body
  (ask-internal (ecase selector
		  ((:all :system-default) `(:slot ?x))
		  (:frame `(:and (:slot ?x) (:frame ?x))))
		kb '?x
		(inference-level-for-tell&ask-defaults kb) :all
		t nil (timeout-for-tell&ask-defaults kb)
		:known-true kb-local-only-p))


;------------------------------------------------------------------------------

(defokbcop okbc:get-kb-type (thing &key (connection (local-connection)))
  :manual-category :kb
  :returned-values kb-type
  :doc-string
  "Returns the \\karg{kb-type} object for \\karg{thing}, which may be a KB,
   a kb-locator, or a kb-type name.  KB-type names are KRS-specific, and
   will be documented with the KRS being used.  KB-type names need never be
   used, since a kb-type can be selected by a user or application by using
   the \\kfn{get-kb-types} and \\kfn{frs-name} operations.  It is not
   portable to specify a kb-type name as a literal in an OKBC program."
  :default-body
  ((declare (ignore connection))
   (continuable-error "Cannot coerce ~S to a kb-type." thing)))

(defmethod get-kb-type-internal ((thing #-MCL clos::standard-class
					#+MCL cl::standard-class)
				 (connection t))
  (class-prototype-safe thing))

(defmethod get-kb-type-internal ((thing #-MCL clos::structure-class
					#+MCL cl::structure-class)
				 (connection t))
  (class-prototype-safe thing))

(defmethod get-kb-type-internal ((thing kb) (connection t))
  (get-kb-type-internal (class-of thing) connection))

(defmethod get-kb-type-internal ((thing symbol) (connection local-connection))
  (let ((class (concrete-kb-class-from-abstract-kb-class-name thing)))
    (if class
	(get-kb-type-internal class connection)
	(call-next-method))))

(defmethod get-kb-type-internal ((thing structure-kb) (connection t))
  (get-kb-type-internal (class-of thing) connection))

(defmethod get-kb-type-internal ((thing (eql nil)) (connection t))
  (continuable-error "No kb-type provided."))

(defmethod get-kb-type-internal ((thing symbol) (connection t))
  (let ((cl (find-class thing nil)))
    (if (and cl
	     (or (subtypep thing 'kb)
		 (subtypep thing 'structure-kb)))
	(get-kb-type-internal cl connection)
	(continuable-error "Cannot coerce ~S to a kb-type." thing))))

(defmethod get-kb-type-internal
    ((thing ok-back:abstract-kb-locator) (connection t))
  (ok-back:kb-type thing))
  
;------------------------------------------------------------------------------

(defokbcop okbc:get-kb-types (&key (connection (local-connection)))
  :enumerator t
  :returned-values list-of-kb-types
  :manual-category :kb
  :doc-string
  "Returns a list of KB types for each of the known KRSs accessible
   through the \\karg{connection}.  \\karg{List-of-kb-types} contains one
   kb-type entry for each KRS known through the connection, and possibly also
   kb-type objects representing supertypes of the KRSs supported."
  :default-body
  (get-kb-types-from-meta-kb (meta-kb-internal connection)))

(defokbcop okbc:get-kbs (&key (connection (local-connection)))
  :returned-values list-of-kbs
  :enumerator t
  :manual-category :kb
  :doc-string
  "Returns a \\karg{list-of-kbs} containing all the known KBs accessible 
   through the \\karg{connection}, irrespective of the KB's implementation
   type.  Note: the connection from which each of the KBs returned was derived
   is not necessarily the same as the value of the \\karg{connection}
   argument.  Later processing of any of these KBs should be done with
   respect to the connection returned when the \\kfn{connection} operation
   is applied to the KB."
  :default-body
  (get-kbs-from-meta-kb (meta-kb-internal connection) connection))

(defmethod get-kbs-from-meta-kb ((meta-kb t) (connection t))
  (remove-duplicates
   (loop for kb-type in (get-kb-types-internal connection)
	 append (get-kbs-of-type-internal
		 kb-type (connection-arg-default kb-type connection)))))

;==============================================================================

(defokbcop okbc:get-kbs-of-type
    (&key (kb-type nil) (connection (local-connection)))
  :returned-values list-of-kbs
  :manual-category :kb
  :enumerator t
  :doc-string
  "Returns \\karg{list-of-kbs}, the list of all the known KBs whose type
   matches \\karg{kb-type}, and that are accessible through the
   \\karg{connection}."
  :compliance-classes :read
  :arguments-to-kb-specialize (kb-type))

;; This stuff is a little subtle.  We hook in a default method on the
;; get-kbs-of-type-internal hook only specialized on standard-object and
;; structure-object, not KB and Structure-KB.  We call a default that
;; recurses down over subclasses if we are in any of the know-to-be
;; abstract kb classes.  If we ever hit a concrete kb class then the
;; user should have provided his own get-kbs-of-type-internal method
;; to be compliant.

;; These removed at Brad Miller's suggestion.  Apparently this stuff
;; doesn't work too well in Franz.
;(defmethod no-applicable-method ((gf (eql #'get-kbs-of-type-internal))
;                                 &rest args)
;  (declare (ignore args))
;  (throw :use-default :use-default))
;
;(defmethod no-next-method
;    ((gf (eql #'get-kbs-of-type-internal)) (method t) &rest args)
;  (declare (ignore args))
;  (throw :use-default :use-default))

;(defmethods get-kbs-of-type-internal
;  ((kb-type (standard-object structure-object)) (connection local-connection))
;  (let ((type (type-of kb-type)))
;    (if (member type ok-back:*abstract-kb-class-names*)
;        (default-local-get-kbs-of-type kb-type)
;        (call-next-method))))

(defvar *inside-default-local-get-kbs-of-type* nil)

(defmethods get-kbs-of-type-internal 
    ((kb-type (standard-object structure-object)) (connection local-connection))
  (let ((type (type-of-name kb-type)))
    (cond ((member type ok-back:*abstract-kb-class-names*)
	   (default-local-get-kbs-of-type kb-type))
	  ((next-method-p) (call-next-method))
	  (*inside-default-local-get-kbs-of-type*
	   (throw :use-default :use-default))
	  (t (error 'okbc:method-missing :okbcop 'okbc:get-kbs-of-type
		    :kb kb-type)))))

(defmethod default-local-get-kbs-of-type ((kb-type t))
  (remove-duplicates
   (let ((localcon (local-connection)))
     (loop for class in (clos::class-direct-subclasses
			 (class-of (get-kb-type-internal kb-type localcon)))
	   for class-type = (get-kb-type-internal class localcon)
	   append (let ((result (catch :use-default
				  (let ((*inside-default-local-get-kbs-of-type*
					 t))
				    (get-kbs-of-type-internal
				     class-type localcon)))))
		    (if (eq result :use-default)
			(default-local-get-kbs-of-type class-type)
			result))))))

;==============================================================================

(defokbcop okbc:get-procedure ((name :value) &key (kb (current-kb)))
  :returned-values procedure
  :manual-category :funspec
  :doc-string
  "Returns the \\karg{procedure} that is the procedure association for
   the \\karg{name}, or \\false\\ if there is no such procedure association.
   See \\kfn{register-procedure}, \\kfn{unregister-procedure}, and
   \\kfn{call-procedure}."
  :default-body
  ((continuable-assert (symbolp name) ()
		       "Illegal argument ~S to get-procedure" name)
   (if name
       (gethash (string-upcase name)
		(name-to-procedure-table kb))
       (continuable-error "NIL cannot name a procedure."))))

(defokbcop okbc:get-slot-facets (frame slot &key (kb (current-kb))
				       (inference-level :taxonomic)
				       (slot-type :own) (kb-local-only-p nil))
  :returned-values (list-of-facets exact-p)
  :manual-category :facet
  :enumerator t
  :doc-string
  "Returns the \\karg{list-of-facets} associated with \\karg{slot} in
   \\karg{frame}."
  :compliance-classes (:read :facets)
  :tell&ask-default-body
  (ecase slot-type
    (:own (ask-internal `(:facet-of ?x ,slot ,frame) kb '?x
			inference-level :all
			t nil (timeout-for-tell&ask-defaults kb)
			:known-true kb-local-only-p))
    (:template (ask-internal `(:template-facet-of ?x ,slot ,frame) kb '?x
			     inference-level :all
			     t nil (timeout-for-tell&ask-defaults kb)
			     :known-true kb-local-only-p))
    ;; Don't assume that the tell&ask knows how to do :OR.
    (:all (multiple-value-bind (ownv own-exact-p)
	      (ask-internal `(:facet-of ?x ,slot ,frame) kb '?x
			    inference-level :all
			    t nil (timeout-for-tell&ask-defaults kb)
			    :known-true kb-local-only-p)
	    (multiple-value-bind (templatev template-exact-p)
		(ask-internal `(:template-facet-of ?x ,slot ,frame) kb '?x
			      inference-level :all
			      t nil (timeout-for-tell&ask-defaults kb)
			      :known-true kb-local-only-p)
	      (values (remove-duplicates (append ownv templatev))
		      (and own-exact-p template-exact-p))))))
  :monitor-body
  (record-reference frame slot t nil kb))


(defokbcop okbc:get-slot-type (frame slot &key (kb (current-kb))
				     (inference-level :taxonomic)
				     (kb-local-only-p nil))
  :returned-values slot-type
  :manual-category :slot
  :doc-string
  "Returns one of \\{{\\tt :own}, {\\tt :template}, \\false\\} to
   identify the \\karg{slot-type} of the slot on question.  If there are both
   an own and a template slot on \\karg{frame} identified by \\karg{slot}, then
   {\\tt :own} is returned.
   If no such slot is known, then \\false\\ is returned."
  :default-body
  (let ((testfn (decanonicalize-testfn :eql kb kb-local-only-p)))
    (cond ((member slot (get-frame-slots-internal
			 frame kb inference-level :own kb-local-only-p)
		   :test testfn)
	   :own)
	  ((member slot (get-frame-slots-internal
			 frame kb inference-level :template kb-local-only-p)
		   :test testfn)
	   :template)
	  (t nil)))
  :monitor-body
  (record-reference frame slot t nil kb))

(defokbcop okbc:get-slot-value
	  (frame slot &key (kb (current-kb)) (inference-level :taxonomic)
		 (slot-type :own) (value-selector :either)
		 (kb-local-only-p nil))
  :returned-values (value-or-false exact-p)
  :manual-category :slot
  :doc-string
  "Returns the single member of the set of values
   of the \\karg{slot}.  This operation is meaningful only for single-valued
   slots.  It is an error to call \\kfn{get-slot-value} on a non-single-valued 
   slot, and implementations should signal a \\kcond{cardinality-violation} if 
   this occurs.  When there is no value for the slot, \\karg{value-or-false} 
   is \\false."
  :default-body
  (multiple-value-bind (values exact-p)
      (get-slot-values-internal
       frame slot kb inference-level slot-type 2 value-selector 
       kb-local-only-p)
    (when (rest values)
      (error 'cardinality-violation
	     :frame frame
	     :slot slot
	     :kb kb
	     :slot-type slot-type
	     :constraint "Single valued slot"
	     :error-message (format nil "Cardinality should be 1 during ~
                                         (get-slot-value ~S ~S ...)"
				    frame slot)))
    (values (first values) exact-p))
  :monitor-body
  (record-reference frame slot t nil kb))

(defokbcop okbc:get-slot-values (frame slot
				       &key (kb (current-kb))
				       (inference-level :taxonomic)
				       (slot-type :own) (number-of-values :all)
				       (value-selector :either)
				       (kb-local-only-p nil))
  :returned-values (list-of-values exact-p more-status)
  :manual-category :slot
  :enumerator t
  :doc-string
  "Returns the \\karg{list-of-values} of \\karg{slot}
   within \\karg{frame}.  If the {\\tt :collection-type} of the slot is
   {\\tt :list}, and only {\\tt :direct} own slots have been asserted, then
   order is preserved; otherwise, the values are returned in no guaranteed
   order.  \\kfn{Get-slot-values} always returns a list of
   values.  If the specified slot has no values, \\emptylist\\ is 
   returned."
  :standard-default-body
  (multiple-value-bind (list-of-specs exact-p more-status)
      (get-slot-values-in-detail-internal frame slot kb inference-level
					  slot-type number-of-values
					  value-selector kb-local-only-p)
    ;; We need to remove-duplicates because get-slot-values-in-detail
    ;; may return default values subsumed by true values, and also
    ;; inherited values that are considered distinct from direct ones.
    (values (remove-duplicates-using-trie-and-coercion
	     (mapcar #'first list-of-specs)
	     (maybe-coerce-to-frame-fun kb kb-local-only-p))
	    exact-p more-status))
  :compliance-classes :read
  :tell&ask-default-body
  ((ask-internal (ecase slot-type
		   (:own `(,slot ,frame ?x))
		   (:template `(:template-slot-value ,slot ,frame ?x)))
		 kb '?x inference-level number-of-values
		 t nil (timeout-for-tell&ask-defaults kb)
		 value-selector kb-local-only-p))
  :monitor-body
  (record-reference frame slot t nil kb))

(defokbcop okbc:get-slot-values-in-detail
    (frame slot
	   &key (kb (current-kb))
	   (inference-level :taxonomic)
	   (slot-type :own) (number-of-values :all)
	   (value-selector :either)
	   (kb-local-only-p nil))
  :returned-values (list-of-specs exact-p more-status default-p)
  :manual-category :slot
  :enumerator t
  :doc-string
  "Returns the \\karg{list-of-specs} describing the values
   of \\karg{slot} within \\karg{frame}.  If the {\\tt :collection-type} 
   of the slot is {\\tt :list}, and only {\\tt :direct} own slots have been 
   asserted, then order is preserved; otherwise, the values are returned in 
   no guaranteed order. \\kfn{Get-slot-values-in-detail} always returns a
   list of specifications as its \\karg{list-of-specs} value.  If the specified
   slot has no values, \\emptylist\\ is returned.

   Each spec is a 3-tuple of the form (value direct-p default-p).
   \\bitem
   \\item value -- A value of the slot
   \\item direct-p -- A flag that is \\true\\ if the value is known to be
                      directly asserted for the slot and \\false\\ otherwise 
   \\item default-p -- A flag that is \\true\\ if the value is known to be
                       a default value, and \\false\\ otherwise
   \\eitem
   The \\karg{default-p} returned value is true if the \\karg{list-of-specs}
   is \\emptylist, and the fact that there are no values is itself a default."
  :compliance-classes :read
  :tell&ask-default-body
  ((multiple-value-bind (list-of-specs exact-p more-status)
       (ask-internal (ecase slot-type
		       (:own `(,slot ,frame ?x))
		       (:template `(:template-slot-value ,slot ,frame ?x)))
		     kb `(?x ,(eq inference-level :direct) nil)
		     inference-level number-of-values
		     t nil (timeout-for-tell&ask-defaults kb)
		     value-selector kb-local-only-p)
     (values list-of-specs exact-p more-status nil)))
  :monitor-body
  (record-reference frame slot t nil kb))

(defokbcop okbc:okbc-condition-p (thing)
  :returned-values boolean
  :manual-category :condition
  :doc-string
  "Returns \\true\\ if \\karg{thing} is an OKBC-defined condition object, and
   \\false\\ otherwise."
  :default-body ((declare (ignore thing)) nil))

(defokbcop okbc:goto-kb (kb)
  :returned-values :void
  :manual-category :kb
  :doc-string
  "Makes \\karg{kb} the current KB.  After a call to \\kfn{goto-kb}, the value
   of a call to \\kfn{current-kb} will be \\karg{kb}.  The newly established
   \\kfn{current-kb} will be used as the default value for the \\karg{kb}
   argument by language bindings that support argument defaulting.  Returns
   no values."
  :causes-side-effects-p t
  :default-body
  (let ((real-kb (kb-object kb)))
    (setq *current-kb* real-kb)
    (setf **kb** real-kb)
    (values)))
  
(defokbcop okbc:has-more (enumerator)
  :returned-values boolean
  :doc-string
  "Returns \\true\\ if the \\karg{enumerator} has more values, otherwise
   returns \\false."
  :manual-category :enumerator
  :default-body (enumerator-has-more enumerator))

(defokbcop ok-back:implement-with-kb-io-syntax
    (procedure &key (kb (current-kb)) (purpose :file) (kb-local-only-p nil))
  :returned-values values
  :manual-category :misc
  :which-ends (:back)
  :doc-string
  "This is an internal implementation substrate for the
   \\kfn{with-kb-io-syntax} macro.  \\karg{Procedure} is executed with the I/O
   environment bound in a manner suitable to the KB and the given purpose.
   The \\karg{purpose} argument has the same interpretation as the same
   argument \\kfn{value-as-string}.
   Note: this functionality is independent of the pretty-names of frames
   being displayed by a user interface tool.  The bindings established
   by {\\tt with-kb-io-syntax} will apply, for example, to slot and facet
   values whether they are frames or not."
  :default-body
  ((declare (ignore kb-local-only-p))
   (ecase purpose
     (:user-interface (let ((*print-readably* nil)
			    (*print-escape* nil))
			(funcall procedure)))
     (:file (with-standard-io-syntax (funcall procedure))))))

(defmethod ok-back:implement-with-kb-io-syntax-internal :around
  ((procedure t) (kb tuple-kb) (purpose t) (kb-local-only-p t))
 (let ((*current-kb-for-io-syntax* kb)
       (*current-purpose-for-io-syntax* purpose))
   (call-next-method)))

(defmacro with-kb-io-syntax
    ((&key (kb '(current-kb)) (purpose :file) (kb-local-only-p nil))
     &body body)
  "A useful macro that executes its body in the appropriate IO environment
   for the KB.  This macro will only have the desired effect either within
   a back end implementation, or in applications that are directly coupled to
   a KB (not using a network connection).  It is useful because it makes sure
   that all IO that occurs within the dynamic extent of the body forms will be
   run in the right IO environment.  This means that random IO such as trace
   and debug prints will get the right IO syntax.<P>

   Because it doesn't work in a network setting, use of this macro in an
   application is non-portable, and is no substitute for correct use of
   coerce-to-kb-value, get-frames-matching and value-as-string, however
   an application will probably be easier to develop and debug if at the
   outer level it does something like the following (given a KB called kb):
   <PRE>
   (if (typep kb 'ok-back:network-kb)
       (actuall-run-my-application kb)
       (with-kb-io-syntax (:kb kb :purpose :user-interface)
         (actuall-run-my-application kb)))
   </PRE>"
  `(implement-with-kb-io-syntax #'(lambda () ,@body)
    :kb ,kb :purpose ,purpose :kb-local-only-p ,kb-local-only-p))

(defokbcop okbc:individual-p
    (thing &key (kb (current-kb)) (kb-local-only-p nil))
  :returned-values boolean
  :manual-category :individual
  :doc-string
  "Returns \\true\\ if \\karg{thing} identifies an individual entity, and
   returns \\false\\ if \\karg{thing} identifies a class."
  :standard-default-body (not (class-p-internal thing kb kb-local-only-p))
  :tell&ask-default-body
  (first (ask-internal `(:individual ,thing)
		       kb t
		       (inference-level-for-tell&ask-defaults kb)
		       1 t nil (timeout-for-tell&ask-defaults kb)
		       :known-true kb-local-only-p))
  :monitor-body
  (record-reference thing nil t nil kb))


(defokbcop okbc:instance-of-p (thing class &key (kb (current-kb))
				     (inference-level :taxonomic)
				     (kb-local-only-p nil))
  :returned-values (boolean exact-p)
  :manual-category :class
  :doc-string
  "Returns \\true\\ if \\karg{thing} is an instance of \\karg{class}, otherwise
   returns \\false."
  :standard-default-body
  (if (eq inference-level :direct)
      (multiple-value-bind (types exact-p)
	  (get-instance-types-internal thing kb :direct :all kb-local-only-p)
	(values (member-frame-list class types kb kb-local-only-p)
		exact-p))
      (multiple-value-bind (types exact-p)
	  (get-instance-types-internal
	   thing kb inference-level :all kb-local-only-p)
	(if (member-frame-list class types kb kb-local-only-p)
	    (values t exact-p)
	    (let ((inexact-p (not exact-p)))
	      (let ((found-p
		     (loop for type in types
			   thereis
			   (multiple-value-bind (found-p exact-p)
			       (subclass-of-p-internal
				type class kb inference-level kb-local-only-p)
			     (when (not exact-p) (setq inexact-p t))
			     (when found-p (return t))))))
		(if found-p
		    (values t t)
		    (values nil (not inexact-p))))))))
  :tell&ask-default-body
  (multiple-value-bind (res exact-p)
      (ask-internal `(:instance-of ,thing ,class)
		    kb t inference-level 1 t nil
		    (timeout-for-tell&ask-defaults kb) :known-true
		    kb-local-only-p)
    (values (first res) exact-p))
  :monitor-body
  (progn
    (record-reference class nil t nil kb)
    (record-reference thing nil t nil kb)))

(defokbcop okbc:kb-p (thing)
  :returned-values boolean
  :manual-category :kb
  :doc-string
  "Returns \\true\\ if \\karg{thing} is a KB, otherwise returns \\false."
  :default-body ((declare (ignore thing)) nil))

(defmethod kb-p-internal ((thing kb)) t)
(defmethod kb-p-internal ((thing structure-kb)) t)

;; Note we have a special case for caching mixin for this op.
(defokbcop okbc:kb-modified-p (&key (kb (current-kb)))
  :returned-values boolean
  :manual-category :kb
  :doc-string
  "Returns \\true\\ if \\karg{kb} has been modified since it was last saved."
  :default-body (ok-back:kb-has-been-modified-p kb))

