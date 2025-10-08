(in-package :ok-kernel)

;;; Defines COMPLIANT-OKBC-IMPLEMENTATION-P, which is true of a compliant
;;; OKBC implementation.

(defun ok-utils:compliant-okbc-implementation-p
    (back-end-name &key (compliance-classes :all)  (force-p nil)
		   (mandatory nil) (specialization-cache nil))
  "This predicate is true of a particular implementation if it is known to be
   compliant at least up to the specified <code>compliance-classes</code>.<P>

   Returns three values:
   <OL>
   <LI>True if the back end is compliant, False otherwise.
   <LI>A sorted list if all of the names of the OKBC operations that have yet
       to be specialized in order for this back end to be compliant to the
       compliance classes specified.
   <LI>The number of missing methods.
   </OL>

   <DL>
   <DT><code>Back-end-name</code><DD>is the name of an OKBC back end, such as
   <code>ok-back:tuple-kb</code>.
   <DT><code>Compliance-classes</code><DD>can be either <code>:all</code> (the
   default), or a list of keywords from <code>
   ok-back:*all-known-okbc-compliance-classes*</code>.
   <DT><code>Force-p</code><DD>forces the recomputation of compliance.
   Compliance checking is expensive and is normally cached because the
   compliance of a back end doesn't change at run-time.  This option is useful
   during back end development.
   </DL>

   This function is particularly useful during the development of a new back
   end.  When developing a back end it is difficult to know <i>a priori</i>
   which operations must be implemented because the set of necessary operations
   will be a non-trivial function of the set of mixins selected.  A useful
   model for back end development is to select the desired set of mixins,
   define your KB class, and them immediately call
   <code>compliant-okbc-implementation-p</code> on that class.  This will
   then return to you the minimum list of operations to implement.
   Repeatedly calling this function during back end development will tell you
   how close you are getting to a compliant KB.<p>

   For example,<PRE>
   > (defclass my-kb (ok-back:okbc-side-effects-cause-error-mixin
                      ok-back:tell&ask-defaults-kb)
       ())
   #&lt;Standard-Class MY-KB&gt;

   > (ok-utils:compliant-okbc-implementation-p 'my-kb :force-p t)
   NIL
   (OKBC:ASKABLE OKBC:COERCE-TO-FRAME OKBC:CREATE-KB-LOCATOR
    OKBC:DECONTEXTUALIZE OKBC:EXPUNGE-KB OKBC:FIND-KB-LOCATOR
    OKBC:GET-BEHAVIOR-SUPPORTED-VALUES OKBC:GET-BEHAVIOR-VALUES
    OKBC:GET-FRAME-IN-KB OKBC:GET-FRAME-SENTENCES OKBC:GET-KB-BEHAVIORS
    OKBC:GET-KBS-OF-TYPE OKBC:OPEN-KB OKBC:OPENABLE-KBS
    OKBC:PUT-BEHAVIOR-VALUES OKBC:TELL OKBC:TELLABLE OKBC:UNTELL)
   18</PRE>"

  (loop for class in (list-if-not compliance-classes)
	do (assert (or (eq :all class)
		       (member class ok-back:*all-known-okbc-compliance-classes*
			       :key 'first-if-list))
		   ()
		   "~S is not a known compliance class.  Check ~
                    ok-back:*all-known-okbc-compliance-classes*"
		   class))
  (compliant-okbc-implementation-p-internal back-end-name compliance-classes
					   mandatory specialization-cache
					   force-p))


(defmethod compliant-okbc-implementation-p-internal
    ((back-end-name symbol) (compliance-classes t) (mandatory t)
     (specialization-cache t) (force-p t))
  (let ((class (find-implementation-class back-end-name)))
    (continuable-assert class () "Cannot find OKBC implementation called ~S"
			back-end-name)
    (compliant-okbc-implementation-p-internal
     class compliance-classes mandatory specialization-cache force-p)))


(defun find-implementation-class (back-end-name)
  (or (find-class back-end-name nil)
      (and (keywordp back-end-name)
	   (let ((sym (find-symbol (string back-end-name) 'okbc)))
	     (and sym (find-class sym nil))))
      (and (not (string-equal (string back-end-name) "-KB"
			      :start1 (- (length (string back-end-name))
					 (length "-KB"))))
	   (let ((sym (find-symbol
		       (concatenate 'string (string back-end-name) "-KB")
		       'okbc)))
	     (and sym (find-implementation-class sym))))))


(defun non-mandatory-okbcop-p
    (op-internal-function &optional
			  (kb-class (find-class 'ok-back:standard-defaults-kb)))
  (let ((methods (#-MCL clos:generic-function-methods
			#+MCL ccl:generic-function-methods
			op-internal-function)))
    ;; An OKBCOP -internal function is said to be non-mandatory if we can find
    ;; any primary method for it specialized on ALL of its kb-specialized
    ;; args that is specialized on okbc:kb or one of its superclasses
    ;; (perhaps t), and for which all of the other args are specialized
    ;; on T, i.e. are not EQL specialized for something like
    ;; (slot-type (eql :own)).
    (or (let ((op-name (internal-name-to-op-name
			(#-MCL generic-function-name
			       #+MCL ccl:function-name
			       op-internal-function))))
	  (not (kb-specializing-arguments op-name)))
	(loop for method in methods
	      for specializers = (#-MCL clos:method-specializers
					#+MCL ccl:method-specializers method)
	      for op-name = (internal-name-to-op-name
			     (#-MCL generic-function-name
				    #+MCL ccl:function-name
				    op-internal-function))
	      for qualifiers = (#-MCL clos::method-qualifiers
				      #+MCL method-qualifiers method)
	      thereis (multiple-value-bind (spec-arg-names spec-args)
			  (kb-specializing-arguments op-name)
			(declare (ignore spec-arg-names))
			(and (null qualifiers)
			     (loop for index in spec-args
				   for spec = (nth index specializers)
				   for cl = (typecase spec
					      (class spec)
					      (symbol (find-class spec nil))
					      (otherwise nil))
				   always (and cl
					       (or (eq cl kb-class)
						   (subtypep kb-class cl))))
			     (loop with t-class = (find-class t)
				   for spec in specializers
				   for index from 0
				   for cl = (typecase spec
					      (class spec)
					      (symbol (find-class spec nil))
					      (otherwise nil))
				   always (or (member index spec-args)
					      (eq cl t-class)))))))))


(defun all-optional-okbcops ()
  (loop for name in *all-okbcops*
	for internal-name = (intern-okbcop-name name)
	for function = (symbol-function internal-name)
	when (non-mandatory-okbcop-p function)
	collect function))

(defun all-mandatory-okbcops (kb-class compliance-classes)
  ;; We cache the result for each compliance class because this
  ;; result is always constant for any OKBC implementation
  ;; (if it isn't, the spec changed since we loaded things).
  (or (second (assoc compliance-classes
		     (get (class-name kb-class) :all-mandatory-okbcops)
		     :test #'equal))
      (let ((res (loop for name in *all-okbcops*
		       for internal-name = (intern-okbcop-name name)
		       for function = (symbol-function internal-name)
		       when (and (not (non-mandatory-okbcop-p
				       function kb-class))
				 (op-matches-compliance-classes-p
				  internal-name kb-class compliance-classes))
		       collect function)))
	(push (list compliance-classes res)
	      (get (class-name kb-class) :all-mandatory-okbcops))
	res)))

(defun op-matches-compliance-classes-p
    (internal-name kb-class desired-compliance-classes)
  (let ((classes-for-op (compliance-classes internal-name)))
    (loop for c in classes-for-op
	  ;; At least one compliance class on this op is in the set we're
	  ;; looking for.
	  thereis
	  (loop for spec in desired-compliance-classes
		;; just in case we're passed the whole list
		for desired-class = (first-if-list spec)
		for entry = (find desired-class
				  ok-back:*all-known-okbc-compliance-classes*
				  :key 'first-if-list)
		thereis
		(and (eq c desired-class)
		     (or (eq entry c)
			 (loop for (behavior value)
			       in (rest entry)
			       always
			       (equal value
				      (get-behavior-values-internal
				       behavior
				       (class-prototype-safe kb-class))))))))))

(defmethod standard-class-p ((thing standard-class)) t)
(defmethod standard-class-p ((thing t)) nil)
(defmethod structure-class-p ((thing structure-class)) t)
(defmethod structure-class-p ((thing t)) nil)

(defmethod specializes ((kb-class standard-class)
			(candidate-method-specializer structure-class)
			(specialization-cache t))
  nil)

(defmethod specializes ((kb-class structure-class)
			(candidate-method-specializer standard-class)
			(specialization-cache t))
  nil)

(defmethod specializes :around
  ((kb-class t) (candidate-method-specializer t) (specialization-cache t))
  (let ((key (cons kb-class candidate-method-specializer)))
    (multiple-value-bind (value found-p trie-node)
	(get-hybrid-trie-returning-node key specialization-cache)
      (if found-p
	  value
	  (let ((res (call-next-method)))
	    (set-hybrid-trie-value trie-node res)
	    res)))))

(defmethod specializes ((kb-class standard-class)
			candidate-method-specializer
			(specialization-cache t))
  (continuable-assert candidate-method-specializer)
  (let ((class (if (standard-class-p candidate-method-specializer)
		   candidate-method-specializer
		   (and (symbolp candidate-method-specializer)
			(find-class candidate-method-specializer nil)))))
    (and class
	 (let ((proto (class-prototype-safe candidate-method-specializer)))
	   (or (kb-p-internal proto)
	       (typep proto 'ok-back:okbc-kb-mixin)))
	 (or (eq kb-class candidate-method-specializer)
	     (subtypep kb-class candidate-method-specializer)))))

(defmethod specializes ((kb-class structure-class)
			candidate-method-specializer
			(specialization-cache t))
  (continuable-assert candidate-method-specializer)
  (let ((class (if (structure-class-p candidate-method-specializer)
		   candidate-method-specializer
		   (and (symbolp candidate-method-specializer)
			(find-class candidate-method-specializer nil)))))
    (and class
	 (kb-p-internal (class-prototype-safe candidate-method-specializer))
	 (or (eq kb-class candidate-method-specializer)
	     (subtypep kb-class candidate-method-specializer)))))

;; Returns three values:
;;   o A boolean that is T if any mandatory OKBC methods are not
;;     specialized for the back-end specified by Class.
;;   o A list of those mandatory methods that are not specialized
;;   o The length of the second value.

(defun op-not-specialized-p (function class op-not-specialized-p)
  (let ((methods (#-MCL clos:generic-function-methods
			#+MCL ccl:generic-function-methods function))
	(gf-name (#-MCL generic-function-name
			#+MCL ccl:function-name function)))
    (let ((op-name (internal-name-to-op-name gf-name)))
      (let ((arg-positions (multiple-value-bind (names pos)
			       (kb-specializing-arguments op-name)
			     (declare (ignore names))
			     pos)))
	(not (loop for position in arg-positions
		   thereis
		   (loop for method in methods
			 for specializers
			 = (#-MCL clos::method-specializers
				  #+MCL ccl:method-specializers
				  method)
			 for qualifiers
			 = (#-MCL clos::method-qualifiers
				  #+MCL ccl:method-qualifiers
				  method)
			 for specialises-p
			 = (and (not qualifiers)
				(specializes
				 class (nth position specializers)
				 op-not-specialized-p))
			 thereis specialises-p)))))))

(defmethod compliant-okbc-implementation-p-internal
    ((class #-MCL clos::class #+MCL ccl:class) (compliance-classes symbol)
     (mandatory t) (specialization-cache t) (force-p t))
  (compliant-okbc-implementation-p-internal class (list compliance-classes)
					   mandatory specialization-cache
					   force-p))

(defmethod compliant-okbc-implementation-p-internal
    ((class #-MCL clos::class #+MCL ccl:class) (compliance-classes (eql :all))
     (mandatory t) (specialization-cache t) (force-p t))
  (compliant-okbc-implementation-p-internal
   class ok-back:*all-known-okbc-compliance-classes* mandatory
   specialization-cache force-p))

(defmethod compliant-okbc-implementation-p-internal
 ((kb-class #-MCL clos::class #+MCL ccl:class) (compliance-classes t)
  (mandatory t) (outside-specialization-cache t) (force-p t))
 (let ((name (class-name kb-class)))
   (let ((known (if force-p :no (and name (get name :okbc-compliant-p :no)))))
     (if (and known outside-specialization-cache (not (eq :no known)))
	 (values-list known)
	 (let ((mandatory
		(or mandatory
		    (all-mandatory-okbcops kb-class compliance-classes)))
	       (specialization-cache
		(or outside-specialization-cache
		    (new-root-trie :specialization nil))))
	   (let ((not-specialized
		  (loop for function in mandatory
			for not-spec-p =
			(op-not-specialized-p function kb-class
					      specialization-cache)
			when not-spec-p
			collect (ok-utils:internal-name-to-op-name
				 (generic-function-name function)))))
	     (when (and name (or (not not-specialized)
				 outside-specialization-cache))
	       (setf (get name :okbc-compliant-p)
		     (list (not not-specialized)
			   not-specialized (length not-specialized))))
	     (values (not not-specialized)
		     (if force-p
			 (sort not-specialized #'string<)
			 not-specialized)
		     (length not-specialized))))))))

(defun all-compliant-okbc-implementations (&optional (compliance-classes :all)
						     (force-p nil))
  "Returns a list of all the of the installed OKBC back end implementations
   that are known to be compliant according to the specified
   <code>compliance-classes</code>.<P>

   <code>Compliance-classes</code> can be either <code>:all</code> (the
   default), or a list of keywords from <code>
   ok-back:*all-known-okbc-compliance-classes*</code>.

   This function is used in order to compute the value of get-kb-types - only
   fully compliant KBs are returned by get-kb-types."   
  (let ((all nil)
	(tested nil)
	(specialization-cache (new-root-trie :specialization nil)))
    (labels ((do-subclasses (class mandatory known-compliant-p)
	       (when (and (not (member class tested :test #'eq))
			  ;; There appears to be a bug in Franz's handling
			  ;; of forward reference classes such that there
			  ;; end up being multiple class objects for
			  ;; classes such as tuple-kb, meta-kb and clos-kb.
			  ;; The ones that are not the same thing as
			  ;; (find-class name) are apparently bogus.
			  #+EXCL (or (not (class-name class))
				     (eq class (find-class
						(class-name class)))))
		 (push class tested)
		 (let ((compliant-p (or known-compliant-p
					(compliant-okbc-implementation-p
					 class
					 :compliance-classes compliance-classes
					 :mandatory mandatory
					 :force-p force-p
					 :specialization-cache
					 specialization-cache))))
		   ;; When any given class is found to be compliant, all of
		   ;; its subclasses must also be compliant.
		   (when compliant-p (push class all))
		   (loop for sub in (class-direct-subclasses class)
			 do (do-subclasses sub mandatory compliant-p))))))
      (loop for class-name in '(kb structure-kb)
	    for class = (find-class class-name)
	    do (setq tested nil) ;; these class graphs are disjoint!
	       (do-subclasses class (all-mandatory-okbcops
				     class (list-if-not compliance-classes))
			      nil))
      all)))
