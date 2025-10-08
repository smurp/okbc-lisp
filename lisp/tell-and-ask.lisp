(in-package :ok-kernel)

(defvar *evaluable-predicate-alist* nil)

(defparameter ok-back:*kif-operator-symbols*
  '(:lambda :listof :cond :setofall :=>> :not :<<= :the :<= :kappa :or :and
    :setof :exists :if :=> :forall :<=> :union :holds quote := :/=)
  "A list of symbols known to OKBC's default tell&ask implementation that
   represent KIF operators according to the KIF grammar.")

(defparameter ok-back:*evaluable-predicate-symbols* '(:< :> :>= :=< := :/= :is)
  "A list of the names of evaluable predicate symbols known by the OKBC default
   tell&ask implementation.")

(defparameter ok-back:*kif-meta-extension-symbols* '(:pragma)
  "A list of the names of magic symbols that extend KIF.")

(defparameter ok-back:*okbc-class-relation-symbols*
  '(:frame :class :individual :facet :slot :primitive)
  "A list of symbols naming OKBC class relations that are part of the
   tell&ask language and the knowledge model.")
(defparameter ok-back:*okbc-relation-symbols*
  (append ok-back:*okbc-class-relation-symbols*
	  '(:template-facet-value :template-slot-value :template-facet-of
	    :facet-of :template-slot-of :slot-of :subclass-of :superclass-of
	    :instance-of :type-of :name :pretty-name :handle))
  "A list of the non-class relation symbols known to the OKBC default
   OKBC tell&ask implementation.")

(defparameter ok-back:*okbc-standard-class-names*
  '(;;; Standard names of Classes
    :thing :number :integer :string :symbol :list)
  "A list of all of the standard class names as specified in the OKBC knowledge
   model section 2.10.1.  Note that this does not include all of the classes
   that are really entailed by the knowledge model.  Other classes can also
   be found in <code>*okbc-class-relation-symbols*</code>.")
(defparameter ok-back:*okbc-standard-class-direct-superclass-alist*
  '((:thing)
    (:integer :number)
    (:list :individual)
    (:otherwise :thing))
  "An alist of the form <code>((class . superclasses)...)</code> that maps
   an OKBC knowledge model class onto its required superclasses.  This is
   used in bootstrapping the kernel OKBC ontology in some back ends.  The
   special key <code>:othersise</code> is used to find the superclasses for
   all classes not found in the alist.")
(defparameter ok-back:*okbc-standard-facet-names*
  '(;;; Standard names of Facets
    :value-type :inverse :cardinality :maximum-cardinality :minimum-cardinality
    :same-values :not-same-values :subset-of-values :numeric-minimum
    :numeric-maximum :some-values :collection-type :documentation-in-frame)
  "A list of all of the standard facet names defined in the OKBC knowledge
   model specification in section 2.10.2.")
(defparameter ok-back:*okbc-standard-slot-names*
  '(;;; Standard names of Slots
    :documentation :domain :slot-value-type :slot-inverse :slot-cardinality
    :slot-maximum-cardinality :slot-minimum-cardinality :slot-same-values
    :slot-not-same-values :slot-subset-of-values :slot-numeric-minimum
    :slot-numeric-maximum :slot-some-values :slot-collection-type)
  "A list of all of the standard slot names defined in the OKBC knowledge
   model specification in section 2.10.3.")

(defparameter ok-back:*okbc-standard-names*
  (append *okbc-class-relation-symbols* *okbc-standard-class-names*
	  *okbc-standard-slot-names* *okbc-standard-facet-names*
	  *kif-meta-extension-symbols*)
  "A list of all of the standard name symbols in the OKBC knowledge model and
   tell&ask language.")
  
(defun ok-utils:list-to-conjunction
    (expression &optional (conjunction-operator :and))
  "Given what may be a list of conjunts, turns the list into a single
   conjunction sentence with the specified operator."
  (if (and (consp expression) (consp (first expression)))
      (if (rest expression)
          `(,conjunction-operator ,@expression)
          (first expression))
      expression))

(defun ok-utils:conjunction-to-list
       (sentence &optional (conjunction-operator :and))
  "Given a sentence that may be a conjunction of sentences, returns a list of
   sentences."
  (assert (listp sentence))
  (cond ((null sentence) nil)
        ((eq (first sentence) conjunction-operator)
         (rest sentence))
        ((consp (first sentence))
         sentence)
        (t (list sentence))))

(defun ok-utils:dequote (thing &optional (error-p t))
  "Takes a quoted expression and removes the quote.  If the expression is not
   quoted and <code>error-p</code> is true, an error is signalled."
  (if (and (consp thing) (symbolp (first thing))
	   (string= (first thing) :quote))
      (second thing)
      (if thing
	  (if error-p
	      (continuable-error "~S is not a quoted expression." thing)
	      thing)
	  thing)))

(defun ok-utils:okbc-sentence-p (sentence)
  "This predicate is true of a KIF sentence if it expresses only a simple
   ground atomic formula in the OKBC frame language, such as
   <code>(age fred 42)</code>."
  (and (consp sentence)
       (atom (first sentence))
       (not (member (first sentence) *kif-operator-symbols*))
       (ground? sentence)
       (let ((required-length
	      (case (first sentence)
		((:template-facet-value) 5)
		((:template-slot-value :template-facet-of :facet-of) 4)
		((:template-slot-of :slot-of :subclass-of :superclass-of
				    :instance-of :type-of) 3)
		((:frame :individual :class :facet :slot :primitive) 2)
		(otherwise nil))))
	 (if required-length
	     (= (length sentence) required-length)
	     (<= (length sentence) 4)))))


(defmacro with-recursion-doing-iteration-if-possible
    ((function local-functon-name &rest args) &body body)
  `(flet ((,local-functon-name (thing)
	   (if thing
	       (let ((res nil)
		     (tail nil))
		 (loop for x = (pop thing)
		       for can = (,function x ,@args)
		       do (if res
			      (let ((new (list can)))
				(setf (rest tail) new)
				(setq tail new))
			      (progn (setq res (list can))
				     (setq tail res)))
		       when (not thing) return nil
		       when (not (consp thing))
		       do (setf (rest tail)
				(,function thing ,@args))
		       (return nil))
		 res)
	       nil)))
    ,@body))
    

(defun canonicalise-kif-ops-and-okbc-relations (thing)
  (with-recursion-doing-iteration-if-possible
      (canonicalise-kif-ops-and-okbc-relations doit)
    (typecase thing
      (cons (typecase (first thing)
	      (symbol
	       (let ((sym (first thing)))
		 (if (string-equal 'quote sym)
		     (list 'quote (second thing))
		     (let ((kif-or-okbc-entry
			    (or (find sym *kif-operator-symbols*
				      :test #'string=)
				(find sym *evaluable-predicate-symbols*
				      :test #'string=)
				(find sym *okbc-relation-symbols*
				      :test #'string=))))
		       (cons (or kif-or-okbc-entry sym)
			     (doit (rest thing)))))))
	      (otherwise (doit thing))))
      (otherwise thing))))

(defun sym-or-frame-handle-for-sym (okbc-entry sym kb)
  (multiple-value-bind (frame found-p)
    (coerce-to-frame-internal okbc-entry kb nil nil)
    (if found-p
	(get-frame-handle-internal frame kb nil)
	sym)))

(defun canon/coerce-syms (thing kb kb-local-only-p intern-okbc-frames-p)
  (with-recursion-doing-iteration-if-possible
      (canon/coerce-syms doit kb kb-local-only-p intern-okbc-frames-p)
    (typecase thing
      (cons (typecase (first thing)
	      (symbol
	       (let ((sym (first thing)))
		 (if (string-equal 'quote sym)
		     (list 'quote (second thing))
		     (let ((kif-entry
			    (or (find sym *kif-operator-symbols*
				      :test #'string=)
				(find sym *evaluable-predicate-symbols*
				      :test #'string=))))
		       (if kif-entry
			   (cons kif-entry (doit (rest thing)))
			   (let ((okbc-entry
				  (find sym *okbc-relation-symbols*
					:test #'string=)))
			     (if okbc-entry
				 (cons (if intern-okbc-frames-p
					   (sym-or-frame-handle-for-sym
					    okbc-entry sym kb)
					   okbc-entry)
				       (doit (rest thing)))
				 (cons sym (doit (rest thing))))))))))
	      (otherwise
	       (doit thing))))
      (symbol
       (let ((okbc-entry (find thing *okbc-standard-names* :test #'string=)))
	 (if okbc-entry
	     (if intern-okbc-frames-p
		 (sym-or-frame-handle-for-sym okbc-entry okbc-entry kb)
		 okbc-entry)
	     thing)))
      (otherwise thing))))

(defun canon/coerce-syms-for-tell (thing kb kb-local-only-p)
  (with-recursion-doing-iteration-if-possible
      (canon/coerce-syms-for-tell doit kb kb-local-only-p)
    (typecase thing
      (cons (typecase (first thing)
	      (symbol
	       (let ((sym (first thing)))
		 (if (string-equal 'quote sym)
		     (list 'quote (second thing))
		     (let ((kif-entry
			    (or (find sym *kif-operator-symbols*
				      :test #'string=)
				(find sym *evaluable-predicate-symbols*
				      :test #'string=))))
		       (if kif-entry
			   (cons kif-entry (doit (rest thing)))
			   (let ((okbc-entry
				  (find sym *okbc-relation-symbols*
					:test #'string=)))
			     (if okbc-entry
				 (cons okbc-entry (doit (rest thing)))
				 (cons sym (doit (rest thing))))))))))
	      (otherwise
	       (let ((new-car
		      (multiple-value-bind (frame found-p)
			(coerce-to-frame-internal
			 (first thing) kb nil kb-local-only-p)
			(if found-p
			    (let ((name (get-frame-name-internal
					 frame kb kb-local-only-p)))
			      (if (or (member name
					      ok-back:*okbc-standard-names*)
				      (member name
					      ok-back:*okbc-relation-symbols*))
				  name
				  (get-frame-handle-internal
				   frame kb kb-local-only-p)))
			    (first thing)))))
		 (cons new-car (doit (rest thing)))))))
      (symbol
       (let ((okbc-entry (find thing *okbc-standard-names* :test #'string=)))
	 (if okbc-entry
	     okbc-entry
	     thing)))
      (otherwise thing))))

(defmacro not-vars (arg form)
  `(if (variable? ,arg)
       ,arg
       ,form))

(defun coerce-sentence-to-kb-value (sentence kb kb-local-only-p)
  (typecase sentence
    (cons
     (cond ((or (member (first sentence) *kif-operator-symbols* :test #'eq)
		(member (first sentence) *evaluable-predicate-symbols*
			:test #'eq))
	    (cons (first sentence)
		  (loop for arg in (rest sentence)
			collect
			(coerce-sentence-to-kb-value arg kb kb-local-only-p))))
	   (t (cond ((member (first sentence)
			     '(:frame :individual :class :facet :slot))
		     (cons (first sentence)
			   (loop for arg in (rest sentence)
				 collect
				 (not-vars
				  arg
				  (coerce-to-kb-value-internal
				   arg (first sentence) kb nil nil t
				   :error-if-not-unique kb-local-only-p)))))
		    ((member (first sentence)
			     '(:primitive :subclass-of :superclass-of))
		     (cons (first sentence)
			   (loop for arg in (rest sentence)
				 collect
				 (not-vars
				  arg
				  (coerce-to-kb-value-internal
				   arg :class kb nil nil t
				   :error-if-not-unique kb-local-only-p)))))
		    ((member (first sentence) '(:instance-of))
		     (list (first sentence)
			   (not-vars
			    (second sentence)
			    (coerce-to-kb-value-internal
			     (second sentence) :frame kb nil nil t
			     :error-if-not-unique kb-local-only-p))
			   (not-vars
			    (third sentence)
			    (coerce-to-kb-value-internal
			     (third sentence) :class kb nil nil t
			     :error-if-not-unique kb-local-only-p))))
		    ((member (first sentence) '(:type-of))
		     (list (first sentence)
			   (not-vars
			    (second sentence)
			    (coerce-to-kb-value-internal
			     (second sentence) :class kb nil nil t
			     :error-if-not-unique kb-local-only-p))
			   (not-vars
			    (third sentence)
			    (coerce-to-kb-value-internal
			     (third sentence) :frame kb nil nil t
			     :error-if-not-unique kb-local-only-p))))
		    ((member (first sentence) '(:template-slot-of :slot-of))
		     (list (first sentence)
			   (not-vars
			    (second sentence)
			    (coerce-to-kb-value-internal
			     (second sentence) :slot kb nil nil t
			     :error-if-not-unique kb-local-only-p))
			   (not-vars
			    (third sentence)
			    (coerce-to-kb-value-internal
			     (third sentence)
			     (if (eq (first sentence) :template-slot-of)
				 :class
				 :frame)
			     kb nil nil t :error-if-not-unique
			     kb-local-only-p))))
		    ((member (first sentence) '(:name :pretty-name :handle))
		     (list (first sentence)
			   (not-vars
			    (second sentence)
			    (coerce-to-kb-value-internal
			     (second sentence) :frame kb nil nil t
			     :error-if-not-unique kb-local-only-p))
			   (not-vars
			    (third sentence)
			    (coerce-to-kb-value-internal
			     (third sentence) :value
			     kb nil nil t :error-if-not-unique
			     kb-local-only-p))))
		    ((member (first sentence) '(:template-facet-of :facet-of))
		     (list (first sentence)
			   (not-vars
			    (second sentence)
			    (coerce-to-kb-value-internal
			     (second sentence) :facet kb nil nil t
			     :error-if-not-unique kb-local-only-p))
			   (not-vars
			    (third sentence)
			    (coerce-to-kb-value-internal
			     (third sentence) :slot kb nil nil t
			     :error-if-not-unique kb-local-only-p))
			   (not-vars
			    (fourth sentence)
			    (coerce-to-kb-value-internal
			     (fourth sentence)
			     (if (eq (first sentence) :template-facet-of)
				 :class
				 :frame)
			     kb nil nil t :error-if-not-unique
			     kb-local-only-p))))
		    ((member (first sentence) '(:template-slot-value))
		     (list (first sentence)
			   (not-vars
			    (second sentence)
			    (coerce-to-kb-value-internal
			     (second sentence) :slot kb nil nil t
			     :error-if-not-unique kb-local-only-p))
			   (not-vars
			    (third sentence)
			    (coerce-to-kb-value-internal
			     (third sentence) :class kb nil nil t
			     :error-if-not-unique kb-local-only-p))
			   (not-vars
			    (fourth sentence)
			    (coerce-to-kb-value-internal
			     (fourth sentence) :value kb nil nil t
			     :error-if-not-unique kb-local-only-p))))
		    ((member (first sentence) '(:template-facet-value))
		     (list (first sentence)
			   (not-vars
			    (second sentence)
			    (coerce-to-kb-value-internal
			     (second sentence) :facet kb nil nil t
			     :error-if-not-unique kb-local-only-p))
			   (not-vars
			    (third sentence)
			    (coerce-to-kb-value-internal
			     (third sentence) :slot kb nil nil t
			     :error-if-not-unique kb-local-only-p))
			   (not-vars
			    (fourth sentence)
			    (coerce-to-kb-value-internal
			     (fourth sentence) :class kb nil nil t
			     :error-if-not-unique kb-local-only-p))
			   (not-vars
			    (fifth sentence)
			    (coerce-to-kb-value-internal
			     (fifth sentence) :value kb nil nil t
			     :error-if-not-unique kb-local-only-p))))
		    (t (case (length sentence)
			 (2 (list
			     (not-vars
			      (first sentence)
			      (coerce-to-kb-value-internal
			       (first sentence) :class kb nil nil t
			       :error-if-not-unique kb-local-only-p))
			     (not-vars
			      (second sentence)
			      (coerce-to-kb-value-internal
			       (second sentence) :frame kb nil nil t
			       :error-if-not-unique kb-local-only-p))))
			 (3 (list
			     (not-vars
			      (first sentence)
			      (coerce-to-kb-value-internal
			       (first sentence) :slot kb nil nil t
			       :error-if-not-unique kb-local-only-p))
			     (not-vars
			      (second sentence)
			      (coerce-to-kb-value-internal
			       (second sentence) :frame kb nil nil t
			       :error-if-not-unique kb-local-only-p))
			     (not-vars
			      (third sentence)
			      (coerce-to-kb-value-internal
			       (third sentence) :value kb nil nil t
			       :error-if-not-unique kb-local-only-p))))
			 (4 (list
			     (not-vars
			      (first sentence)
			      (coerce-to-kb-value-internal
			       (first sentence) :facet kb nil nil t
			       :error-if-not-unique kb-local-only-p))
			     (not-vars
			      (second sentence)
			      (coerce-to-kb-value-internal
			       (second sentence) :slot kb nil nil t
			       :error-if-not-unique kb-local-only-p))
			     (not-vars
			      (third sentence)
			      (coerce-to-kb-value-internal
			       (third sentence) :frame kb nil nil t
			       :error-if-not-unique kb-local-only-p))
			     (not-vars
			      (fourth sentence)
			      (coerce-to-kb-value-internal
			       (fourth sentence) :value kb nil nil t
			       :error-if-not-unique kb-local-only-p))))
			 (otherwise (coerce-to-kb-value-internal
				     sentence :value kb nil nil t
				     :error-if-not-unique
				     kb-local-only-p))))))))
    (otherwise (coerce-to-kb-value-internal
		sentence :value kb nil nil t :error-if-not-unique
		kb-local-only-p))))

(defun default-tell (sentence kb frame value-selector kb-local-only-p)
  (let ((canonicalised-without-keys
	 (canonicalise-kif-ops-and-okbc-relations sentence))
	(canonicalised-with-keys
	 (canon/coerce-syms-for-tell sentence kb kb-local-only-p)))
    (handle-sentence-handling-conjunctions
     canonicalised-without-keys canonicalised-with-keys kb frame
     value-selector kb-local-only-p :tell))
  nil)

(defun default-untell (sentence kb frame value-selector kb-local-only-p)
  (let ((canonicalised-without-keys
	 (canonicalise-kif-ops-and-okbc-relations sentence))
	(canonicalised-with-keys
	 (canon/coerce-syms-for-tell sentence kb kb-local-only-p)))
    (handle-sentence-handling-conjunctions
     canonicalised-without-keys canonicalised-with-keys kb frame
     value-selector kb-local-only-p :untell)))

(defvar *frames-created-by-this-sentence*)

(defun default-tellable (sentence kb value-selector kb-local-only-p)
  (let ((canonicalised-without-keys
	 (canonicalise-kif-ops-and-okbc-relations sentence))
	(canonicalised-with-keys
	 (canon/coerce-syms-for-tell sentence kb kb-local-only-p))
	(*frames-created-by-this-sentence* nil))
    (handle-sentence-handling-conjunctions
     canonicalised-without-keys canonicalised-with-keys kb nil
     value-selector kb-local-only-p :tellable)))

(defvar *remaining-conjuncts*)
(defvar *remaining-conjuncts-with-keys*)

(defun handle-sentence-handling-conjunctions
    (sentence sentence-with-keys kb frame value-selector kb-local-only-p key)
  (typecase sentence
    (cons
     (case (first sentence)
       (:and
	(ecase key
	  (:tellable
	   (let ((*remaining-conjuncts* (rest sentence))
		 (*remaining-conjuncts-with-keys* (rest sentence-with-keys)))
	     (loop until (not *remaining-conjuncts*)
		   when (not (handle-sentence-handling-conjunctions
			      (pop *remaining-conjuncts*)
			      (pop *remaining-conjuncts-with-keys*) kb frame
			      value-selector kb-local-only-p key))
		   return nil
		   finally (return t))))
	  (:untell
	   (let ((*remaining-conjuncts* (rest sentence))
		 (*remaining-conjuncts-with-keys* (rest sentence-with-keys))
		 (removed-p t))
	     (loop until (not *remaining-conjuncts*)
		   do (let ((res (handle-sentence-handling-conjunctions
				  (pop *remaining-conjuncts*)
				  (pop *remaining-conjuncts-with-keys*)
				  kb frame value-selector kb-local-only-p
				  key)))
			(when (not res) (setq removed-p nil))))
	     removed-p))
	  (:tell
	   (let ((*remaining-conjuncts* (rest sentence))
		 (*remaining-conjuncts-with-keys* (rest sentence-with-keys)))
	     (loop until (not *remaining-conjuncts*)
		   do (handle-sentence-handling-conjunctions
		       (pop *remaining-conjuncts*)
		       (pop *remaining-conjuncts-with-keys*) kb frame
		       value-selector kb-local-only-p key))
	     t))))
       (otherwise
	(if (ground? sentence)
	    (handle-ground-sentence sentence sentence-with-keys kb frame
				    value-selector kb-local-only-p key)
	    (handle-unhandled-sentence sentence kb frame value-selector
				       kb-local-only-p key)))))
    (otherwise t))) ;;; drop it on the floor, it's just an atom.


(defmacro handle-tell-schema (pattern sentence &key tell untell (tellable t))
  (let ((tell (if (and (consp tell) (consp (first tell)))
		  tell
		  (list tell)))
	(untell (if (and (consp untell) (consp (first untell)))
		    untell
		    (list untell))))
    `(macrolet ((binding-for (var) `(rest (assoc ',var .schema-result.))))
      (let ((.schema-result. (unify-against-literal ',pattern ,sentence)))
	(if (or (eq :fail .schema-result.)
		(member (first ,sentence)
			*kif-operator-symbols* :test #'eq))
	    nil
	    (ecase key
	      (:tell
	       ,@(sublis (loop for v in (variables-in tell)
			       collect (cons v (list 'binding-for v)))
			 tell)
	       t)
	      (:untell
	       ,@(sublis (loop for v in (variables-in untell)
			       collect (cons v (list 'binding-for v)))
			 untell)
	       t)
	      (:tellable
	       ,(sublis (loop for v in (variables-in tellable)
			      collect (cons v (list 'binding-for v)))
			tellable))))))))

(defmacro handle-tell-schema-test (pattern sentence test &key tell untell
					   (tellable t))
  (let ((tell (if (and (consp tell) (consp (first tell)))
		       tell
		       (list tell)))
	(untell (if (and (consp untell) (consp (first untell)))
			 untell
			 (list untell))))
    `(macrolet ((binding-for (var) `(rest (assoc ',var .schema-result.))))
      (let ((.schema-result. (unify-against-literal ',pattern ,sentence)))
	(if (or (eq :fail .schema-result.)
		(member (first ,sentence)
			*kif-operator-symbols* :test #'eq)
		(not ,(sublis (loop for v in (variables-in tell)
				    collect (cons v (list 'binding-for v)))
			      test)))
	    nil
	    (ecase key
	      (:tell
	       ,@(sublis (loop for v in (variables-in tell)
			       collect (cons v (list 'binding-for v)))
			 tell)
	       t)
	      (:untell
	       ,@(sublis (loop for v in (variables-in untell)
			       collect (cons v (list 'binding-for v)))
			 untell))
	      (:tellable
	       ,(sublis (loop for v in (variables-in tellable)
			      collect (cons v (list 'binding-for v)))
			tellable))))))))

(defmacro handle-tell-schemata ((&rest patterns) sentence &key tell untell)
  (let ((tell (if (and (consp tell) (consp (first tell)))
		  tell
		  (list tell)))
	(untell (if (and (consp untell) (consp (first untell)))
		    untell
		    (list untell))))
    `(macrolet ((binding-for (var) `(rest (assoc ',var .schema-result.))))
      (let ((.schema-result. :no-unify))
	,@(loop for p in patterns
		collect `(when (eq .schema-result. :no-unify)
			  (let ((.unify-result.
				 (unify-against-literal ',p
							,sentence)))
			    (when (not (eq .unify-result. :fail))
			      (setq .schema-result. .unify-result.)))))
	(if (or (eq .schema-result. :fail)
		(eq .schema-result. :no-unify)
		(member (first ,sentence) *kif-operator-symbols*
			:test #'eq))
	    nil
	    (ecase key
	      (:tell
	       ,@(sublis (loop for v in (variables-in tell)
			       collect (cons v (list 'binding-for v)))
			 tell)
	       t)
	      (:untell
	       ,@(sublis (loop for v in (variables-in untell)
			       collect (cons v (list 'binding-for v)))
			 untell))
	      (:tellable t)))))))

(defun substitute-new-instance (name new-value kb)
  (multiple-value-bind (frame found-p)
    (coerce-to-frame-internal new-value kb nil nil)
    (let ((handle (if found-p
		      (get-frame-handle-internal frame kb nil)
		      new-value)))
      (when (boundp '*remaining-conjuncts*)
	(setq *remaining-conjuncts*
	      (subst-handling-quote name handle *remaining-conjuncts*)))
      (when (boundp '*remaining-conjuncts-with-keys*)
	(setq *remaining-conjuncts-with-keys*
	      (subst-handling-quote name handle
				    *remaining-conjuncts-with-keys*))))))

(eval-when (compile load eval)
  (defun subst-handling-quote (name new-value form)
    (if (equal name form)
	new-value
	(typecase form
	  (cons (if (and (symbolp (first form))
			 (string-equal 'quote (first form)))
		    form
		    #+ignore;; the old way.
		    (cons (subst-handling-quote name new-value (first form))
			  (subst-handling-quote name new-value (rest form)))
		    ;; rewritten by JPR on 1-Oct-98 to prevent stack overflow
		    ;; in HCL.
		    (let ((res nil)
			  (tail nil))
		      (loop for arg = (pop form)
			    for substituted = (subst-handling-quote
					       name new-value arg)
			    do (cond (res
				      (setf (rest tail) (list substituted))
				      (setq tail (rest tail)))
				     (t (setq res (list substituted))
					(setq tail res)))
			    when (not form) return nil
			    when (not (consp form))
			    do (progn (setf (rest tail)
					    (subst-handling-quote
					     name new-value form))
				      (return nil)))
		      res)))
	  (otherwise form))))

  #+Harlequin-Common-Lisp
  (when (not (compiled-function-p #'subst-handling-quote))
    (compile 'subst-handling-quote))

  (defun sublis-handling-quote (alist form)
    "Just like <code>sublis</code> only substitutions are not performed inside
     KIF quotation terms embedded within <code>form</code>."
    (if alist
	(sublis-handling-quote (rest alist)
			       (subst-handling-quote (first (first alist))
						     (rest  (first alist))
						     form))
	form)))

(defun handle-subclass-or-instance-sentence
    (sentence sentence-with-keys kb frame value-selector kb-local-only-p key)
  (declare (ignore frame))
  ;;; Subclass/Instance link asserting sentences -------------------------
  (ecase value-selector
    (:known-true
     (or (handle-tell-schema
	  (:subclass-of ?sub ?super)
	  sentence-with-keys
	  :tell (add-class-superclass-internal ?sub ?super kb kb-local-only-p)
	  :untell (remove-class-superclass-internal
		   ?sub ?super kb kb-local-only-p))
	 (handle-tell-schema
	  (:superclass-of ?super ?sub)
	  sentence-with-keys
	  :tell (add-class-superclass-internal ?sub ?super kb kb-local-only-p)
	  :untell (remove-class-superclass-internal
		   ?sub ?super kb kb-local-only-p))
	 (handle-tell-schema
	  (:type-of ?class ?frame)
	  sentence-with-keys
	  :tell (add-instance-type-internal ?frame ?class kb kb-local-only-p)
	  :untell (remove-instance-type-internal
		   ?frame ?class kb kb-local-only-p))
	 (handle-tell-schema
	  (:instance-of ?frame ?class)
	  sentence-with-keys
	  :tell (add-instance-type-internal ?frame ?class kb kb-local-only-p)
	  :tellable (progn (pushnew ?frame
				    *frames-created-by-this-sentence*)
			   t)
	  :untell (remove-instance-type-internal
		   ?frame ?class kb kb-local-only-p))))
    (:default-only
	(ecase key
	  (:tellable nil)
	  ((:untell :tell)
	   (error 'cannot-handle :sentence sentence))))))

(defun handle-creation-sentence
    (sentence sentence-with-keys kb frame value-selector kb-local-only-p key)
  (declare (ignore frame value-selector sentence))
  ;;; Creation sentences -------------------------------------------------
  (or (handle-tell-schema
       (:frame ?frame)
       sentence-with-keys
       :tell (or (coercible-to-frame-p-internal ?frame kb kb-local-only-p)
		 (substitute-new-instance
		  ?frame
		  (if (typep ?frame '(or symbol number string))
		      (create-frame-internal ?frame :individual kb nil nil nil
					     nil nil nil nil t nil nil
					     kb-local-only-p)
		      (create-frame-internal nil :individual kb nil nil nil
					     nil nil nil nil t ?frame nil
					     kb-local-only-p))
		  kb))
       :tellable (progn (pushnew ?frame *frames-created-by-this-sentence*) t)
       :untell (multiple-value-bind (frame found-p)
		   (coerce-to-frame-internal
		    ?frame kb nil kb-local-only-p)
		 (when found-p
		   (delete-frame-internal frame kb kb-local-only-p))))
      (handle-tell-schema
       (:class ?class)
       sentence-with-keys
       :tell (or (class-p-internal ?class kb kb-local-only-p)
		 (substitute-new-instance
		  ?class
		  (if (typep ?class '(or symbol number string))
		      (create-class-internal ?class kb nil nil t nil nil nil
					     nil nil nil nil kb-local-only-p)
		      (create-class-internal nil kb nil nil t nil nil nil
					     nil nil ?class nil
					     kb-local-only-p))
		  kb))
       :tellable (progn (pushnew ?class *frames-created-by-this-sentence*) t)
       :untell (multiple-value-bind (frame found-p)
		   (coerce-to-frame-internal
		    ?class kb nil kb-local-only-p)
		 (when found-p
		   (delete-frame-internal frame kb kb-local-only-p))))
      (handle-tell-schema
       (:slot ?slot)
       sentence-with-keys
       :tell (or (slot-p-internal ?slot kb kb-local-only-p)
		 (substitute-new-instance
		  ?slot
		  (if (typep ?slot '(or symbol number string))
		      (create-slot-internal ?slot kb nil
					    :own nil nil
					    nil nil nil
					    nil kb-local-only-p)
		      (create-slot-internal nil kb nil
					    :own nil nil
					    nil nil ?slot
					    nil kb-local-only-p))
		  kb))
       :tellable (progn (pushnew ?slot *frames-created-by-this-sentence*) t)
       :untell (when (slot-p-internal ?slot kb kb-local-only-p)
		 (delete-slot-internal ?slot kb kb-local-only-p)))
      (handle-tell-schema
       (:facet ?facet)
       sentence-with-keys
       :tell (or (facet-p-internal ?facet kb kb-local-only-p)
		 (substitute-new-instance
		  ?facet
		  (if (typep ?facet '(or symbol number string))
		      (create-facet-internal ?facet kb nil nil
					     :own nil nil
					     nil nil nil
					     nil kb-local-only-p)
		      (create-facet-internal nil kb nil nil
					     :own nil nil
					     nil nil ?facet
					     nil kb-local-only-p))
		  kb))
       :tellable (progn (pushnew ?facet *frames-created-by-this-sentence*) t)
       :untell (when (facet-p-internal ?facet kb kb-local-only-p)
		 (delete-facet-internal ?facet kb kb-local-only-p)))
      (handle-tell-schema
       (:individual ?individual)
       sentence-with-keys
       :tell (or (and (coercible-to-frame-p-internal
		       ?individual kb kb-local-only-p)
		      (individual-p-internal ?individual kb kb-local-only-p))
		 (substitute-new-instance
		  ?individual
		  (if (typep ?individual '(or symbol number string))
		      (create-individual-internal ?individual kb nil
						  nil nil nil
						  nil nil kb-local-only-p)
		      (create-individual-internal nil kb nil
						  nil nil nil
						  ?individual nil
						  kb-local-only-p))
		  kb))
       :tellable
       (progn (pushnew ?individual *frames-created-by-this-sentence*) t)
       :untell (multiple-value-bind (frame found-p)
		   (coerce-to-frame-internal
		    ?individual kb nil kb-local-only-p)
		 (when found-p
		   (delete-frame-internal frame kb kb-local-only-p))))
      (handle-tell-schema-test
       (?class ?frame)
       ;; This is a little dangerous, since we don't know what sort of
       ;; thing to create.  Assume it's an individual
       sentence-with-keys
       (and (atom ?frame) (atom ?class))
       :tell (or (coercible-to-frame-p-internal ?frame kb kb-local-only-p)
		 (substitute-new-instance
		  ?frame
		  (tell-and-ask-create-frame-of-specified-class
		   ?frame ?class kb kb-local-only-p)
		  kb))
       :tellable (progn (pushnew ?frame *frames-created-by-this-sentence*) t)
       :untell (multiple-value-bind (frame found-p)
		 (coerce-to-frame-internal
		  ?frame kb nil kb-local-only-p)
		 (when found-p
		   (remove-instance-type-internal frame ?class kb
						  kb-local-only-p))))))

(defmethod tell-and-ask-create-frame-of-specified-class
 (?frame ?class kb kb-local-only-p)
 (if (typep ?frame '(or symbol number string))
     (create-frame-internal ?frame :individual kb
			    (list ?class) nil nil
			    nil nil nil nil t nil nil
			    kb-local-only-p)
     (create-frame-internal nil :individual kb
			    (list ?class) nil nil
			    nil nil nil nil t ?frame nil
			    kb-local-only-p)))

(defun handle-template-slot-sentence
    (sentence sentence-with-keys kb frame value-selector kb-local-only-p key)
  (declare (ignore frame sentence))
  ;;; Slot and facet asserting sentences ---------------------------------
      ;;; Template slots and facets
  (or (handle-tell-schema
       (:template-facet-of ?facet ?slot ?class)
       sentence-with-keys
       :tell (attach-facet-internal ?class ?slot ?facet kb :template
				    kb-local-only-p)
       :untell (detach-facet-internal ?class ?slot ?facet kb :template
				      kb-local-only-p))
      (handle-tell-schema
       (:template-slot-of ?slot ?class)
       sentence-with-keys
       :tell (attach-slot-internal ?class ?slot kb :template kb-local-only-p)
       :untell (detach-slot-internal ?class ?slot kb :template
				     kb-local-only-p))
      (handle-tell-schema
       (:template-facet-value ?facet ?slot ?class ?value)
       sentence-with-keys
       :tell (add-facet-value-internal ?class ?slot ?facet ?value kb :equal
				       :template value-selector
				       kb-local-only-p)
       :untell (if (variable? ?value)
		   (remove-local-facet-values-internal
		    ?class ?slot ?facet kb :template value-selector
		    kb-local-only-p)
		   (remove-facet-value-internal
		    ?class ?slot ?facet ?value kb :equal
		    :template value-selector kb-local-only-p)))
      (handle-tell-schema
       (:template-slot-value ?slot ?class ?value)
       sentence-with-keys
       :tell (add-slot-value-internal ?class ?slot ?value kb :equal
				      :template 0 value-selector
				      kb-local-only-p)
       :untell (if (variable? ?value)
		   (remove-local-slot-values-internal
		    ?class ?slot kb :template value-selector kb-local-only-p)
		   (remove-slot-value-internal ?class ?slot ?value kb :equal
					       :template :all value-selector
					       kb-local-only-p)))))

(defun handle-own-slot-sentence
    (sentence sentence-with-keys kb frame value-selector kb-local-only-p key)
  (declare (ignore frame))
  ;;; Slot and facet asserting sentences ---------------------------------
      ;;; Own slots and facets
  (or (handle-tell-schema-test
       (:name ?frame ?value)
       sentence-with-keys
       (coercible-to-frame-p-internal ?frame kb kb-local-only-p)
       :tell (put-frame-name-internal ?frame ?value kb kb-local-only-p)
       :untell (if (member nil (get-behavior-values-internal
				:frame-names-required kb))
		   (put-frame-name-internal ?frame nil kb kb-local-only-p)
		   (error 'cannot-handle :sentence sentence)))
      (handle-tell-schema
       (:pretty-name ?frame ?value)
       sentence-with-keys
       :tell (put-frame-pretty-name-internal ?frame ?value kb kb-local-only-p)
       :untell (error 'cannot-handle :sentence sentence))
      (handle-tell-schema
       (:facet-of ?facet ?slot ?class)
       sentence-with-keys
       :tell (attach-facet-internal ?class ?slot ?facet kb :own
				    kb-local-only-p)
       :untell (detach-facet-internal ?class ?slot ?facet kb :own
				      kb-local-only-p))
      (handle-tell-schema
       (:slot-of ?slot ?class)
       sentence-with-keys
       :tell (attach-slot-internal ?class ?slot kb :own kb-local-only-p)
       :untell (detach-slot-internal ?class ?slot kb :own kb-local-only-p))
      (handle-tell-schema-test
       (:holds ?facet ?slot ?frame ?value)
       sentence-with-keys
       (coercible-to-frame-p-internal ?frame kb kb-local-only-p)
       :tell (add-facet-value-internal ?frame ?slot ?facet ?value kb :equal
				       :own value-selector kb-local-only-p)
       :untell (if (variable? ?value)
		   (remove-local-facet-values-internal
		    ?class ?slot ?facet kb :own value-selector
		    kb-local-only-p)
		   (remove-facet-value-internal ?frame ?slot ?facet ?value kb
						:equal :own value-selector
						kb-local-only-p)))
      (handle-tell-schema-test
       (:holds ?slot ?frame ?value)
       sentence-with-keys
       (coercible-to-frame-p-internal ?frame kb kb-local-only-p)
       :tell (add-slot-value-internal ?frame ?slot ?value kb :equal
				      :own 0 value-selector kb-local-only-p)
       :untell (if (variable? ?value)
		   (remove-local-slot-values-internal
		    ?class ?slot kb :own value-selector
		    kb-local-only-p)
		   (remove-slot-value-internal ?frame ?slot ?value kb
					       :equal :own :all value-selector
					       kb-local-only-p)))
      (handle-tell-schema-test
       (?slot ?frame ?value)
       sentence
       (coercible-to-frame-p-internal ?frame kb kb-local-only-p)
       :tell (add-slot-value-internal ?frame ?slot ?value kb :equal
				      :own 0 value-selector kb-local-only-p)
       :untell (if (variable? ?value)
		   (remove-local-slot-values-internal
		    ?class ?slot kb :own value-selector
		    kb-local-only-p)
		   (remove-slot-value-internal ?frame ?slot ?value kb
					       :equal :own :all value-selector
					       kb-local-only-p)))
      (handle-tell-schema-test
       (?facet ?slot ?frame ?value)
       sentence
       (coercible-to-frame-p-internal ?frame kb kb-local-only-p)
       :tell (add-facet-value-internal ?frame ?slot ?facet ?value kb :equal
				       :own value-selector kb-local-only-p)
       :untell (if (variable? ?value)
		   (remove-local-facet-values-internal
		    ?class ?slot ?facet kb :own value-selector
		    kb-local-only-p)
		   (remove-facet-value-internal ?frame ?slot ?facet ?value kb
						:equal :own value-selector
						kb-local-only-p)))))

(defun handle-ground-sentence
    (sentence sentence-with-keys kb frame value-selector kb-local-only-p key)
  (or (handle-subclass-or-instance-sentence
       sentence sentence-with-keys kb frame value-selector kb-local-only-p key)
      (handle-creation-sentence
       sentence sentence-with-keys kb frame value-selector kb-local-only-p key)
      (handle-template-slot-sentence
       sentence sentence-with-keys kb frame value-selector kb-local-only-p key)
      (handle-own-slot-sentence
       sentence sentence-with-keys kb frame value-selector kb-local-only-p key)
      (handle-unhandled-sentence
       sentence kb frame value-selector kb-local-only-p key)))

(defokbcgeneric handle-unhandled-sentence
    (sentence kb frame value-selector kb-local-only-p key)
  (:documentation "A trapdoor in the default implementation of OKBC's tell&ask
   handler.  This generic function is called when a sentence that is
   being told to is doesn't match any of the axiom schemata that OKBC
   understands.  Implementations that know how to store arbitrary sentences
   should specialize this method to handle leftover sentences.  The
   <code>sentence</code> being told is being told with respect to
   <code>frame</code> as for the <code>tell</code> operation.  <code>Key</code>
   is a keyword indicating the reason why this generic function was called.
   It will be one of <code>:tell</code> or <code>:tellable</code>."))

(defmethod handle-unhandled-sentence
    (sentence (kb t) (frame t) (value-selector t) (kb-local-only-p t) (key t))
  (ecase key
    (:tell (error 'cannot-handle :sentence sentence))
    (:tellable nil)))

;------------------------------------------------------------------------------

;;; Now define Ask.

(defun quasi-symbol-vars-to-symbols (query)
  ;; We may get a query from a network client in which the variables are
  ;; quasi-symbols.  We'd like to keep all variables as being symbolp,
  ;; so we do an up-front substitution and then switch the variables
  ;; back at the end.
  (let ((alist nil)
	(ralist nil))
    (labels ((rec (x)
	       (if (consp x)
		   (cons (rec (first x)) (rec (rest x)))
		   (if (quasi-symbol-p x)
		       (or (first (rassoc x alist))
			   (let ((new-var
				  (make-symbol
				   (concatenate 'string
						(quasi-symbol-name x)
						(name (quasi-symbol-package
						       x))))))
			     (push (cons new-var x) alist)
			     (push (cons x new-var) ralist)
			     new-var))
		       x))))
      (values (rec query) alist ralist))))

(defun default-ask (query reply-pattern kb inference-level number-of-values
			  error-p where timeout value-selector
			  kb-local-only-p)
  (let ((dotted-where
	 (loop for (var val) in where collect (cons var val)))
	(quasi-var-alist nil)
	(reverse-quasi-var-alist nil))
    (multiple-value-bind (canonicalised canonical-for-default-tell&ask)
      (if (member nil (get-behavior-values-internal
		       :frame-names-required kb))
	  (values (canon/coerce-syms
		   (sublis dotted-where query) kb kb-local-only-p t)
		  (canon/coerce-syms
		   (sublis dotted-where query) kb kb-local-only-p nil))
	  (let ((x (coerce-to-kb-value-internal
		    (canonicalise-kif-ops-and-okbc-relations
		     (sublis dotted-where query))
		    :value kb nil nil t :error-if-not-unique kb-local-only-p)))
	    (values x x)))
      (let ((*all-binding-lists* nil)
	    (number-of-values (if (eq number-of-values :all)
				  most-positive-fixnum
				  number-of-values)))
	(declare (special *all-binding-lists*))
	(multiple-value-setq (canonical-for-default-tell&ask quasi-var-alist)
	  (quasi-symbol-vars-to-symbols canonical-for-default-tell&ask))
	(when reverse-quasi-var-alist
	  (setq canonicalised (sublis reverse-quasi-var-alist canonicalised)))
	(multiple-value-bind (result exact-p more-status)
	  (catch :timeout
	    (if timeout
		(with-timeout
		    (timeout (throw :timeout (values :timeout nil :timeout)))
		  (handle-ask-handling-conjunctions
		   canonical-for-default-tell&ask canonicalised kb
		   inference-level number-of-values error-p
		   value-selector kb-local-only-p))
		(handle-ask-handling-conjunctions
		 canonical-for-default-tell&ask canonicalised kb
		 inference-level number-of-values error-p
		 value-selector kb-local-only-p)))
	  (values (loop for b in *all-binding-lists*
			collect (if quasi-var-alist
				    (sublis (sublis quasi-var-alist b)
					    reply-pattern)
				    (sublis b reply-pattern)))
		  exact-p
		  (if (eq result :timeout) :timeout more-status)))))))

(defun default-askable (sentence kb value-selector kb-local-only-p)
  (default-tellable sentence kb value-selector kb-local-only-p))

(defun handle-ask-handling-conjunctions
    (canonicalised canonical-target kb inference-level number-of-values
		   error-p value-selector kb-local-only-p)
  (declare (special *all-binding-lists*))
  (flet ((doit-the-hard-way ()
	   (multiple-value-bind (binding-lists exact-p)
	       (handle-ask-handling-conjunctions-internal
		canonicalised canonical-target kb inference-level error-p
		value-selector kb-local-only-p nil)
	     (if (eq binding-lists :fail)
		 (values nil exact-p nil)
		 (loop for blist in binding-lists
		       for rest on binding-lists
		       for count from 0 below number-of-values
		       do (push blist *all-binding-lists*)
		       finally (return (values nil exact-p
					       (if rest
						   (length (rest rest))
						   nil))))))))
    (if (numberp number-of-values)
	(multiple-value-bind (binding-lists exact-p)
	    (handler-case
	     (handle-unhandled-query canonicalised canonical-target kb
				     inference-level error-p value-selector
				     kb-local-only-p nil)
	     (cannot-handle (condition)
			    (declare (ignore condition))
			    (values nil t)))
	  (if (and (consp binding-lists)
		   (>= (length binding-lists) number-of-values))
	      (loop for blist in binding-lists
		    for rest on binding-lists
		    for count from 0 below number-of-values
		    do (push blist *all-binding-lists*)
		    finally (return (values nil exact-p
					    (if rest
						(length (rest rest))
					      nil))))
	      (doit-the-hard-way)))
	(doit-the-hard-way))))
	      

(defmethod handle-ask-conjunction
    (args target-args (kb t) inference-level error-p value-selector
	  kb-local-only-p bindings)
  (if args
      (let ((inexact-p nil))
	(multiple-value-bind
	      (result exact-p)
	    (handle-ask-handling-conjunctions-internal
	     (first args) (first target-args) kb inference-level
	     error-p value-selector kb-local-only-p
	     bindings)
	  (when (not exact-p) (setq inexact-p t))
	  (if (not (eq :fail result))
	      (if (rest args)
		  (let ((results (loop with exact-p = nil
				       with result-from-tail = nil
				       for blist in result
				       do (multiple-value-setq
					      (result-from-tail exact-p)
					    (handle-ask-conjunction
					     (rest args) (rest target-args)
					     kb inference-level
					     error-p value-selector
					     kb-local-only-p blist))
				       when (not exact-p) do (setq inexact-p t)
				       when (not (eq :fail result-from-tail))
				       append result-from-tail)))
		    (if results
			(values results (not inexact-p))
			(values :fail (not inexact-p))))
		  (values result (not inexact-p)))
	      (values :fail (not inexact-p)))))
      (values (list bindings) t)))

(defun handle-ask-handling-conjunctions-internal
    (query target-query kb inference-level error-p value-selector
	   kb-local-only-p bindings)
  (typecase query
    (cons
     (case (first query)
       (:and (handle-ask-conjunction
	      (rest query) (rest target-query) kb inference-level error-p
	      value-selector kb-local-only-p bindings))
       (otherwise
	(handle-simple-query (sublis bindings query)
			     (sublis bindings target-query)
			     kb inference-level error-p value-selector
			     kb-local-only-p bindings))))
    (otherwise (values bindings t))))

(defmacro handle-ask-schema (pattern &body body)
  `(macrolet ((binding-for (var) `(rest (assoc ',var .ask-result.))))
    (let ((.ask-result. (unify-against-literal ,pattern query)))
      (if (or (eq :fail .ask-result.)
	      (and (variable? (first ,pattern))
		   (member (first query) *kif-operator-symbols* :test #'eq)))
	  (values :fail t t)
	  (progn ,@(sublis-handling-quote
		    (loop for v in (variables-in body)
			  collect (cons v (list 'binding-for v)))
		    body))))))

(defmacro handle-target-ask-schema (pattern &body body)
  `(let ((query target-query))
    (handle-ask-schema ,pattern ,@body)))

(defmacro handle-ask-schemata (patterns &body body)
  `(macrolet ((binding-for (var) `(rest (assoc ',var .ask-result.))))
    (let ((.ask-result. :no-unify))
      ,@(loop for p in patterns
	      collect `(when (eq .ask-result. :no-unify)
			(let ((.unify-result.
			       (unify-against-literal ,p query)))
			  (when (not (or (eq .unify-result. :fail)
					 (and (variable? (first query))
					      (member (first .unify-result.)
						      *kif-operator-symbols*
						      :test #'eq))))
			    (setq .ask-result. .unify-result.)))))
      (if (eq :no-unify .ask-result.)
	  (values :fail t t)
	  (multiple-value-bind (.clause-result. .exact-p.)
	      (progn ,@(sublis-handling-quote
			(loop for v in (variables-in body)
			      collect (cons v (list 'binding-for v)))
			body))
	    (values .clause-result. .exact-p. nil))))))

(defmacro handle-target-ask-schemata (patterns &body body)
  `(let ((query target-query))
    (handle-ask-schemata ,patterns ,@body)))

(defmacro augment-bindings (var list &optional (bindings 'bindings))
  `(loop for .value. in ,list
         collect (cons (cons ,var .value.) ,bindings)))

(defun handle-kernel-type-query (query target-query kb kb-local-only-p bindings
				       type-key list-getter predicate)
  (declare (ignore target-query)) 
  (handle-ask-schema
   `(,type-key ?c)
   (if (variable? ?c)
       (let ((classes (funcall list-getter kb :all kb-local-only-p)))
	 (values (if classes
		     (augment-bindings ?c classes)
		     :fail)
		 t))
       (if (funcall predicate ?c kb kb-local-only-p)
	   (values (list bindings) t)
	   (values :fail t)))))
  
(defmacro or-fail (&body body)
  (if body
      `(multiple-value-bind (result exact-p unify-failed-p) ,(first body)
	 (if unify-failed-p
	     (or-fail ,@(rest body))
	     (values result exact-p nil)))
      `(values :fail t t)))

(defun handle-frame-type-query (query target-query kb inference-level error-p
				      value-selector kb-local-only-p
				      bindings)
  (declare (ignore inference-level error-p value-selector))
  (or-fail
   (handle-ask-schema
    `(:frame ?f)
    (if (variable? ?f)
	(let ((frames (get-kb-frames-internal kb kb-local-only-p)))
	  (values (if frames
		      (augment-bindings ?f frames)
		      :fail)
		  t))
	(if (coercible-to-frame-p-internal ?f kb kb-local-only-p)
	    (values (list bindings) t)
	    (values :fail t))))
   (handle-kernel-type-query query target-query kb kb-local-only-p bindings
			     :class 'get-kb-classes-internal 'class-p-internal)
   (handle-kernel-type-query query target-query kb kb-local-only-p bindings
			     :slot 'get-kb-slots-internal 'slot-p-internal)
   (handle-kernel-type-query query target-query kb kb-local-only-p bindings
			     :facet 'get-kb-facets-internal 'facet-p-internal)
   (handle-kernel-type-query query target-query kb kb-local-only-p bindings
			     :individual 'get-kb-individuals-internal
			     'individual-p-internal)))

(defun handle-slot-of-attachment-query (query target-query kb inference-level
					      error-p value-selector
					      kb-local-only-p bindings
					      slot-of-key slot-type)
  (declare (ignore error-p value-selector target-query))
  (handle-ask-schema
   `(,slot-of-key ?slot ?frame)
   (if (variable? ?frame)
       (let ((frames (get-kb-frames-internal kb kb-local-only-p)))
	 (if frames
	     (if (variable? ?slot)
		 (values
		  (or (loop for frame in frames
			    for slots = (get-frame-slots-internal
					 frame kb inference-level slot-type
					 kb-local-only-p)
			    when slots
			    append (loop for slot in slots
					  collect
					  (cons (cons ?slot slot)
						(cons (cons ?frame frame)
						      bindings))))
		      :fail)
		  t)
		 (let ((matches
			(loop for frame in frames
			      for found-p = (frame-has-slot-p-internal
					     frame ?slot kb inference-level
					     slot-type kb-local-only-p)
			      when found-p
			      collect frame)))
		   (values (if matches
			       (augment-bindings ?frame matches)
			       :fail)
			   t)))
	     (values :fail t)))
       (if (variable? ?slot)
	   (let ((matches (get-frame-slots-internal
			   ?frame kb inference-level slot-type
			   kb-local-only-p)))
	     (values (if matches
			 (augment-bindings ?slot matches)
			 :fail)
		     t))
	   (if (frame-has-slot-p-internal ?frame ?slot kb inference-level
					  slot-type kb-local-only-p)
	       (values (list bindings) t)
	       (values :fail t))))))

(defun handle-facet-of-attachment-query
    (query target-query kb inference-level error-p value-selector
	   kb-local-only-p bindings facet-of-key slot-type)
  (declare (ignore error-p value-selector))
  (if (variable? (first query))
      (values :fail t t)
  (handle-target-ask-schema
   `(,facet-of-key ?facet ?slot ?frame)
   (if (variable? ?frame)
       ;; We don't know the frame
       (if (variable? ?slot)
	   (if (variable? ?facet)
	       (let ((triples nil))
		 (loop for frame in (get-kb-frames-internal kb kb-local-only-p)
		       do (loop for slot in (get-frame-slots-internal
					     frame kb inference-level slot-type
					     kb-local-only-p)
				do (loop for facet
					 in (get-slot-facets-internal
					     frame slot kb inference-level
					     slot-type kb-local-only-p)
					 do (push (list facet slot frame)
						  triples))))
		 (values (if triples
			     (loop for (facet slot frame) in triples
				   collect (append (list (cons ?facet facet)
							 (cons ?slot slot)
							 (cons ?frame frame))
						   bindings))
			     :fail)
			 t))
	       (let ((pairs nil))
		 (loop for frame in (get-kb-frames-internal kb kb-local-only-p)
		       do (loop for slot in (get-frame-slots-internal
					     frame kb inference-level slot-type
					     kb-local-only-p)
				when (slot-has-facet-p-internal
				      frame slot ?facet kb inference-level
				      slot-type kb-local-only-p)
				do (push (list slot frame) pairs)))
		 (values (if pairs
			     (loop for (slot frame) in pairs
				   collect (append (list (cons ?slot slot)
							 (cons ?frame frame))
						   bindings))
			     :fail)
			 t)))
	   ;; We don't know frame, but have slot.
	   (if (variable? ?facet)
	       (let ((pairs nil))
		 (loop for frame in (get-kb-frames-internal kb kb-local-only-p)
		       do (loop for facet
				in (get-slot-facets-internal
				    frame ?slot kb inference-level
				    slot-type kb-local-only-p)
				do (push (list facet frame) pairs)))
		 (values (if pairs
			     (loop for (facet frame) in pairs
				   collect (append (list (cons ?facet facet)
							 (cons ?frame frame))
						   bindings))
			     :fail)
			 t))
	       ;; We don't know frame, but have slot and facet.
	       (let ((frames nil))
		 (loop for frame in (get-kb-frames-internal kb kb-local-only-p)
		       when (slot-has-facet-p-internal
			     frame ?slot ?facet kb inference-level
			     slot-type kb-local-only-p)
		       do (push frame frames))
		 (values (if frames
			     (loop for frame in frames
				   collect (cons (cons ?frame frame) bindings))
			     :fail)
			 t))))
       ;;; We know the frame
       (if (variable? ?slot)
	   (if (variable? ?facet)
	       (let ((pairs nil))
		 (loop for slot in (get-frame-slots-internal
				    ?frame kb inference-level slot-type
				    kb-local-only-p)
		       do (loop for facet in
				(get-slot-facets-internal
				 ?frame slot kb inference-level slot-type
				 kb-local-only-p)
				do (push (list facet slot) pairs)))
		 (values (if pairs
			     (loop for (facet slot) in pairs
				   collect (append (list (cons ?facet facet)
							 (cons ?slot slot))
						   bindings))
			     :fail)
			 t))
	       ;; we know frame and facet, but not slot.
	       (let ((slots
		      (loop for slot in (get-frame-slots-internal
					 ?frame kb inference-level slot-type
					 kb-local-only-p)
			    when (slot-has-facet-p-internal
				  ?frame slot ?facet kb inference-level
				  slot-type kb-local-only-p)
			    collect slot)))
		 (values (if slots
			     (loop for slot in slots
				   collect (cons (cons ?slot slot)
						 bindings))
			     :fail)
			 t)))
	   ;; frame and slot are fixed.
	   (if (variable? ?facet)
	       (values
		(let ((matches (get-slot-facets-internal
				?frame ?slot kb inference-level slot-type
				kb-local-only-p)))
		  (if matches
		      (augment-bindings ?facet matches)
		      :fail))
		t)
	       ;; frame, slot and facet are fixed.
	       (if (slot-has-facet-p-internal
		    ?frame ?slot ?facet kb inference-level
		    slot-type kb-local-only-p)
		   (list bindings)
		   (values :fail t))))))))

(defun handle-slot-value-query (query target-query kb inference-level error-p
				      value-selector kb-local-only-p
				      bindings slot-type)
  (declare (ignore error-p query))
  (handle-target-ask-schemata
   ((ecase slot-type
      (:own `(?slot ?frame ?value))
      (:template (if (variable? (first query))
		     nil
		     `(:template-slot-value ?slot ?frame ?value))))
    (ecase slot-type
      (:own `(:holds ?slot ?frame ?value))
      (:template nil)))
   (if (variable? ?frame)
       (if (variable? ?slot)
	   (let ((frames (get-kb-frames-internal kb kb-local-only-p)))
	     (if frames
		 (if (variable? ?value)
		     (values
		      (let ((triples nil))
			(loop for frame in frames
			      for slots = (get-frame-slots-internal
					   frame kb inference-level slot-type
					   kb-local-only-p)
			      do (loop for slot in slots
				       for values = (get-slot-values-internal
						     frame slot kb
						     inference-level
						     slot-type :all
						     value-selector
						     kb-local-only-p)
				       do (loop for value in values
						do (push (list slot frame
							       value)
							 triples))))
			(values
			 (if triples
			     (loop for (slot frame value) in triples
				   collect (append (list (cons ?slot slot)
							 (cons ?frame frame)
							 (cons ?value value))
						   bindings))
			     :fail)
			 t)))
		     (values
		      (let ((pairs nil))
			(loop for frame in frames
			      for slots = (get-frame-slots-internal
					   frame kb inference-level slot-type
					   kb-local-only-p)
			      do (loop for slot in slots
				       when (member-slot-value-p-internal
					     frame slot ?value kb
					     inference-level :equal
					     slot-type value-selector
					     kb-local-only-p)
				       do (push (list slot frame) pairs)))
			(values
			 (if pairs
			     (loop for (slot frame) in pairs
				   collect (append (list (cons ?slot slot)
							 (cons ?frame frame))
						   bindings))
			     :fail)
			 t))))
		 (values :fail t)))
	   ;;; Frame is unknown, but slot is known
	   (if (variable? ?value)
	       (let ((frames (get-kb-frames-internal kb kb-local-only-p)))
		 (if frames
		     (values
		      (let ((pairs nil))
			(loop for frame in frames
			      for values = (get-slot-values-internal
					    frame ?slot kb inference-level
					    slot-type :all value-selector
					    kb-local-only-p)
			      do (loop for value in values
				       do (push (list frame value) pairs)))
			(values
			 (if pairs
			     (loop for (frame value) in pairs
				   collect (append (list (cons ?frame frame)
							 (cons ?value value))
						   bindings))
			     :fail)
			 t)))
		     (values :fail t)))
	       ;;; frame isn't known, but slot and value are:
	       (let ((matches (get-frames-with-slot-value-internal
			       ?slot ?value kb inference-level slot-type
			       value-selector kb-local-only-p)))
		 (values (if matches
			     (augment-bindings ?frame matches)
			     :fail)
			 t))))       
       ;;; Frame is known
       (if (variable? ?slot)
	   (if (variable? ?value)
	       (values
		(let ((pairs nil))
		  (loop for slot in (get-frame-slots-internal
				     ?frame kb inference-level slot-type
				     kb-local-only-p)
			do (loop for value in (get-slot-values-internal
					       ?frame slot kb
					       inference-level
					       slot-type :all
					       value-selector
					       kb-local-only-p)
				 do (push (list slot value) pairs)))
		  (values
		   (if pairs
		       (loop for (slot value) in pairs
			     collect (append (list (cons ?slot slot)
						   (cons ?value value))
					     bindings))
		       :fail)
		   t)))
	       ;;; frame and value are known
	       (values
		(let ((matches
		       (loop for slot in (get-frame-slots-internal
					  ?frame kb inference-level slot-type
					  kb-local-only-p)
			     when (member-slot-value-p-internal
				   ?frame slot ?value kb inference-level
				   :equal slot-type value-selector
				   kb-local-only-p)
			     collect slot)))
		  (values
		   (if matches
		       (augment-bindings ?slot matches)
		       :fail)
		   t))))
	   ;;; frame and slot are known
	   (if (variable? ?value)
	       (values
		(let ((matches (get-slot-values-internal
				?frame ?slot kb inference-level slot-type :all
				value-selector kb-local-only-p)))
		  (if matches
		      (augment-bindings ?value matches)
		      :fail))
		t)
	       ;;; frame, slot and value are known
	       (values (if (member-slot-value-p-internal
			    ?frame ?slot ?value kb inference-level
			    :equal slot-type value-selector
			    kb-local-only-p)
			   (list bindings)
			   :fail)
		       t))))))

(defun handle-facet-value-query (query target-query kb inference-level error-p
				       value-selector kb-local-only-p
				       bindings slot-type)
  (declare (ignore error-p target-query))
  (handle-ask-schemata
   ((ecase slot-type
      (:own `(?facet ?slot ?frame ?value))
      (:template `(:template-facet-value ?facet ?slot ?frame ?value)))
    (ecase slot-type
      (:own `(:holds ?facet ?slot ?frame ?value))
      (:template nil)))
   (if (variable? ?frame)
       (if (variable? ?slot)
	   (if (variable? ?facet)
	       ;; None of frame, slot or facet are known
	       (let ((frames (get-kb-frames-internal kb kb-local-only-p)))
		 (if frames
		     (if (variable? ?value)
			 (let ((quadruples nil))
			   (loop for frame in frames
				 for slots = (get-frame-slots-internal
					      frame kb inference-level
					      slot-type kb-local-only-p)
				 do (loop for slot in slots
					  for facets =
					  (get-slot-facets-internal
					   frame slot kb inference-level
					   slot-type kb-local-only-p)
					  do (loop for facet in facets
						   for values =
						   (get-facet-values-internal
						    frame slot facet kb
						    inference-level
						    slot-type :all
						    value-selector
						    kb-local-only-p)
						   do (loop
						       for value in values
						       do (push
							   (list facet slot
								 frame value)
							   quadruples)))))
			   (values
			    (if quadruples
				(loop for (facet slot frame value)
				      in quadruples
				      collect
				      (append (list (cons ?facet facet)
						    (cons ?slot slot)
						    (cons ?frame frame)
						    (cons ?value value))
					      bindings))
				:fail)
			    t))
			 (let ((triples nil))
			   (loop for frame in frames
				 for slots = (get-frame-slots-internal
					      frame kb inference-level
					      slot-type kb-local-only-p)
				 do (loop for slot in slots
					  for facets =
					  (get-slot-facets-internal
					   frame slot kb inference-level
					   slot-type kb-local-only-p)
					  do (loop
					      for facet in facets
					      when
					      (member-facet-value-p-internal
					       frame slot facet ?value kb
					       inference-level :equal
					       slot-type value-selector
					       kb-local-only-p)
					      do (push (list facet slot
							     frame)
						       triples))))
			   (values
			    (if triples
				(loop for (facet slot frame) in triples
				      collect
				      (append (list (cons ?facet facet)
						    (cons ?slot slot)
						    (cons ?frame frame))
					      bindings))
				:fail)
			    t)))
		     (values :fail t)))
	       ;; neither frame nor slot are known, but facet is
	       (let ((frames (get-kb-frames-internal kb kb-local-only-p)))
		 (if frames
		     (if (variable? ?value)
			 (let ((triples nil))
			   (loop for frame in frames
				 for slots = (get-frame-slots-internal
					      frame kb inference-level
					      slot-type kb-local-only-p)
				 do (loop for slot in slots
					  for values =
					  (get-facet-values-internal
					   frame slot ?facet kb
					   inference-level slot-type :all
					   value-selector kb-local-only-p)
					  do (loop for value in values
						   do (push
						       (list slot frame value)
						       triples))))
			   (values
			    (if triples
				(loop for (slot frame value) in triples
				      collect
				      (append (list (cons ?slot slot)
						    (cons ?frame frame)
						    (cons ?value value))
					      bindings))
				:fail)
			    t))
			 ;; frame and slot aren't known, but facet and
			 ;; value are
			 (let ((pairs nil))
			   (loop for frame in frames
				 for slots = (get-frame-slots-internal
					      frame kb inference-level
					      slot-type kb-local-only-p)
				 do (loop for slot in slots
					  when
					  (member-facet-value-p-internal
					   frame slot ?facet ?value kb
					   inference-level :equal slot-type
					   value-selector kb-local-only-p)
					  do (push (list slot frame) pairs)))
			   (values
			    (if pairs
				(loop for (slot frame) in pairs
				      collect
				      (append (list (cons ?slot slot)
						    (cons ?frame frame))
					      bindings))
				:fail)
			    t)))
		     (values :fail t))))
	   ;;; frame isn't known, but slot is
	   (if (variable? ?facet)
	       ;; frame and facet are not known
	       (let ((frames (get-kb-frames-internal kb kb-local-only-p)))
		 (if frames
		     (if (variable? ?value)
			 (let ((triples nil))
			   (loop for frame in frames
				 for facets =
				 (get-slot-facets-internal
				  frame ?slot kb inference-level
				  slot-type kb-local-only-p)
				 do (loop for facet in facets
					  for values =
					  (get-facet-values-internal
					   frame ?slot facet kb inference-level
					   slot-type :all value-selector
					   kb-local-only-p)
					  do (loop for value in values
						   do (push
						       (list facet frame value)
						       triples))))
			   (values
			    (if triples
				(loop for (facet frame value) in triples
				      collect
				      (append (list (cons ?facet facet)
						    (cons ?frame frame)
						    (cons ?value value))
					      bindings))
				:fail)
			    t))
			 ;;; frame and facet are unknown, but slot and value
			 ;;; are.
			 (let ((pairs nil))
			   (loop for frame in frames
				 for facets = (get-slot-facets-internal
					       frame ?slot kb inference-level
					       slot-type kb-local-only-p)
				 do (loop for facet in facets
					  when
					  (member-facet-value-p-internal
					   frame ?slot facet ?value kb
					   inference-level :equal
					   slot-type value-selector
					   kb-local-only-p)
					  do (push (list facet frame) pairs)))
			   (values
			    (if pairs
				(loop for (facet frame) in pairs
				      collect
				      (append (list (cons ?facet facet)
						    (cons ?frame frame))
					      bindings))
				:fail)
			    t)))
		     (values :fail t)))
	       ;; frame is not known, but slot and facet are
	       (if (variable? ?value)
		   (let ((frames (get-kb-frames-internal kb kb-local-only-p)))
		     (if frames
			 (let ((pairs nil))
			   (loop for frame in frames
				 for values =
				 (get-facet-values-internal
				  frame ?slot ?facet kb
				  inference-level slot-type :all
				  value-selector kb-local-only-p)
				 do (loop for value in values
					  do (push (list frame value) pairs)))
			   (values
			    (if pairs
				(loop for (frame value) in pairs
				      collect
				      (append (list (cons ?frame frame)
						    (cons ?value value))
					      bindings))
				:fail)
			    t))
			 (values :fail t)))
		   ;;; frame isn't known, but slot, facet and value are.
		   (let ((matches (get-frames-with-facet-value-internal
				   ?slot ?facet ?value kb inference-level
				   slot-type value-selector kb-local-only-p)))
		     (values (if matches
				 (augment-bindings ?frame matches)
				 :fail)
			     t)))))
       ;;; Frame is known
       (if (variable? ?slot)
	   (if (variable? ?facet)
	       ;; Frame is known, but, slot and facet are not
	       (if (variable? ?value)
		   (let ((triples nil))
		     (loop for slot in (get-frame-slots-internal
					?frame kb inference-level
					slot-type kb-local-only-p)
			   for facets =
			   (get-slot-facets-internal
			    ?frame slot kb inference-level
			    slot-type kb-local-only-p)
			   do (loop for facet in facets
				    for values =
				    (get-facet-values-internal
				     ?frame slot facet kb inference-level
				     slot-type :all value-selector
				     kb-local-only-p)
				    do (loop for value in values
					     do (push (list facet slot value)
						      triples))))
		     (values
		      (if triples
			  (loop for (facet slot value) in triples
				collect
				(append (list (cons ?facet facet)
					      (cons ?slot slot)
					      (cons ?value value))
					bindings))
			  :fail)
		      t))
		   ;; frame and value are know, but slot and facet aren't
		   (let ((pairs nil))
		     (loop for slot in (get-frame-slots-internal
					?frame kb inference-level
					slot-type kb-local-only-p)
			   for facets =
			   (get-slot-facets-internal
			    ?frame slot kb inference-level
			    slot-type kb-local-only-p)
			   do (loop for facet in facets
				    when (member-facet-value-p-internal
					  ?frame slot facet ?value kb
					  inference-level :equal
					  slot-type value-selector
					  kb-local-only-p)
				    do (push (list facet slot) pairs)))
		     (values
		      (if pairs
			  (loop for (facet slot) in pairs
				collect (append (list (cons ?facet facet)
						      (cons ?slot slot))
						bindings))
			  :fail)
		      t)))
	       ;; Frame and facet are known, but slot isn't
	       (if (variable? ?value)
		   (let ((pairs nil))
		     (loop for slot in (get-frame-slots-internal
					?frame kb inference-level
					slot-type kb-local-only-p)
			   for values =
			   (get-facet-values-internal
			    ?frame slot ?facet kb inference-level
			    slot-type :all value-selector
			    kb-local-only-p)
			   do (loop for value in values
				    do (push (list slot value) pairs)))
		     (values
		      (if pairs
			  (loop for (slot value) in pairs
				collect
				(append (list (cons ?slot slot)
					      (cons ?value value))
					bindings))
			  :fail)
		      t))
		   ;; frame, facet and value are know, but slot isnt
		   (let ((slots nil))
		     (loop for slot in (get-frame-slots-internal
					?frame kb inference-level
					slot-type kb-local-only-p)
			   when (member-facet-value-p-internal
				 ?frame slot ?facet ?value kb
				 inference-level :equal
				 slot-type value-selector
				 kb-local-only-p)
			   do (push slot slots))
		     (values
		      (if slots
			  (loop for slot in slots
				collect (append (list (cons ?slot slot))
						bindings))
			  :fail)
		      t))))
	   ;;; Frame and slot are known
	   (if (variable? ?facet)
	       ;; Frame and slot are known, but facet isn't
	       (if (variable? ?value)
		   (let ((pairs nil))
		     (loop for facet in
			   (get-slot-facets-internal
			    ?frame ?slot kb inference-level
			    slot-type kb-local-only-p)
			   do (loop for value in
				    (get-facet-values-internal
				     ?frame ?slot facet kb inference-level
				     slot-type :all value-selector
				     kb-local-only-p)
				    do (push (list facet value)
					     pairs)))
		     (values
		      (if pairs
			  (loop for (facet value) in pairs
				collect
				(append (list (cons ?facet facet)
					      (cons ?value value))
					bindings))
			  :fail)
		      t))
		   ;; frame, slot and value are know, facet isn't
		   (let ((facets nil))
		     (loop for facet in
			   (get-slot-facets-internal
			    ?frame ?slot kb inference-level
			    slot-type kb-local-only-p)
			   when (member-facet-value-p-internal
				 ?frame ?slot facet ?value kb
				 inference-level :equal slot-type
				 value-selector kb-local-only-p)
			   do (push facet facets))
		     (values
		      (if facets
			  (loop for facet in facets
				collect (append (list (cons ?facet facet))
						bindings))
			  :fail)
		      t)))
	       ;;; frame, slot and facet are known
	       (if (variable? ?value)
		   (let ((values (get-facet-values-internal
				  ?frame ?slot ?facet kb inference-level
				  slot-type :all value-selector
				  kb-local-only-p)))
		     (values
		      (if values
			  (loop for value in values
				collect
				(append (list (cons ?value value))
					bindings))
			  :fail)
		      t))
		   ;; frame, slot, facet and value are know.
		   (values
		    (if (member-facet-value-p-internal
			 ?frame ?slot ?facet ?value kb
			 inference-level :equal slot-type value-selector
			 kb-local-only-p)
			(list bindings)
			:fail)
		    t)))))))


(defun handle-instance/type-query (query target-query kb inference-level
					 error-p value-selector kb-local-only-p
					 bindings)
  (declare (ignore error-p value-selector target-query))
  (if (variable? (first query))
      (values :fail t t)
  (handle-ask-schemata
   (`(:instance-of ?instance ?class)
     `(:type-of ?class ?instance)
     `(?class ?instance))
   (if (variable? ?class)
       (if (variable? ?instance)
	   (let ((classes (get-kb-classes-internal
			   kb :all kb-local-only-p)))
	     (if classes
		 (let ((pairs nil))
		   (loop for class in classes
			 for instances = (get-class-instances-internal
					  class kb inference-level :all
					  kb-local-only-p)
			 do (loop for instance in instances
				  do (push (list class instance)
					   pairs)))
		   (values (if pairs
			       (loop for (class instance) in pairs
				     collect (append
					      (list (cons ?class class)
						    (cons ?instance instance))
					      bindings))
			       :fail)
			   t))
		 (values :fail t)))
	   ;; frame is known, but class 
	   (let ((matches (get-instance-types-internal
			   ?instance kb inference-level :all
			   kb-local-only-p)))
	     (if matches
		 (augment-bindings ?class matches)
		 (values :fail t))))
	   ;;; the class is known
       (if (variable? ?instance)
	   (let ((matches (get-class-instances-internal
			   ?class kb inference-level :all
			   kb-local-only-p)))
	     (if matches
		 (augment-bindings ?instance matches)
		 (values :fail t)))
	   ;; both frame and class are known
	   (if (instance-of-p-internal ?instance ?class kb inference-level
				       kb-local-only-p)
	       (list bindings)
	       (values :fail t)))))))

(defun handle-subclass-query (query target-query kb inference-level error-p
				    value-selector kb-local-only-p bindings)
  (declare (ignore error-p value-selector target-query))
  (if (variable? (first query))
      (values :fail t t)
  (handle-ask-schemata
   (`(:subclass-of ?subclass ?superclass)
     `(:superclass-of ?superclass ?subclass))
   (if (variable? ?superclass)
       (if (variable? ?subclass)
	   (let ((classes (get-kb-classes-internal
			   kb :all kb-local-only-p)))
	     (let ((pairs nil))
	       (loop for superclass in classes
		     for subclasses = (get-class-subclasses-internal
				       superclass kb inference-level :all
				       kb-local-only-p)
		     do (loop for subclass in subclasses
			      do (push (list superclass subclass)
				       pairs)))
	       (values (if pairs
			   (loop for (superclass subclass) in pairs
				 collect (append
					  (list (cons ?superclass superclass)
						(cons ?subclass     subclass))
					  bindings))
			   :fail)
		       t)))
	   (let ((matches (get-class-superclasses-internal
			   ?subclass kb inference-level :all
			   kb-local-only-p)))
	     (if matches
		 (augment-bindings ?superclass matches)
		 (values :fail t))))
	   ;;; the superclass is known
       (if (variable? ?subclass)
	   (let ((matches (get-class-subclasses-internal
			   ?superclass kb inference-level :all
			   kb-local-only-p)))
	     (if matches
		 (augment-bindings ?subclass matches)
		 (values :fail t)))
	   ;; both sub and superclass are known
	   (if (subclass-of-p-internal ?subclass ?superclass kb
				       inference-level kb-local-only-p)
	       (list bindings)
	       (values :fail t)))))))

(defun handle-primitivity-query (query target-query kb inference-level error-p
				       value-selector kb-local-only-p bindings)
  (declare (ignore inference-level error-p value-selector target-query))
  (if (variable? (first query))
      (values :fail t t)
      (handle-ask-schema
       `(:primitive ?x)
       (if (variable? ?x)
	   (let ((matches (loop for class in (get-kb-classes-internal
					      kb :all kb-local-only-p)
				when (primitive-p-internal
				      class kb kb-local-only-p)
				collect class)))
	     (values (if matches
			 (augment-bindings ?x matches)
			 :fail)
		     t))
	   (values (if (primitive-p-internal ?x kb kb-local-only-p)
		       (list bindings)
		       :fail)
		   t)))))

(defun handle-pragma-sentence
    (query target-query kb inference-level error-p value-selector
	   kb-local-only-p bindings)
  (if (and (rest query) (eq (first query) :pragma))
      (destructuring-bind (?target-sentence . @target-plist) (rest target-query)
	(declare (ignore @target-plist))
	(destructuring-bind (?sentence . @plist) (rest query)
	  (if (variable? ?sentence)
	      (continuable-error
	       "The first (sentence) argument to a :PRAGMA construct ~
              cannot be a variable: ~S" ?sentence)
	      (handle-pragma-sentence-dispatch
	       (first @plist) @plist ?sentence ?target-sentence query
	       target-query kb inference-level error-p
	       value-selector kb-local-only-p bindings))))
      (values :fail t t)))

(defmethod handle-pragma-sentence-dispatch
 ((key t) (pragmata (eql nil))
  sentence target-sentence (query t) (target-query t) kb
  inference-level error-p value-selector kb-local-only-p bindings)
 (handle-ask-handling-conjunctions-internal
  sentence target-sentence kb inference-level error-p value-selector
  kb-local-only-p bindings))

(defmethod handle-pragma-sentence-dispatch
 ((key (eql :inference-level)) pragmata
  sentence target-sentence (query t)
  (target-query t) kb inference-level error-p value-selector kb-local-only-p
  bindings)
 (pop pragmata)
 (let ((new-i/l (pop pragmata)))
   (continuable-assert
    (ecase new-i/l
      (:all-inferable (eq inference-level :all-inferable))
      (:taxonomic (member inference-level '(:all-inferable :taxonomic)))
      (:direct (member inference-level '(:all-inferable :taxonomic :direct))))
    nil "You cannot upgrade the inference level using a PRAGMA construct from ~
         ~S to ~S" inference-level new-i/l)
   (handle-pragma-sentence-dispatch
    (first pragmata) pragmata sentence target-sentence query target-query kb
    new-i/l error-p value-selector kb-local-only-p bindings)))

;; Def macro for evaluable predicates.  Can be defined as a symbol
;; naming a function, or a lambda expression.
(defmacro defevaluable-predicate (predicate as-function)
  "A def macro for evaluable predicates.  This allows you to define your
   own predicates to be used in a tell and ask query."
  (let ((keyname (intern (symbol-name predicate) :keyword)))
  `(progn (pushnew (list ',keyname ,as-function) *evaluable-predicate-alist*)
          (pushnew ',keyname ok-back:*evaluable-predicate-symbols*)
          ',predicate)))

(defun handle-evaluable-predicate-query
    (query target-query kb inference-level error-p value-selector
	   kb-local-only-p bindings)
  (declare (ignore inference-level error-p value-selector target-query))
  (if (variable? (first query))
      (values :fail t t)
      (or-fail
       (handle-ask-schema
	`(:is ?x ?y)
	(if (variable? ?y)
	    (continuable-error "The second argument to a :IS sentence ~
                                cannot be a variable: ~S" ?y)
	    (let ((expression-value (trivial-eval-for-okbc ?y nil)))
	      (if (variable? ?x)
		  (augment-bindings ?x (list expression-value))
		  (values (if (equal-in-kb-internal ?x expression-value
						    kb kb-local-only-p)
			      (list bindings)
			      :fail)
			  t)))))
       (handle-ask-schema
	`(:= ?x ?y)
	(if (variable? ?x)
	    (if (variable? ?y)
		(values :fail t)
		(augment-bindings ?x (list ?y)))
	    (if (variable? ?y)
		(augment-bindings ?y (list ?x))
		(values (if (equal-in-kb-internal ?x ?y kb kb-local-only-p)
			    (list bindings)
			    :fail)
			t))))
       (handle-ask-schema
	`(:/= ?x ?y)
	(if (or (variable? ?x) (variable? ?y))
	    (values :fail t)
	    (values (if (equal-in-kb-internal ?x ?y kb kb-local-only-p)
			:fail
			(list bindings))
		    t)))
       (handle-ask-schema
	`(:< ?x ?y)
	(if (or (variable? ?x) (variable? ?y))
	    (values :fail t)
	    (values (if (and (numberp ?x) (numberp ?y) (< ?x ?y))
			(list bindings)
			:fail)
		    t)))
       (handle-ask-schema
	`(:> ?x ?y)
	(if (or (variable? ?x) (variable? ?y))
	    (values :fail t)
	    (values (if (and (numberp ?x) (numberp ?y) (> ?x ?y))
			(list bindings)
			:fail)
		    t)))
       (handle-ask-schema
	`(:>= ?x ?y)
	(if (or (variable? ?x) (variable? ?y))
	    (values :fail t)
	    (values (if (and (numberp ?x) (numberp ?y) (>= ?x ?y))
			(list bindings)
			:fail)
		    t)))
       (handle-ask-schema
	`(:=< ?x ?y)
	(if (or (variable? ?x) (variable? ?y))
	    (values :fail t)
	    (values (if (and (numberp ?x) (numberp ?y) (<= ?x ?y))
			(list bindings)
			:fail)
		    t)))
       (if (procedure-p (first query))
	   (if (loop for arg in (rest query)
		     always (not (variable? arg)))
	       ;; The fully bound case returns just t or nil.
	       (if (call-procedure-internal (first query) kb (rest query))
		   (values (list bindings) t)
		   (values :fail t))
	       (let ((results (call-procedure-internal (first query) kb
						       (rest query))))
		 (if (eq :fail results)
		     (values :fail t)
		     (values
		      (loop for binding-set in results
			    collect (nconc (loop for (var val) in binding-set
						 collect (cons var val))
					   bindings))
		      t))))
	   (let ((match (second (assoc (first query)
				       *evaluable-predicate-alist*))))
	     (if match
		 (if (loop for arg in (rest query)
			   always (not (variable? arg)))
		     ;; The fully bound case returns just t or nil.
		     (if (let ((*current-kb* kb))
			   (apply match (rest query)))
			 (values (list bindings) t)
			 (values :fail t))
		     (let ((results (let ((*current-kb* kb))
				      (apply match (rest query)))))
		       (if (eq :fail results)
			   (values :fail t)
			   (values
			    (loop for binding-set in results
				  collect (nconc (loop for (var val)
						       in binding-set
						       collect (cons var val))
						 bindings))
			    t))))
		 (values :fail t t)))))))


(defun handle-frame-properties-query-internal
    (query target-query kb inference-level error-p value-selector
	   kb-local-only-p bindings relation get-function)
  (declare (ignore inference-level error-p value-selector query))
  (handle-target-ask-schema
   `(,relation ?frame ?value)
   (if (variable? ?frame)
       (if (variable? ?value)
	   (let ((pairs nil))
	     (loop for frame in (get-kb-frames-internal kb kb-local-only-p)
		   for value = (funcall get-function frame kb
					kb-local-only-p)
		   do (push (list frame value) pairs))
	     (values (if pairs
			 (loop for (frame value) in pairs
			       collect (append (list (cons ?frame frame)
						     (cons ?value value))
					       bindings))
			 :fail)
		     t))
	   (let ((frames nil))
	     (loop for frame in (get-kb-frames-internal kb kb-local-only-p)
		   for value = (funcall get-function frame kb
					kb-local-only-p)
		   when (equal value ?value)
		   do (push frame frames))
	     (values (if frames
			 (loop for frame in frames
			       collect (append (list (cons ?frame frame))
					       bindings))
			 :fail)
		     t)))
       (values
	(let ((value (funcall get-function ?frame kb kb-local-only-p)))
	  (if (variable? ?value)
	      (augment-bindings ?value (list value))
	      (if (equal value ?value)
		  (list bindings)
		  :fail)))
	t))))

(defun handle-frame-properties-query
    (query target-query kb inference-level error-p value-selector
	   kb-local-only-p bindings)
  (if (variable? (first query))
      (values :fail t t)
      (or-fail
       (handle-frame-properties-query-internal
	query target-query kb inference-level error-p value-selector
	kb-local-only-p bindings :name 'get-frame-name-internal)
       (handle-frame-properties-query-internal
	query target-query kb inference-level error-p value-selector
	kb-local-only-p bindings :pretty-name 'get-frame-pretty-name-internal)
       (handle-frame-properties-query-internal
	query target-query kb inference-level error-p value-selector
	kb-local-only-p bindings :handle 'get-frame-handle-internal))))

(defokbcgeneric handle-simple-query
    (query target-query kb inference-level error-p value-selector
	   kb-local-only-p bindings)
  (:documentation "This is a hook provided in the default implementation of
   OKBC's tell&ask.  It is called with a simple, atomic <code>query</code>
   in the OKBC tell&ask language (in KIF syntax).  <code>Bindings</code> is
   a set of bindings for known variables.  Methods on this generic function
   should return either a list of binding lists for matches found, or
   <code>:fail</code>.  For example, if <code>query</code> were
   <code>(:subclass-of ?x &lt;frame foo&gt;)</code>, then this method
   might return
   <code>(((?x .  &lt;class c1&gt;)) ((?x .  &lt;class c2&gt;)))</code>.
   This method is provided to give a trapdoor through to systems that
   can handle more complex queries than just the OKBC language.  Queries
   concerning n-ary relations, for example can be handled in an
   <code>:around</code> method that falls through to the default method for
   normal OKBC cases."))

(defokbcgeneric handle-unhandled-query
    (query target-query kb inference-level error-p value-selector
	   kb-local-only-p bindings)
  (:documentation "A trapdoor in the default implementation of OKBC's tell&ask
   handler that is called by <code>handle-simple-query</code> to address simple
   queries that do not match any of OKBC's standard axiom schemata.  This
   generic function should be specialized on back ends that know how to
   store arbitrary sentences, but that still use the default tell&ask
   mechanism for all of the standard OKBC axiom schemata."))

(defmethod handle-simple-query (query target-query (kb t) inference-level
				      error-p value-selector kb-local-only-p
				      bindings)
  ;; Sentential back ends might want to specialize this for inference-level
  ;; = :direct.
  (or-fail
   (handle-pragma-sentence query target-query kb inference-level error-p
			   value-selector kb-local-only-p
			   bindings)
   (handle-evaluable-predicate-query query target-query kb inference-level
				     error-p value-selector kb-local-only-p
				     bindings)
   (handle-frame-properties-query query target-query kb inference-level error-p
				  value-selector kb-local-only-p bindings)
   (handle-frame-type-query query target-query kb inference-level error-p
			    value-selector kb-local-only-p
			    bindings)
   (handle-primitivity-query query target-query kb inference-level error-p
			     value-selector kb-local-only-p bindings)
   (handle-instance/type-query query target-query kb inference-level error-p
			       value-selector kb-local-only-p
			       bindings)
   (handle-subclass-query query target-query kb inference-level error-p
			  value-selector kb-local-only-p bindings)
   (handle-slot-of-attachment-query query target-query kb inference-level
				    error-p value-selector kb-local-only-p
				    bindings :slot-of :own)
   (handle-slot-of-attachment-query query target-query kb inference-level
				    error-p value-selector kb-local-only-p
				    bindings :template-slot-of :template)
   (handle-facet-of-attachment-query query target-query kb inference-level
				     error-p value-selector kb-local-only-p
				     bindings :facet-of :own)
   (handle-facet-of-attachment-query query target-query kb inference-level
				     error-p value-selector kb-local-only-p
				     bindings :template-facet-of :template)
   (handle-slot-value-query query target-query kb inference-level error-p
			    value-selector kb-local-only-p bindings :own)
   (handle-slot-value-query query target-query kb inference-level error-p
			    value-selector kb-local-only-p bindings :template)
   (handle-facet-value-query query target-query kb inference-level error-p
			     value-selector kb-local-only-p bindings
			     :own)
   (handle-facet-value-query query target-query kb inference-level error-p
			     value-selector kb-local-only-p bindings
			     :template)
   (handle-unhandled-query query target-query kb inference-level error-p
			   value-selector kb-local-only-p bindings)))

(defmethod handle-unhandled-query (query (target-query t) (kb t)
					 (inference-level t) (error-p t)
					 (value-selector t) (kb-local-only-p t)
					 (bindings t))
  (error 'cannot-handle :sentence query))

