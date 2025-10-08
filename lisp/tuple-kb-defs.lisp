(in-package :tuple-store)

(defstruct tuple-store
  (dbclass-table (make-hash-table :test #'eql))
  (full-index-p t)
  (hash-index-p nil)
  (full-index nil)
  (kb nil)
  (atom-to-sentence-index nil))

(defun create-tuple-store (&optional (hash-index-p nil) (full-index-p t))
  (assert (not (and full-index-p hash-index-p)))
  (if hash-index-p
      (make-tuple-store :hash-index-p
			(make-hash-index :name :tuple-store)
			:full-index-p nil
			:dbclass-table :error-shouldnt-use-this
			:atom-to-sentence-index (tries:make-trie))
      (if full-index-p
	  (let ((ts (make-tuple-store)))
	    (setf (tuple-store-full-index ts)
		  (make-hash-table :test #'equal :size 5000))
	    ts)
	  (let ((ts (make-tuple-store :full-index-p nil)))
	    ts))))
  
(defdoc tuple-store (structure)
  "The defstruct used by <code>tuple-kb</code>s and
   <code>structure-tuple-kb</code>s to store their knowledge as tuples.")

(defdoc tuple-store (function)
  "An accessor on <code>tuple-kb</code>s and
   <code>structure-tuple-kb</code>s that delivers the
   <code>tuple-store</code> used to store the knowledge in the KB.")

(defmethod mark-to-require-rehash :after ((ts tuple-store))
 (mark-to-require-rehash (tuple-store-dbclass-table ts))
 (mark-to-require-rehash (tuple-store-full-index ts)))

(defokbcgeneric tuple-store (kb))

(defmacro fetch-one-bindingm (pattern kb &optional filter (index-hint 0)
				      (check-included-kbs-p t))
  "Similar to fetch-one-binding, only you don't need to specify the
   pattern-hash-key."
  `(let ((.pattern. ,pattern))
    (fetch-one-binding .pattern. ,kb ,filter ,index-hint
     (pattern-hash-key .pattern.) ,check-included-kbs-p t)))

(defmacro tuple-store-fetchm
    (pattern kb &key (test nil) (return-pattern pattern)
	     (index-hint 0) (check-included-kbs-p t)
	     (max-matches nil) (uniquifying-table nil))
  "Fetch any facts matching PATTERN in KB.  The test
optional TEST function called with the pattern and a fact and should
return :fail if the fact cannot match the pattern.  Return the result
of substituting unify's bindings on the pattern."
  `(let ((.pattern. ,pattern))
    (tuple-store-fetch .pattern.
     ,kb
     :test ,test
     :return-pattern ,return-pattern 
     :index-hint ,index-hint
     :check-included-kbs-p ,check-included-kbs-p
     :max-matches ,max-matches
     :pattern-hash-key (pattern-hash-key .pattern.)
     :uniquifying-table ,uniquifying-table)))

(defvar *kbs-to-search*)

(defun check-included-kbs-p (kb kb-local-only-p)
  (if kb-local-only-p
      nil
      (if (boundp '*kbs-to-search*)
	  (or (second (assoc kb *kbs-to-search*)) t)
	  t)))

(defmacro with-kbs-to-search ((kb) &body body)
  `(if (and (ok-back:kb-p-internal ,kb) (tuple-store ,kb))
       (let ((*kbs-to-search*
	      (cons (list ,kb (tuple-store-precedence-list (tuple-store ,kb)))
		    (if (boundp '*kbs-to-search*)
			*kbs-to-search*
			nil))))
	 ,@body)
        (progn ,@body)))

(in-package :tuple-kb)

(defparameter *default-tuple-kb-indexing-type* :hash-index)

(defstruct (tuplekb-locator (:include file-kb-locator)))

(defparameter *tuplekb-supported-behaviors*
  `((:constraint-checking-time   t :immediate :never)
    (:constraint-report-time   nil :immediate)
    (:constraints-checked      nil :value-type :inverse :cardinality
			           :minimum-cardinality :maximum-cardinality
				   :same-values :not-same-values 
				   :subset-of-values :numeric-minimum
				   :numeric-maximum :some-values 
				   :collection-type :domain
                                   :slot-value-type :slot-inverse
                                   :slot-cardinality :slot-minimum-cardinality
                                   :slot-maximum-cardinality :slot-same-values
                                   :slot-not-same-values :slot-subset-of-values
                                   :slot-numeric-minimum :slot-numeric-maximum
                                   :slot-some-values :slot-collection-type)
    (:defaults                 nil :override)
    (:compliance               nil :facets-supported :user-defined-facets
                                   :read-only :monotonic)
    (:class-slot-types         nil :template :own)
    (:collection-types         nil :set)
    (:frame-names-required       t nil t)
    (:are-frames               nil :class :facet :slot :instance :individual)))

(defparameter *tuplekb-default-behaviors*
  `((:constraint-checking-time :immediate)
    (:constraint-report-time   :immediate)
    (:constraints-checked      :value-type :inverse :cardinality
			       :minimum-cardinality :maximum-cardinality
			       :same-values :not-same-values 
			       :subset-of-values :numeric-minimum
			       :numeric-maximum :some-values 
			       :collection-type :domain
                               :slot-value-type :slot-inverse
                               :slot-cardinality :slot-minimum-cardinality
                               :slot-maximum-cardinality :slot-same-values
                               :slot-not-same-values :slot-subset-of-values
                               :slot-numeric-minimum :slot-numeric-maximum
                               :slot-some-values :slot-collection-type)
    (:defaults                 :override)
    (:compliance               :facets-supported :user-defined-facets
                               :read-only :monotonic)
    (:class-slot-types         :template :own)
    (:collection-types         :set)
    (:frame-names-required     nil)
    (:are-frames               :class :facet :slot :instance :individual)))

(defstruct (ok-back:structure-tuple-kb
	     (:include ok-back:file-structure-kb)
	     (:constructor construct-structure-tuple-kb)
	     (:predicate is-a-structure-tuple-kb))
  (parent-kbs nil)
  (frame-name-mapping-table (make-hash-table :test #'eq))
  (name-to-frame-mapping-table (make-hash-table :test #'eq))
  (read-only-p nil)
  (current-behaviors (copy-tree *tuplekb-default-behaviors*))
  (tuple-store (tuple-store::create-tuple-store))
  (cache-of-frame-frame-local nil)
  (cache-of-frame-frame-global nil)
  (cache-of-class-frame-local nil)
  (cache-of-class-frame-global nil)
  (cache-of-slot-frame-local nil)
  (cache-of-slot-frame-global nil)
  (cache-of-facet-frame-local nil)
  (cache-of-facet-frame-global nil)
  (cache-of-individual-frame-local nil)
  (cache-of-individual-frame-global nil)
  (io-package (find-package :user)))

(defmethod io-package ((kb ok-back::structure-tuple-kb))
 (structure-tuple-kb-io-package kb))

(defmethod (setf io-package) (new (kb ok-back::structure-tuple-kb))
 (let ((package (if (packagep new) new (find-package new))))
   (setf (structure-tuple-kb-io-package kb) package)))

(defdoc ok-back:structure-tuple-kb (structure)
  "This is the structure-object equivalent of <code>tuple-kb</code>.")

(defmethod mark-to-require-rehash :after ((kb ok-back:structure-tuple-kb))
 (when (and (hash-table-p
	     (tuple-kb::structure-tuple-kb-frame-name-mapping-table kb)))
   (mark-to-require-rehash
    (structure-tuple-kb-frame-name-mapping-table kb)))
 (without-recursion-in-stack
  (mark-to-require-rehash-tuple-kb kb nil)
  (loop for prev in (get-kb-direct-parents-internal kb)
	do (mark-to-require-rehash prev))))

(defokbcclass ok-back:abstract-tuple-kb-kb () ())

(defokbcclass ok-back:tuple-kb
    (;;;; frame-name-interning-mixin ;; not any more!
     ok-utils:assert-kif-definitions-as-sentences-mixin
     ok-back:abstract-tuple-kb-kb
     ok-back:caching-mixin
     ok-back:handle-number-of-values-mixin
     ok-back:default-inheritance-mixin
     ok-back:file-mixin
     ok-back:standard-defaults-kb)
  ((parent-kbs   :accessor tuple-kb-parent-kbs   :initarg :parent-kbs
		 :initform nil)
   (tuple-store  :accessor tuple-kb-tuple-store :initarg :tuple-store
		 :initform (tuple-store::create-tuple-store))
   (read-only-p  :accessor read-only-p           :initarg :read-only-p
		 :initform nil)
   (current-behaviors :initform (copy-tree *tuplekb-default-behaviors*)
		      :initarg :current-behaviors
		      :accessor current-behaviors)
   (cache-of-frame-frame-local  :accessor tuple-kb-cache-of-frame-frame-local
				:initform nil)
   (cache-of-frame-frame-global :accessor tuple-kb-cache-of-frame-frame-global
			        :initform nil)
   (cache-of-class-frame-local  :accessor tuple-kb-cache-of-class-frame-local
			        :initform nil)
   (cache-of-class-frame-global :accessor tuple-kb-cache-of-class-frame-global
			        :initform nil)
   (cache-of-slot-frame-local   :accessor tuple-kb-cache-of-slot-frame-local
			        :initform nil)
   (cache-of-slot-frame-global  :accessor tuple-kb-cache-of-slot-frame-global
			        :initform nil)
   (cache-of-facet-frame-local  :accessor tuple-kb-cache-of-facet-frame-local
			        :initform nil)
   (cache-of-facet-frame-global :accessor tuple-kb-cache-of-facet-frame-global
			        :initform nil)
   (cache-of-individual-frame-local
    :accessor tuple-kb-cache-of-individual-frame-local :initform nil)
   (cache-of-individual-frame-global
    :accessor tuple-kb-cache-of-individual-frame-global :initform nil)
   (io-package :initarg :io-package :accessor io-package :initform
	       (find-package :user)))
  (:documentation "A class of KB that stores the knowledge in the KB in a
   <code>tuple-store</code> as logical sentences.  This class, and its
   companion defstruct class <code>structure-tuple-kb</code>, are the
   only compliant OKBC KB classes shipped as part of the default
   implementation of OKBC in Lisp. It is generally expected that OKBC will
   be bound to the representation systems in use at the user's site, but if
   there is no such representation system this class can be used.  It
   implements a fully compliant KB that gives full support for slots,
   annonymous or named frames, and checks all of the OKBC-defined
   constraints."))

(defmethod mark-to-require-rehash :after ((kb tuple-kb))
 (without-recursion-in-stack
  (mark-to-require-rehash-tuple-kb kb nil)
  (loop for prev in (get-kb-direct-parents-internal kb)
	do (mark-to-require-rehash prev))))

(defmethod tuple-store ((instance t))
 ;; A stub method that says that random things don't have tuple-stores.
 ;; This is used in with-kbs-to-search
  nil)

(defmethod tuple-store ((instance tuple-kb))
  (tuple-kb-tuple-store instance))

(defmethod (setf tuple-store) (new-value (instance tuple-kb))
  (setf (tuple-kb-tuple-store instance) new-value))

(defmethod current-behaviors ((instance structure-tuple-kb))
  (structure-tuple-kb-current-behaviors instance))

(defmethod (setf current-behaviors) (new-value (instance structure-tuple-kb))
  (setf (structure-tuple-kb-current-behaviors instance) new-value))

(defmethod tuple-store ((instance structure-tuple-kb))
  (structure-tuple-kb-tuple-store instance))

(defmethod (setf tuple-store) (new-value (instance structure-tuple-kb))
  (setf (structure-tuple-kb-tuple-store instance) new-value))

(defmethod read-only-p ((instance structure-tuple-kb))
  (structure-tuple-kb-read-only-p instance))

(defnetwork-okbc-kb ok-back:tuple-kb (caching-mixin))

;==============================================================================

;;; Pattern compiler

(defmethod find-interesting-indvars (pattern)
  (if (consp pattern)
      (remove-duplicates
       (loop for arg in pattern append (find-interesting-indvars arg)))
      (if (and (variable? pattern)
	       (not (search "IGNORE" (symbol-name pattern)
			    :test #'char-equal)))
	  (list pattern)
	  nil)))

(defun dotted-p (thing)
  (and (consp thing)
       (loop do (pop thing)
	     when (not thing) return nil
	     when (not (consp thing)) return t)))

(defun flatten-conjunctions (list &optional (conjunction-operator 'and))
  (if (consp list)
      (if (eq conjunction-operator (first list))
	  (if (= (length list) 2)
	      (flatten-conjunctions (second list) conjunction-operator)
	      (let ((found-p nil))
		(let ((result
		       (loop for arg in (rest list)
			     append (if (and (consp arg)
					     (eq conjunction-operator
						 (first arg)))
					(progn (setq found-p t) (rest arg))
					(list arg)))))
		  (if found-p
		      (flatten-conjunctions (cons conjunction-operator result)
					    conjunction-operator)
		      (cons conjunction-operator
			    (loop with results =
				  (loop for arg in result
					collect (flatten-conjunctions
						 arg conjunction-operator))
				  for arg in results
				  for rest on results
				  unless (member arg (rest rest) :test #'eq)
				  collect arg))))))
	  (loop for arg in list
		collect (if (dotted-p arg)
			    arg
			    (flatten-conjunctions arg conjunction-operator))))
      list))

(defun subst-vars (tree)
  (if (consp tree)
      (cond ((eq :Indvar (first tree)) (second tree))
	    ((eq :Seqvar (first tree)) (second tree))
	    (t (cons (subst-vars (first tree)) (subst-vars (rest tree)))))
      tree))

(defvar *bindings-at-this-contour*)
(defvar *handled-vars*)
(defvar *depth*)

(defun maybe-insert-return-pattern (list)
  (declare (special *return-match-p* *bindings*))
  (if *return-match-p*
      (if (and (= (length list) 2)
	       (member (first list) '(:seqvar :indvar)))
	  (if (and (symbolp *return-match-p*)
		   (eq (second list)
		       (second (assoc *return-match-p*
				      *bindings*))))
	      list
	      (list 'and list
		    (if (consp *return-match-p*)
			`(list
			  ,@(loop for x in *return-match-p*
				  collect
				  (second
				   (assoc x *bindings*))))
			(second (assoc *return-match-p*
				       *bindings*)))))
	  (case (first list)
	    (let (assert (not (fourth list)))
	      (list (first list)
		    (second list)
		    (maybe-insert-return-pattern (third list))))
	    (and (append (butlast list)
			 (list (maybe-insert-return-pattern
				(first (last list))))))
	    (otherwise list)))
      list))

(defun append-bindings-for-this-contour (body)
  (assert body)
  (let ((new (set-difference *bindings-at-this-contour* *handled-vars*
			     :test #'equal)))
    (if new
	(let ((result (if (eq 'and (first body))
			  (append body new)
			  `(and ,body ,@new))))
	  (loop for b in new
		do (pushnew b *handled-vars* :test #'equal))
	  result)
	body)))

(defun var-in-tree-p-checking-lambda-contours (tree)
  (if (consp tree)
      (if (eq 'let (first tree))
	  nil
	  (if (member (first tree) '(:Seqvar :Indvar))
	      tree
	      (or (var-in-tree-p-checking-lambda-contours (first tree))
		  (var-in-tree-p-checking-lambda-contours (rest tree)))))
      (and (kif-variable-p tree) tree)))

(defun move-variables-to-end-1 (list)
  (declare (special *return-match-p* *bindings*))
  (if (consp list)
      (if (eq 'let (first list)) ;; cross lambda contour
	  (let ((*bindings-at-this-contour*
		 *bindings-at-this-contour*)
		(*depth* (+ 1 *depth*)))
	    (loop for entry in (second list)
		  for x = (first entry)
		  when (member x '(:Seqvar :Indvar))
		  do (push x *bindings-at-this-contour*))
	    (let ((body (move-variables-to-end-1 (third list))))
	      (assert (not (fourth list)))
	      (assert (third list))
	      (assert body)
;	      (pprint :-----------------)
;	      (pprint list)
	      (let ((result (list (first list) (second list)
				  (append-bindings-for-this-contour body))))
;		(pprint result)
		result)))
	  (let ((var (loop for x in list
			   for var = (var-in-tree-p-checking-lambda-contours x)
			   when var return x)))
;	    (print (list :var========== var))
	    (if var
		(let ((remainder (remove var list :test #'equal)))
		  (assert remainder)
		  (push var *bindings-at-this-contour*)
		  (move-variables-to-end-1 remainder))
		(mapcar 'move-variables-to-end-1 list))))
      list))

(defun move-variables-to-end (list)
  (declare (special *return-match-p* *bindings*))
  (let ((*bindings-at-this-contour* nil)
	(*handled-vars* nil)
	(*depth* 0))
    (Subst-vars
     (maybe-insert-return-pattern
      (append-bindings-for-this-contour
       (move-variables-to-end-1 list))))))

(defun names-a-seqvar-p (thing)
  (and (consp thing) (eq (first thing) 'quote)
       (variable? (second thing))))

(defmethod build-gensym (prefix (thing t))
  (gensym (format nil "~A-" prefix)))

(defmethod build-gensym (prefix (thing symbol))
  (gensym (format nil "~A-~A-" prefix thing)))

(defmethod build-gensym-cons (prefix (thing cons) (cadr symbol))
  (format nil "~A-Q-~A-" prefix (second thing)))

(defmethod build-gensym-cons (prefix (thing cons) (cadr t))
  (format nil "~A-Q-" prefix))

(defmethod build-gensym (prefix (thing cons))
  (if (eq 'quote (first thing))
      (gensym (build-gensym-cons prefix thing (second thing)))
      (gensym (format nil "~A-Q-" prefix))))

(defun make-condition-for-known-lists
    (pattern pattern-name test-structure-name comparator-alist)
  "Makes a condition for the specified pattern now that we know that we're
   dealing with a list type of pattern."
  (declare (special *referenced-variables* *bindings*))
  (let ((gensymsa
	 (loop for thing in pattern
	       collect (locally #-TI (declare (ignore thing))
				(build-gensym "PATTERN" thing))))
	(gensymsb
	 (loop for thing in pattern
	       collect (locally #-TI (declare (ignore thing))
				(build-gensym "CANDIDATE" thing))))
	(cdr-map  (loop for thing in pattern
			collect (names-a-seqvar-p thing))))
    (let ((conjunction-from-rest
	   (cons 'and
		 (remove t
			 (loop for thing in pattern
			       for gena in gensymsa
			       for genb in gensymsb
			       collect (make-condition-for-pattern
					thing gena genb comparator-alist)))))
	  (indvar-alist
	   (loop for thing in pattern
		 for gensym in gensymsb
		 when (and (consp thing) (eq 'quote (first thing))
			   (variable? (second thing)))
		 collect (list (second thing) gensym))))
      (setq *bindings* (append indvar-alist *bindings*))
      (values
       (list 'let
	     (append
	      (loop for gena in gensymsa
		    for cdr-p in cdr-map
		    for index from 0
		    when (member gena *referenced-variables*)
		    collect
		    (progn
		      (pushnew pattern-name *referenced-variables*)
		      (list gena `(,(if cdr-p 'nthcdr 'nth)
				   ,index (the list ,pattern-name)))))
	      (loop for genb in gensymsb
		    for cdr-p in cdr-map
		    for index from 0
		    when (member genb *referenced-variables*)
		    collect
		    (progn
		      (pushnew test-structure-name
			       *referenced-variables*)
		      (list genb `(,(if cdr-p 'nthcdr 'nth)
				   ,index (the list ,test-structure-name))))))
	     conjunction-from-rest)
       indvar-alist))))

(defmethod object-reference-p ((thing symbol)) t)
(defmethod object-reference-p ((thing t)) nil)

(defun make-comparator-for (pattern pattern-name test-structure-name
				    &optional (real-test-structure-name
					       test-structure-name))
  "Makes a form that compares the pattern with the test structure."
  (declare (special *referenced-variables* *return-match-p*))
  (declare (ignore pattern-name))
  (if (object-reference-p pattern)
      (cond ((variable? pattern)
	     (if *return-match-p*
		 (progn (pushnew real-test-structure-name
				 *referenced-variables*)
			(list :Indvar test-structure-name))
		 t))
	    ((sequence-variable-p pattern)
	     (if *return-match-p*
		 (progn (pushnew real-test-structure-name
				 *referenced-variables*)
			(list :Seqvar test-structure-name))
		 t))
	    (t (pushnew real-test-structure-name *referenced-variables*)
	       `(eq ',pattern ,test-structure-name)))
      (progn (pushnew real-test-structure-name *referenced-variables*)
	     `(#-dont-use-fast-equal fast-equal
	       #+dont-use-fast-equal equal
	       ',pattern ,test-structure-name))))

(defun make-condition-for-pattern (pattern pattern-name test-structure-name
					   comparator-alist)
  "Makes a condition that tests for a match for a pattern. 
   This can be compiled into a function to make Epikit
   searches more efficient."
  (declare (special *referenced-variables*))
  (if (consp pattern)
      (if (eq 'quote (first pattern))
	  (make-comparator-for (second pattern)
			       pattern-name test-structure-name)
	  (multiple-value-bind (body alist)
	      (Make-Condition-For-Known-Lists
	       pattern pattern-name test-structure-name comparator-alist)
	    (values
	     `(and (consp ,test-structure-name)
	       ,(if (find-if 'names-a-seqvar-p pattern)
		    `(>= (length (the list ,test-structure-name))
		      ,(- (length pattern)
			  (count-if 'names-a-seqvar-p pattern)))
		    `(= ,(length pattern)
		      (length (the list ,test-structure-name))))
	       ,body)
	     alist)))
      (if (object-reference-p pattern)
	  (progn (pushnew pattern-name *referenced-variables*)
		 (pushnew test-structure-name *referenced-variables*)
		 `(;eq ;;; this has to be from the comparator alist, because
		   ;; it is not quoted.
                   ,(or (second (assoc pattern comparator-alist :test #'eq))
                        #-dont-use-fast-equal 'fast-equal
                        #+dont-use-fast-equal 'equal)
		   ,pattern-name ,test-structure-name))
	  (progn (pushnew test-structure-name *referenced-variables*)
		 `(,(or (second (assoc pattern comparator-alist :test #'eq))
			#-dont-use-fast-equal 'fast-equal
			#+dont-use-fast-equal 'equal)
		   ',pattern ,test-structure-name)))))

(defun deconsify (list)
  (if (consp list)
      (if (eq 'cons (first list))
	  (if (and (consp (third list)) (eq (first (third list)) 'quote))
	     `(list ,(second list) ,@(loop for x in (second (third list))
					   collect `(quote ,x)))
	      (progn (warn "Can't interpret list ~S" list) list))
	  (mapcar 'deconsify list))
      list))

(defun remove-any-outer-quote (x)
  (if (and (consp x) (eq (first x) 'quote))
      (cons 'list (loop for thing in (second x) collect `(quote ,thing)))
      x))

(defun remove-lists (list)
  "Removes calls to the function LIST from the list."
  (if (consp list)
      (case (first list)
	((list #+EXCL excl::bq-list) (mapcar 'remove-lists (rest list)))
	(quote list)
	(list*
	 (if (and (consp (first (last list)))
		  (eq (first (first (last list))) 'quote))
	     (append (mapcar 'remove-lists (butlast (rest list)))
		     (second (first (last list))))
	     (progn (warn "Strange list structure found in ~S" list) list)))
	#+EXCL
	(excl::bq-cons
	 (let ((car (second list))
	       (cdr (third list)))
	   (mapcar 'remove-lists
		   (cons car
			 (if (eq (first cdr) 'quote)
			     (loop for x in (second cdr)
				   collect (list 'quote x))
			     cdr)))))
	#+EXCL
	(excl::bq-list*
	 (mapcar 'remove-lists
		 (loop for arg in (rest list)
		       for tail on (rest list)
		       append (if (rest tail)
				  (list arg)
				  (if (eq (first arg) 'quote)
				      (loop for x in (second arg)
					    collect (list 'quote x))
				      arg)))))
	(otherwise (warn "Strange list structure found in ~S" list) list))
      list))

(defokbcgeneric ok-utils:self-evaluating-p (x)
  (:documentation "This predicate is true if the argument <code>x</code> is
   a self-evaluating form, such as a literal number, or a quoted sexpression."))

(defmethod ok-utils:self-evaluating-p ((x t)) nil)
(defmethod ok-utils:self-evaluating-p ((x cons)) (eq (first x) 'quote))
(defmethod ok-utils:self-evaluating-p ((x string)) t)
(defmethod ok-utils:self-evaluating-p ((x number)) t)
(defmethod ok-utils:self-evaluating-p ((x symbol))
  (or (keywordp x) (case x ((t nil) t) (otherwise nil))))
(defmethod ok-utils:self-evaluating-p ((x vector))
  (loop for i from 0 below (length x)
	for e = (aref x i)
	always (self-evaluating-p e)))

(defun unlist*ify (list)
  "Removes references to list* by opening them out into lists with suitable
   quotes."
  (if (and (consp list) (eq 'list* (first list)))
      (let ((last (first (last list))))
	   (if (and (consp last)
		    (eq 'quote (first last))
		    (consp (second last)))
	       (cons 'list (append (mapcar 'unlist*ify (rest (butlast list)))
				   (loop for x in (second last)
					 collect
					 (if (and (self-evaluating-p x)
						  (not (and (consp x)
							    (eq (first x)
								'quote))))
					     x
					     `(quote ,x)))))
	       (progn (warn "Couldn't unlist*ify ~S" list)
		      list)))
      list))

(defun genericise-macroexpanded-bq-list (list)
  #+(or EXCL TI) list
  #+Harlequin-Common-Lisp 
  (subst 'list* 'system::bq-list* (subst 'list 'system::bq-list list))
  #+Lucid (subst 'list* 'lucid-runtime-support::bq-list*
                 (subst 'list 'lucid-runtime-support::bq-list
			(subst 'cons 'lucid-runtime-support::bq-cons list)))
  #-(or EXCL Lucid TI Harlequin-Common-Lisp) (error "need a fix here."))

(defun macroexpand-completely (form &optional (environment nil))
  #+TI (ticl:macroexpand-all form environment)
  #-TI
  (let ((result (macroexpand form environment)))
    (if (consp result)
	(cons (first result)
	      (loop for arg in (rest result)
		    collect (macroexpand-completely arg environment)))
	result)))

(defvar user::*enable-pattern-compilation-p* t)
(defvar *match-optimize-speed* 1)

(defmacro tuple-store:compile-pattern
    (pattern &key (return-match-p t)
	     (return-pattern
	      (find-interesting-indvars pattern)
	      supplied-p)
	     (comparator-alist nil))
  "Given a pattern such as `(,relation ,object ?x), generates a match function
 that specifically detects this sort of query.  If return-match-p is true then
 the binding that matches is returned, otherwise just a truth value is 
 computed."
  ;;; e.g. `(,relation ,object $x)
  (assert (or supplied-p (not (rest return-pattern))) ()
	  "You must supply a return pattern or ignore something in ~S"
	  pattern)
  (let ((actual-return-pattern
	 (if supplied-p
	     (if (and (consp return-pattern)
		      (eq 'quote (first return-pattern)))
		 (second return-pattern)
		 return-pattern)
	     (first return-pattern))))
    (if (ecase user::*enable-pattern-compilation-p*
	  ((t)
	   #-Lucid
	   (>= #-EXCL
	       (second (assoc 'speed (cl::declaration-information 'optimize)))
	       #+(and allegro-version>= (version>= 5))
	       excl::.speed.
	       #+(and allegro-version>= (not (version>= 5)))
	       #+EXCL comp::.speed.
	       *match-optimize-speed*)
	   #+lucid
	   (zerop
	    (rest (assoc 'compilation-speed lucid::*compiler-optimizations*))))
	  ((nil) nil)
	  (:force t))
	(let ((*referenced-variables* nil)
	      (*return-match-p* (and return-match-p actual-return-pattern))
	      (*bindings* nil))
	  (declare (special *referenced-variables* *return-match-p*
			    *bindings*))
	  (let ((body (flatten-conjunctions
		       (move-variables-to-end
			(make-condition-for-pattern
			 (remove-lists
			  (unlist*ify
			   (deconsify
			    (remove-any-outer-quote
			     (genericise-macroexpanded-bq-list
			      (macroexpand-completely pattern))))))
			 'pattern 'test-structure comparator-alist)))))
	    (let ((function
		   `#'(lambda (pattern test-structure)
		    ,@(if (is-in-tree 'pattern body)
			  nil
			  '((declare (ignore pattern))))
		    (or ,body :fail))))
	      ;;;(pprint function)
	      function)))
	''unify)))

;==============================================================================

;;; Needed for macro expansion

(eval-when (compile load eval) (proclaim '(inline ok-utils:variable?)))

(defun ok-utils:variable? (x)
  "Return T if X is a variable."
  (and (symbolp x)
       (let ((sn (symbol-name x)))
	 (and (> (length (the simple-string sn)) 0)
	      (char= #\? (schar sn 0))))))

(defun ok-utils:anonymous-variable? (x)
  "Return T if X is an anonymous variable."
  (and (symbolp x)
       (let ((sn (symbol-name x)))
	 (and (= (length (the simple-string sn)) 1)
	      (char= #\? (schar sn 0))))))

(defun ok-utils:sequence-variable-p (thing)
  "Non NIL iff THING is a KIF sequence variable (a symbol whose name
begins with a '@')."
  (and (symbolp thing)
       (let ((sn (symbol-name thing)))
	 (and (> (length (the simple-string sn)) 0)
	      (char= #\@ (schar sn 0))))))

(defun ok-utils:kif-variable-p (thing)
  "Non NIL iff THING is a KIF individual variable (a symbol whose name 
begins with a '?') or sequence variable (starts with '@')."
  (or (variable? thing)
      (sequence-variable-p thing)))

;==============================================================================

;;;----------------------------------------------------------------------
;;; SIMPLE UNIFICATION and LOGIC UTILITIES
;;;----------------------------------------------------------------------


(defun ok-utils:variables-in (pattern &optional vars)
  "Returns a list of all of the KIF variables in the <code>pattern</code> that
   are not in the list <code>vars</code>."   
  (labels
      ((vars-in (pattern vars)
	 (cond ((consp pattern)
		(if (and (symbolp (first pattern))
			 (string-equal 'quote (first pattern)))
		    vars
		    (vars-in (cdr pattern)
			     (vars-in (car pattern) vars))))
	       ((and (variable? pattern)
		 (not (anonymous-variable? pattern)))
		(pushnew pattern vars))
	       (t vars))))
    (nreverse (vars-in pattern (reverse vars)))))

(defun ok-utils:ground? (x &optional ground-vars)
  "Return T if X contains no variables other than GROUND-VARS."
  (subsetp (variables-in x) ground-vars))

(defun free-in? (var exp bindings)
  ;; Returns nil if <var> occurs in <exp>,
  ;;    assuming <bindings>.
  (cond ((null exp) t)
	((fast-equal var exp) nil)
	((variable? exp)
	 (let ((val (assoc exp bindings)))
	   (if val 
	    (free-in? var (cdr val) bindings)
	    t)))
	((not (listp exp)) t)
	((free-in? var (car exp) bindings)
	 (free-in? var (cdr exp) bindings))))

(defun unify-variable-against-literal (var exp bindings &aux val)
  (cond
    ((anonymous-variable? var) bindings)
    (t (setq val (assoc var bindings))
       (cond (val (if (variable? (rest val))
		      (if (eq (rest val) exp)
			  bindings
			  :fail)
		      (unify-against-literal (cdr val) exp bindings)))
	     ;; If safe, bind <var> to <exp>
	     ((or (eq var exp) (free-in? var exp bindings))
	      (cons (cons var exp) bindings))
	     (t :FAIL)))))

(defun ok-utils:unify-against-literal (a b &optional (bindings nil))
  "Unifies the form <code>a</code> against the literal <code>b</code>
   using the binding alist <code>bindings</code>.  Returns the binding alist
   that achieves the unification, or <code>:fail</code><P>

   This function is useful when detecting axiom schemata.  For example,
   If we want to detect instances of the (:subclass-of ?x ?y) schema,
   we can get bindings for this using:
   <PRE>(unify-against-literal '(:subclass-of ?x ?y) form)</PRE>
   so if <code>form</code> were <code>(:subclass-of fred ?x)</code>, we would
   get back the binding list: <code>((?y . ?x) (?x . fred))</code>."
  (cond ((and (fast-equal a b) (not (variables-in a))) bindings)
	((variable? a) (unify-variable-against-literal a b bindings))
	((and (consp a) (consp b)
	 (not (eq :FAIL
		  (setq bindings
			(unify-against-literal (car a) (car b) bindings)))))
	 (unify-against-literal (cdr a) (cdr b) bindings))
	(t :FAIL)))

(defun unify-variable (var exp bindings &aux val)
  ;; Must distinguish no value from value of nil
  (cond
    ((anonymous-variable? var)
     bindings)
    (t
     (setq val (assoc var bindings))
     (cond (val (unify (cdr val) exp bindings))
	   ;; If safe, bind <var> to <exp>
	   ((free-in? var exp bindings)
	    (cons (cons var exp) bindings))
	   (t :FAIL)))))

(defun ok-utils:unify (a b &optional (bindings nil))
  "Unify A and B.  Return the list of bindings for the most general
unifier for A and B or :fail if they do not unify."
  (cond ((fast-equal a b) bindings)
	((variable? a) (unify-variable a b bindings))
	((variable? b) (unify-variable b a bindings))
	;;((or (not (listp a)) (not (listp b))) :FAIL)
	;; af 8/1/96
	;; THe above was a BUG: (unify '(?x ?y) '(a)) didn't fail!
	((and (consp a) (consp b)
	 (not (eq :FAIL
		  (setq bindings
			(unify (car a) (car b) bindings)))))
	 (unify (cdr a) (cdr b) bindings))
	(t :FAIL)))

;==============================================================================

(in-package :ok-kernel)

(defparameter *meta-kb-supported-behaviors*
  `((:constraint-checking-time nil :never)
    (:constraint-report-time   nil :immediate)
    (:constraints-checked      nil :value-type :inverse :cardinality
			           :minimum-cardinality :maximum-cardinality
				   :same-values :not-same-values 
				   :subset-of-values :numeric-minimum
				   :numeric-maximum :some-values 
				   :collection-type :domain
                                   :slot-value-type :slot-inverse
                                   :slot-cardinality :slot-minimum-cardinality
                                   :slot-maximum-cardinality :slot-same-values
                                   :slot-not-same-values :slot-subset-of-values
                                   :slot-numeric-minimum :slot-numeric-maximum
                                   :slot-some-values :slot-collection-type)
    (:defaults                 nil :override)
    (:compliance               nil :facets-supported :user-defined-facets
                                   :read-only :monotonic)
    (:class-slot-types         nil :template :own)
    (:collection-types         nil :set)
    (:frame-names-required     nil nil)
    (:are-frames               nil :class :facet :slot :instance :individual)))

(defparameter *meta-kb-default-behaviors*
  `((:constraint-checking-time :never)
    (:constraint-report-time   :immediate)
    (:constraints-checked      :value-type :inverse :cardinality
			       :minimum-cardinality :maximum-cardinality
			       :same-values :not-same-values 
			       :subset-of-values :numeric-minimum
			       :numeric-maximum :some-values 
			       :collection-type :domain
                               :slot-value-type :slot-inverse
                               :slot-cardinality :slot-minimum-cardinality
                               :slot-maximum-cardinality :slot-same-values
                               :slot-not-same-values :slot-subset-of-values
                               :slot-numeric-minimum :slot-numeric-maximum
                               :slot-some-values :slot-collection-type)
    (:defaults                 :override)
    (:compliance               :facets-supported :user-defined-facets
                               :read-only :monotonic)
    (:class-slot-types         :template :own)
    (:collection-types         :set)
    (:frame-names-required     nil)
    (:are-frames               :class :facet :slot :instance :individual)))

(defokbcclass ok-back:abstract-meta-kb-kb () ())

(defokbcclass ok-back:meta-kb
    (ok-back:abstract-meta-kb-kb
     ok-back:frames-have-clos-slots-as-okbc-slots-mixin ok-back:tuple-kb)
  ()
  (:documentation "The CLOS class of KB used to implement the Meta Kb for the
   Lisp implementation of OKBC.  This KB is a subclass of <code>tuple-kb</code>
   which it uses for general fact storage, and of
   <code>frames-have-clos-slots-as-okbc-slots-mixin</code>, which is provided
   so that CLOS slots in objects like KB locators and KB class objects appear
   as OKBC slots."))

(defnetwork-okbc-kb ok-back:meta-kb ())

