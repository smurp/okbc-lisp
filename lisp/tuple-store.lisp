(in-package :tuple-store)

(defvar *visited-kbs*)

(defvar *number-to-find*)

(defstruct index-entry
  (facts nil)
  (count 0)
  ;; Note:  we could make a subclass of index entry for subindexed ones,
  ;; but for now I'd rather pay one extra word of memory than an extra
  ;; generic function dispatch on each index access.
  (subindex nil)
  (key-stack nil))

(defmethod print-object ((instance index-entry) (stream t))
  (typecase (index-entry-key-stack instance)
    (null (format stream "#<Index entry ~D: Anonymous>"
		  (index-entry-count instance)))
    (cons (format stream "#<Index entry ~D: {~{~A~^, ~}}>"
		  (index-entry-count instance)
		  (reverse (index-entry-key-stack instance))))
    (otherwise (format stream "#<Index entry ~D: ~A>"
		       (index-entry-count instance)
		       (index-entry-key-stack instance)))))

(defmethod print-object ((instance tuple-store) (stream t))
   (if (or #-(or Allegro Harlequin-Common-Lisp) *print-structure*
	   #+Allegro excl:*print-structure*
	   #+Harlequin-Common-Lisp hcl:*print-structure*
	   (not (tuple-store-kb instance)))
       (call-next-method)
       (print-unreadable-object
	(instance stream :type t :identity t)
	(format stream "for ~S" (tuple-store-kb instance)))))



(defparameter *subindex-threshold* 75)
(defparameter *stop-index-search-threshold* 20)

(defstruct (dbclass (:print-function dbclass-printer))
  name					;a symbol
  kb					;kb it belongs to
  facts					;facts of this dbclass
  (index :uninitialized)
  (rule-instances (make-rule-index)))   ;;rules applicable to this dbclass

(defun dbclass-printer (cl st ig)
  (declare (ignore ig))
  (let ((count 0))
    (when (hash-table-p (dbclass-rule-instances cl))
      (maphash #'(lambda (k v)
		   (declare (ignore k))
		   (incf count (length v)))
	       (dbclass-rule-instances cl)))
    (if (> count 0)
	(format st "#<Dbclass ~A, Entries:~D, Count:~D>" (dbclass-name cl)
		(hash-table-count (dbclass-rule-instances cl)) count)
	(format st "#<Dbclass ~A>" (dbclass-name cl)))))

(defun construct-dbclass (name kb)
  (let ((instance (make-dbclass :NAME name :KB kb)))
    (setf (dbclass-index instance) (make-index instance))
    instance))

(defokbcclass primitive-db-object () ()
  (:documentation "The abstract superclass of all objects that the rule engine
     can allow."))

(defmethod tuple-store ((instance tuple-store)) instance)

(defmethod tuple-store-direct-parents ((kb tuple-store))
  (mapcar 'tuple-store
	  (get-kb-direct-parents-internal (tuple-store-kb kb))))

(defun tuple-store-precedence-list (ts)
  (let ((all nil))
    (labels ((rec (ts)
	       (when (not (member ts all :test #'eq))
		 (push ts all)
		 (loop for p in (get-kb-direct-parents-internal
				 (tuple-store-kb ts))
		       do (rec (tuple-store p))))))
      (rec ts))
    all))

(defmethod get-dbclass ((fact standard-object) (store tuple-store))
  (get-dbclass-from-hash-table fact store))

(defmethod get-dbclass ((fact standard-class) (store tuple-store))
  (get-dbclass-from-hash-table fact store))

(defmethod get-dbclass ((fact structure-object) (store tuple-store))
  (get-dbclass-from-hash-table fact store))

(defmethod get-dbclass ((fact structure-class) (store tuple-store))
  (get-dbclass-from-hash-table fact store))

(defmethod get-dbclass ((fact (eql nil)) (store tuple-store))
  (generic-error "~% NIL can't be a dbclass."))

(defmethod get-dbclass ((fact cons) (store tuple-store))
  (get-dbclass (first fact) store))

(defun get-dbclass-from-hash-table (fact store)
  (or (gethash fact (tuple-store-dbclass-table store))
      (setf (gethash fact (tuple-store-dbclass-table store))
	    (construct-dbclass fact store))))

(defmethod get-dbclass ((fact number) (store tuple-store))
  (get-dbclass-from-hash-table fact store))

(defmethod get-dbclass ((fact symbol) (store tuple-store))
  (if (variable? fact)
      (generic-error
       "Bad dbclass type: ~A.  Variables cannot be indexed." fact)
      (get-dbclass-from-hash-table fact store)))

(defmethod get-dbclass ((fact primitive-db-object) (store tuple-store))
  (get-dbclass-from-hash-table fact store))

(defmethod get-dbclass ((fact dbclass) (store tuple-store))
  fact)

(defmethod get-dbclass ((fact t) (store t))
  (generic-error
   "Bad dbclass type ~S for ~S.  If you really think that you should ~
    be able to index this fact, you should add an appropriate ~
    re::get-dbclass method to the Tuple Store class ~S."
   (ok-back:type-of-name fact) fact (ok-back:type-of-name store)))

(defun nil-is-in-tree (x)
  (typecase x
    (cons (or (nil-is-in-tree (first x))
	      (if (consp (rest x))
		  (nil-is-in-tree (rest x))
		  nil)))
    (otherwise (eq nil x))))

(defun get-all-atoms-1 (fact)
  (declare (special *all*))
  (typecase fact
    (cons (loop for f = (pop fact)
		do (get-all-atoms-1 f)
		when (not fact) return nil
		when (not (consp fact)) return (get-all-atoms-1 fact)))
    (symbol (when (and fact (not (variable? fact)))
	      (tries:pushnew-using-state fact *all*)))
    (otherwise (tries:pushnew-using-state fact *all*))))

(defun get-all-atoms (fact)
  (let ((*all* (tries:make-trie-remove-duplicate-state)))
    (declare (special *all*))
    (get-all-atoms-1 fact)
    (tries::trie-remove-duplicate-state-unique *all*)))
    
(defun make-rule-index ()
  (make-hash-table))

(defun make-index (up)
  (new-root-hybrid-trie :dbclass-index up))

(defun get-indexed (pat index)
  (get-hybrid-trie pat index))

(defun (setf get-indexed) (val pat index)
  (setf (get-hybrid-trie pat index) val))

(defun get-some-non-variable-internal (tree except)
  (declare (special *index-hint*))
  (typecase tree
    (cons (or (get-some-non-variable-internal (first tree) except)
	      (get-some-non-variable-internal (rest tree)  except)))
    (null nil)
    (symbol (if (or (variable? tree) (member tree except))
		nil
		(if (<= *index-hint* 0)
		    tree
		    (progn (decf *index-hint*) nil))))
    (otherwise (if (member tree except)
		   nil
		   (if (<= *index-hint* 0)
		       tree
		       (progn (decf *index-hint*) nil))))))

(defun get-some-non-variable (tree index-hint &optional (except nil))
  (let ((*index-hint* index-hint))
    (declare (special *index-hint*))
    (let ((result (get-some-non-variable-internal tree except)))
      (continuable-assert
       (zerop *index-hint*) () "Index hint ~D was too high!!!" index-hint)
      result)))

(defun bad-bindings-p (bindings)
  (or (eq bindings :FAIL)
      ;; JPR: We put this test in because without it,
      ;; (unify '(a ?x) '(a)) will return
      ;; ((?x)), i.e. a binding list, but an incomplete one.
      (loop for binding in bindings
	    thereis (not (rest binding)))))

(defun tuple-store-all-parents (kb &optional (top-level-call-p t) (root nil))
  (if top-level-call-p
      (let ((*visited-kbs* nil))
	(tuple-store-all-parents kb nil kb) *visited-kbs*)
      (progn (when (not (eq kb root)) (push kb *visited-kbs*))
	     (loop for prev in (tuple-store-direct-parents kb)
		   unless (or (eq prev root)
			      (member prev *visited-kbs* :test #'eq))
		   do (tuple-store-all-parents prev nil root)))))

(defun peek-for-insert (fact kb &optional (top-level-call-p t)
			     (check-included-kbs-p t))
  (macrolet ((peek-1 ()
	       '(let ((dbclass (get-dbclass fact kb)))
		 (multiple-value-bind (existing found-p trie-node)
		     (get-hybrid-trie-returning-node
		      fact (dbclass-index dbclass))
		   (values existing found-p trie-node dbclass)))))
    (if check-included-kbs-p
	(if top-level-call-p
	    (let ((*visited-kbs* nil)) (peek-for-insert fact kb nil
							check-included-kbs-p))
	    (progn (push kb *visited-kbs*)
		   (loop for prev in (tuple-store-direct-parents kb)
			 when (not (member prev *visited-kbs* :test #'eq))
			 do (multiple-value-bind
				(existing found-p trie-node dbclass)
			      (peek-for-insert fact prev nil
					       check-included-kbs-p)
			      (when found-p
				(return (values existing found-p trie-node
						dbclass))))
			 finally (return (peek-1)))))
	(peek-1))))

(defun is-full-indexed-p (hash-key kb &optional (top-level-call-p t))
  (if top-level-call-p
      (let ((*visited-kbs* nil)) (is-full-indexed-p hash-key kb nil))
      (progn (push kb *visited-kbs*)
	     (or (if (tuple-store-hash-index-p kb)
		     (multiple-value-bind
			 (val found-p)
		       (tries:get-trie
			hash-key (tuple-store-atom-to-sentence-index kb))
		       (declare (ignore val))
		       found-p)
		     (if (symbolp hash-key)
			 (fast-gethash-for-symbol
			  hash-key (tuple-store-full-index kb))
			 (gethash hash-key (tuple-store-full-index kb))))
		 (loop for prev in (tuple-store-direct-parents kb)
		       when (not (member kb *visited-kbs*))
		       do (let ((res (is-full-indexed-p
				      hash-key prev)))
			    (when res (return res))))))))

(defun forcibly-full-index-fact-in-index
    (fact full-index &optional (except nil))
  (loop for atom in (get-all-atoms fact)
	unless (member atom except)
	do (let ((hash-key (fast-hash-key atom)))
	     (let ((entry (if (or hash-key (not atom))
			      (if (symbolp hash-key)
				  (fast-gethash-for-symbol hash-key full-index)
				  (gethash hash-key full-index))
			      (generic-error "Null hash key found!!!"))))
	        (if entry
		    (progn (push fact (index-entry-facts entry))
			   (incf (index-entry-count entry))
			   (let ((subindex (index-entry-subindex entry)))
			     (when subindex
			       (forcibly-full-index-fact-in-index
				fact subindex (cons atom except)))))
		    (setf (gethash hash-key full-index)
			  (make-index-entry :facts (list fact) :count 1
					    :key-stack
					    (if except
						(cons atom except)
						atom))))))))

(defun forcibly-full-index-fact (fact kb)
  (when (tuple-store-full-index-p kb)
    (forcibly-full-index-fact-in-index fact (tuple-store-full-index kb))))

(defun facts-full-indexed-under
    (hash-key kb &optional (uniqueify-p nil) (included-kbs-p t))
  (cond ((or (tuple-store-full-index-p kb) (tuple-store-hash-index-p kb))
	 (if (and uniqueify-p (variable? hash-key))
	     (let ((state (tries:make-trie-remove-duplicate-state)))
	       (if included-kbs-p
		   (facts-full-indexed-under-internal
		    (fast-hash-key hash-key) kb t state)
		   (facts-locally-full-indexed-under hash-key kb state))
	       (tries:trie-remove-duplicate-state-unique state))
	     (let ((res (if included-kbs-p
			    (facts-full-indexed-under-internal
			     (fast-hash-key hash-key) kb)
			    (facts-locally-full-indexed-under
			     hash-key kb nil))))
	       (if uniqueify-p
		   (remove-duplicates-equal-using-trie* res)
		   (apply #'append res)))))
	(t (error "facts-full-indexed-under NYI")
	   nil)))

(defun facts-locally-full-indexed-under (hash-key kb &optional (state nil))
  (if (variable? hash-key)
      (let ((state (or state (tries:make-trie-remove-duplicate-state))))
	(if (tuple-store-hash-index-p kb)
	    ;; Map over the atom table and pluck out all the sentences.
	    (tries:maptrie-values
	     #'(lambda (trie)
		 (tries:maptrie-values
		  #'(lambda (form) (tries:pushnew-using-state form state))
		  trie))
	     (tuple-store-atom-to-sentence-index kb))
	    ;; Iterate over the dbclasses because there are fewer of them than
	    ;; index entries.
	    (maphash #'(lambda (k v)
			 (declare (ignore k))
			 (loop for form in  (dbclass-facts v)
			       do (tries:pushnew-using-state form state)))
		     (tuple-store-dbclass-table kb)))
	(tries:trie-remove-duplicate-state-unique state))
      (if (tuple-store-hash-index-p kb)
	  (multiple-value-bind (value found-p)
	    (tries:get-trie hash-key (tuple-store-atom-to-sentence-index kb))
	    (if found-p
		(let ((res nil))
		  (tries:maptrie-values #'(lambda (x) (push x res)) value)
		  res)
		nil))
	  (let ((entry
		 (if (symbolp hash-key)
		     (fast-gethash-for-symbol
		      hash-key (tuple-store-full-index kb))
		     (gethash hash-key (tuple-store-full-index kb)))))
	    (if entry
		(index-entry-facts entry)
		nil)))))

(defun facts-full-indexed-under-internal
    (hash-key kb &optional (top-level-call-p t) (state nil))
  (if top-level-call-p
      (let ((*visited-kbs* nil))
	(facts-full-indexed-under-internal hash-key kb nil state))
      (if kb
	  (cons (facts-locally-full-indexed-under hash-key kb state)
		(progn (push kb *visited-kbs*)
		       (loop for prev in (tuple-store-direct-parents kb)
			     unless (member prev *visited-kbs* :test #'eq)
			     append (facts-full-indexed-under-internal
				     hash-key prev nil state))))
	  nil)))

(defvar *register-tuple-store-side-effects-p* t)

(defmethod ok-cache:register-side-effect
     ((instance tuple-store) &optional (arg nil))
 (when (tuple-store-kb instance)
   (ok-cache:register-side-effect (tuple-store-kb instance) arg)))

(defun hash-index-peek-for-insert (key fact kb &optional (top-level-call-p t)
			     (check-included-kbs-p t))
  (when (not kb) (break))
  (if check-included-kbs-p
      (if top-level-call-p
	  (let ((*visited-kbs* nil))
	    (hash-index-peek-for-insert key fact kb nil check-included-kbs-p))
	  (progn (push kb *visited-kbs*)
		 (loop for prev in (tuple-store-direct-parents kb)
		       when (not (member prev *visited-kbs* :test #'eq))
		       do (let ((existing
				 (hash-index-peek-for-insert
				  key fact prev nil check-included-kbs-p)))
			      
			    (when existing
			      (return (values existing t))))
		       finally (return (value-is-indexed-p
					 fact (tuple-store-hash-index-p kb)
					 key)))))
      (value-is-indexed-p fact (tuple-store-hash-index-p kb) key)))

(defun insert (fact kb &optional (containing-nil-ok-p nil)
		    (check-included-kbs-p t))
  (continuable-assert fact () "Can't assert NIL.")
  (continuable-assert
   (not (and (not containing-nil-ok-p) (nil-is-in-tree fact)))
   () "Can't assert a fact containing NIL.")
  (if (tuple-store-hash-index-p kb)
      (let ((existing (hash-index-peek-for-insert
		       (pattern-hash-key fact)
		       fact kb t check-included-kbs-p)))
	(if existing
	    (values nil existing)
	    (progn (put-in-table fact
				 ;;(pattern-hash-key fact)
				 fact (tuple-store-hash-index-p kb))
		   (loop for atom in (get-all-atoms fact)
			 do (multiple-value-bind
				(val found-p node)
			      (tries:get-trie-returning-node
			       atom (tuple-store-atom-to-sentence-index kb))
			      (declare (ignore val))
			      (when (not found-p)
				(setf (tries:trie-value node) (make-trie)))
			      (setf (get-trie fact (tries:trie-value node))
				    fact)))
		   (when *register-tuple-store-side-effects-p*
		     (ok-cache:register-side-effect kb :insert))
		   (values t fact))))
      (multiple-value-bind (existing found-p trie-node dbclass)
	(peek-for-insert fact kb t check-included-kbs-p)
	(declare (ignore found-p))
	(if existing
	    (values nil existing)
	    (let ((new-struct (list fact nil)))
	      (set-hybrid-trie-value trie-node new-struct)
	      (push fact (dbclass-facts dbclass))
	      (forcibly-full-index-fact fact kb)
	      (when *register-tuple-store-side-effects-p*
		(ok-cache:register-side-effect kb :insert))
	      (values t new-struct))))))

(defun indexed-in-tuple-store-p (atom kb)
  (let ((hash-key (fast-hash-key atom)))
    (when (not (tuple-store-full-index kb))
      ;; (format t "~%;;; Forcing full index of ~A" kb)
      (maybe-post-hoc-full-index-kb kb))
    (is-full-indexed-p hash-key kb)))

(defun ensure-full-index (kb)
  (when (not (tuple-store-full-index kb))
    (setf (tuple-store-full-index kb)
	  (make-hash-table :test #'equal :size 5000))))

(defun maybe-post-hoc-full-index-kb
    (kb &optional (top-level-call-p t))
  (if (tuple-store-hash-index-p kb)
      nil
      (if top-level-call-p
	  (let ((*visited-kbs* nil))
	    (maybe-post-hoc-full-index-kb kb nil))
	  (progn (when (not (tuple-store-full-index-p kb))
		   (setf (tuple-store-full-index-p kb) t)
		   (ensure-full-index kb)
		   (maphash #'(lambda (k dbclass)
				(declare (ignore k))
				(loop for fact in (dbclass-facts dbclass)
				      do (forcibly-full-index-fact
					  fact kb)))
			    (tuple-store-dbclass-table kb)))
		 (push kb *visited-kbs*)
		 (loop for prev in (tuple-store-direct-parents kb)
		       unless (member prev *visited-kbs*)
		       do (maybe-post-hoc-full-index-kb prev nil))))))

(defun drop
    (fact kb &optional (exact-p nil) (check-included-kbs-p nil)
	  (top-level-call-p t) (safe-p nil))
  (if (and top-level-call-p check-included-kbs-p)
      (let ((*visited-kbs* nil)) (drop fact kb exact-p t nil))
      (progn
	(when (null fact) (generic-error "~% Can't drop NIL."))
	(if exact-p
	    (let ((matches (tuple-store-fetch
			    fact kb :check-included-kbs-p nil)))
	      (continuable-assert (member fact matches :test #'equal))
	      (drop-asserted-fact fact kb)
	      (when safe-p
		;; This is just a sanity check.  We can remove it when we
		;; have more confidence in dropping working OK.  JPR.
		(okbc-assert
		 (not (member fact (tuple-store-fetch
				    fact kb
				    :check-included-kbs-p nil)
			      :test #'equal))
		 () "Fact ~S not successfully droppped!" fact)))
	    (let ((matches (tuple-store-fetch
			    fact kb :check-included-kbs-p nil)))
	      (loop for match in matches
		    do (drop-asserted-fact match kb))
	      (when safe-p
		;; This is just a sanity check.  We can remove it when we
		;; have more confidence in dropping working OK.  JPR.
		(okbc-assert (not (tuple-store-fetch
				  fact kb :check-included-kbs-p nil))
			    () "Fact ~S not successfully droppped!" fact))))
	(when check-included-kbs-p
	  (push kb *visited-kbs*)
	  (loop for prev in (tuple-store-direct-parents kb)
		unless (member prev *visited-kbs* :test #'eq)
		do (drop fact prev exact-p t safe-p))))))

(defun drop-asserted-fact (fact kb)
  (when (null fact) (generic-error "~% Can't drop NIL."))
  (if (tuple-store-hash-index-p kb)
      (when (drop-fact-from-hash-index fact kb (tuple-store-hash-index-p kb))
	(when *register-tuple-store-side-effects-p*
		 (ok-cache:register-side-effect kb :drop)))
      (let ((dbclass (get-dbclass fact kb)))
	(destructuring-bind (unique-fact reference-count)
	    (or (get-indexed fact (dbclass-index dbclass))
		'(nil nil))
	  (declare (ignore reference-count))
	  (cond ((not unique-fact) (values nil :fact-not-known))
		(t (delete-hybrid-trie
		    unique-fact (dbclass-index dbclass))
		   (setf (dbclass-facts dbclass)
			 (delete unique-fact (dbclass-facts dbclass)
				 :test #'eql))
		   (when (tuple-store-full-index-p kb)
		     (drop-fact-from-full-index
		      unique-fact (tuple-store-full-index kb) nil))
		   (when *register-tuple-store-side-effects-p*
		     (ok-cache:register-side-effect kb :drop))
		   t))))))

(defun drop-fact-from-full-index (fact full-index except)
  (let ((atoms (get-all-atoms fact)))
    (loop for atom in atoms
	  for hash-key = (fast-hash-key atom)
	  for entry = (if (or hash-key (not atom))
			  (if (symbolp hash-key)
			      (fast-gethash-for-symbol hash-key full-index)
			      (gethash hash-key full-index))
			  (generic-error "Null hash-key found!!"))
	  when entry
	  do (setf (index-entry-facts entry)
		   (delete fact (index-entry-facts entry) :test #'eql))
	  (let ((subindex (index-entry-subindex entry)))
	    (when subindex
	      (drop-fact-from-full-index
	       fact subindex (cons atom except)))))))

(defun drop-fact-from-hash-index (fact kb hash-index)
  (cond ((delete-from-table fact fact hash-index)
	 (loop for atom in (get-all-atoms fact)
	       do (multiple-value-bind (val found-p)
		    (tries:get-trie
		     atom (tuple-store-atom-to-sentence-index kb))
		    (when found-p
		      (tries:delete-trie fact val))))
	 t)
	(t nil)))

(defun get-candidates (pattern kb)
  (dbclass-facts (get-dbclass pattern kb)))

(defun get-candidates-with-full-index-with-key
    (key pattern kb index-start index keys-so-far)
  (loop with current-key = key
	with shortest = nil
	with length = nil
	with best-entry = nil
	with best-key = current-key
	for count from (+ 1 index-start)
	do
	(multiple-value-bind (facts number-of-facts entry)
	    (get-candidates-with-full-index
	     current-key kb 0 index t keys-so-far)
	  ;; (print (list :******* facts number-of-facts entry))
	  (cond ((not entry) nil);; failed, so try again
		((eq :unindexed entry)
		 (return (values facts number-of-facts entry)))
		((<= number-of-facts;; heuristically 20 is ok.
		     *stop-index-search-threshold*)
		 (return (values facts number-of-facts entry)))
		;; toggle these clauses later !!!!!
		(t (when (not length)
		     (setq length number-of-facts)
		     (setq shortest facts)
		     (setq best-key current-key)
		     (setq best-entry entry))
		   (cond ((index-entry-subindex entry)
			  (multiple-value-bind
				(facts2 number-of-facts2 entry2)
			      (get-candidates-with-full-index
			       pattern kb 0 (index-entry-subindex entry) t
			       (cons current-key keys-so-far))
			    ;; (print (list :%%%%%% facts2 number-of-facts2 entry2))
			    ;; (break)
			    (if (and entry2 (not (eq t entry2)))
				(return (values facts2 number-of-facts2
						entry2))
				;; The subindex doesn't do us any good, but
				;; this may still be the best game in town.
				(progn
				  (when (or (not length)
					    (< number-of-facts length))
				    ;; (print (list :recording-best----------- facts number-of-facts entry))
				    (setq length number-of-facts)
				    (setq shortest facts)
				    (setq best-key current-key)
				    (setq best-entry entry))
				  (setq current-key (get-some-non-variable
						     pattern count
						     keys-so-far))))))
			 (t (when (or (not length)
				      (< number-of-facts length))
			      ;; (print (list :recording-best222----------- facts number-of-facts entry))
			      (setq length number-of-facts)
			      (setq shortest facts)
			      (setq best-key current-key)
			      (setq best-entry entry))
			    (setq current-key (get-some-non-variable
					       pattern count keys-so-far)))))))
	when (not current-key)
	do
	;; (print :-------no-current-key)
	(return
	  (if (progn;; (print :----) (break)
		(and length (>= length *subindex-threshold*)
		     (not (index-entry-subindex best-entry))
		     (indexable-atom-in-tree-p pattern best-key keys-so-far)))
	      ;; trigger full subindexing
	      (let ((new-keys-so-far (cons best-key keys-so-far))
		    (new-index
		     (make-hash-table :test #'equal :size 300)))
		;; (break)
		;; (format t "~%forcing subindex or for ~S given ~S" pattern new-keys-so-far)
		;; (when (rest new-keys-so-far) (break))
		(loop for fact in (index-entry-facts best-entry)
		      do;; (print (list :full-indexing-- fact))
		      (forcibly-full-index-fact-in-index
		       fact new-index new-keys-so-far))
		;; Now put it in the table.  Note, we do this after the
		;; subindex is computed just in case we blow out.
		(setf (index-entry-subindex best-entry) new-index)
		(multiple-value-bind (facts2 number-of-facts2 entry2 status2)
		    (get-candidates-with-full-index
		     pattern kb 0 new-index t new-keys-so-far)
		  (if (and entry2 (not (eq t entry2)))
		      (values facts2 number-of-facts2 entry2 status2)
		      (values shortest length best-entry))))
	      (values shortest length best-entry)))))

(defun indexable-atom-in-tree-p (tree excluding and-excluding)
  (if (consp tree)
      (loop with remainder = tree
	    for arg = (pop remainder)
	    when (indexable-atom-in-tree-p arg excluding and-excluding) return t
	    when (not remainder) return nil
	    when (not (consp remainder))
	    return (indexable-atom-in-tree-p remainder excluding and-excluding))
      (and tree
	   (if (symbolp tree)
	       (not (variable? tree))
	       t)
	   (not (fast-equal tree excluding))
	   (not (member tree and-excluding :test #'fast-equal)))))

(defun get-candidates-with-full-index
    (pattern kb index-start index recursive-p keys-so-far)
  (declare (notinline get-candidates-with-full-index))
;  (when (< (length (remove-duplicates keys-so-far)) (length keys-so-far))
;    (error "Bug here!!!!"))
  (typecase pattern
    (cons
     (let ((key (get-some-non-variable pattern index-start keys-so-far)))
       (if key
	       ;;; Search for the one with the lowest index count.
	       ;;; If we don't do this, we get screwed by systems with a
	       ;;; zillion slot values.
	   (get-candidates-with-full-index-with-key
	    key pattern kb index-start index keys-so-far)
	   (if recursive-p
	       (values nil 0 t :recursive-call-with-no-key)
		   ;;; Should only ever do this for a top-level call.
	       (get-candidates-for-literals pattern kb)))))
    (null (generic-error "Cannot have a null pattern"))
    (otherwise
     (let ((hash-key (fast-hash-key pattern)))
       (let ((entry (if (or hash-key (not pattern))
			(if (symbolp hash-key)
			    (fast-gethash-for-symbol hash-key index)
			    (gethash hash-key index))
			(generic-error "No hash key found!!"))))
	 (if entry
	     (values (index-entry-facts entry) (index-entry-count entry)
		     entry)
	     (values nil 0 :unindexed)))))))

(defun get-candidates-for-literals (pattern kb)
  (let ((candidates nil)
	(length (if (null (rest (last pattern)))
		    (length pattern)
		    ;; this is a dotted pattern
		    nil)))
    ;; do this the hard way
    ;; note: we don't have to look back at previous
    ;; kbs here.  This is handled by any callers.
    (maphash #'(lambda (key dbclass)
		 (declare (ignore key))
		 (loop for fact
		       in (dbclass-facts dbclass)
		       when (or (not length)
				(= (length
				    pattern)
				   length))
		       do (push fact candidates)))
	     (tuple-store-dbclass-table kb))
    candidates))

(defun get-candidates-maybe-with-full-index
    (pattern kb &optional (index-hint 0) (pattern-hash-key nil))
  (declare (ignore index-hint))
  (let ((hi (tuple-store-hash-index-p kb)))
    (if hi
	(get-matches pattern hi
		     (or pattern-hash-key (pattern-hash-key pattern)))
	(if (tuple-store-full-index-p kb)
	    (get-candidates-with-full-index
	     pattern kb 0 (tuple-store-full-index kb) nil nil)
	    (get-candidates pattern kb)))))

(defun tuple-store-fetch (pattern kb &key (test nil) (return-pattern pattern)
			       (index-hint 0) (check-included-kbs-p t)
			       (top-level-call-p t) (max-matches nil)
			       (uniquifying-table nil) (pattern-hash-key nil))
  "Fetch any facts matching PATTERN in KB.  The test
optional TEST function called with the pattern and a fact and should
return :fail if the fact cannot match the pattern.  Return the result
of substituting unify's bindings on the pattern."
  (if top-level-call-p
      (let ((*visited-kbs* nil)
	    (table (and check-included-kbs-p
			(make-root-trie :purpose :uniquify)))
	    (*number-to-find* (or max-matches most-positive-fixnum)))
	(let ((result (tuple-store-fetch pattern kb
					 :test test
					 :return-pattern return-pattern
					 :index-hint index-hint
					 :check-included-kbs-p
					 check-included-kbs-p
					 :top-level-call-p nil
					 :uniquifying-table table
					 :max-matches max-matches
					 :pattern-hash-key pattern-hash-key)))
	  (values (if check-included-kbs-p
		      (hybrid-trie-all-values table)
		      result)
		  (<= *number-to-find* 0))))
      (let ((local-result
	     (macrolet ((record-in-table ()
			  `(let ()
			    (multiple-value-bind (value found-p trie-node)
				(get-hybrid-trie-returning-node
				 key uniquifying-table)
			      (declare (ignore value))
			      (when (not found-p)
				(set-hybrid-trie-value trie-node key)
				(decf *number-to-find*))))))
	       (if test
		   (loop with candidates
			 = (get-candidates-maybe-with-full-index
			    pattern kb index-hint pattern-hash-key)
			 for candidate in candidates
			 for bindings
			 = (let ((res (funcall test pattern candidate)))
			     (if (eq res :fail)
				 res
				 (unify pattern candidate)))
			 for bad-bindings-p = (bad-bindings-p bindings)
			 while (> *number-to-find* 0)
			 when (and (not bad-bindings-p)
				   uniquifying-table)
			 do (let ((key (sublis bindings return-pattern)))
			      (record-in-table))
			 when (and (not bad-bindings-p)
				   (not check-included-kbs-p)
				   (not uniquifying-table))
			 collect (let ((key (sublis bindings return-pattern)))
				   (decf *number-to-find*)
				   key))
		   (loop with candidates
			 = (get-candidates-maybe-with-full-index
			    pattern kb index-hint pattern-hash-key)
			 for candidate in candidates
			 for bindings = (unify pattern candidate)
			 for bad-bindings-p = (bad-bindings-p bindings)
			 while (> *number-to-find* 0)
			 when (and (not bad-bindings-p)
				   uniquifying-table)
			 do (let ((key (sublis bindings return-pattern)))
			      (record-in-table))
			 when (and (not bad-bindings-p)
				   (not check-included-kbs-p)
				   (not uniquifying-table))
			 collect (let ((key (sublis bindings return-pattern)))
				   (decf *number-to-find*)
				   key))))))
	(if check-included-kbs-p
	    (if (consp check-included-kbs-p)
		(let ((result local-result))
		  (loop for k in check-included-kbs-p
			unless (or (eq k kb) (<= *number-to-find* 0))
			do (let ((k-result
				  (tuple-store-fetch pattern k
						     :test test
						     :return-pattern
						     return-pattern
						     :index-hint index-hint
						     :check-included-kbs-p nil
						     :top-level-call-p nil
						     :uniquifying-table
						     uniquifying-table
						     :max-matches
						     max-matches
						     :pattern-hash-key
						     pattern-hash-key)))
			     (setq result (union result k-result
						 :test #'equal))))
		  result)
		(let ((result local-result))
		  (push kb *visited-kbs*)
		  (loop for prev in (tuple-store-direct-parents kb)
			unless (or (<= *number-to-find* 0)
				   (member prev *visited-kbs* :test #'eq))
			do (let ((previous-result
				  (tuple-store-fetch pattern prev
						     :test test
						     :return-pattern
						     return-pattern
						     :index-hint index-hint
						     :check-included-kbs-p t
						     :top-level-call-p nil
						     :uniquifying-table
						     uniquifying-table
						     :max-matches
						     max-matches
						     :pattern-hash-key
						     pattern-hash-key)))
			     (setq result (union result previous-result
						 :test #'equal))))
		  result))
	    local-result))))

(defun fetch-one-binding (pattern kb &optional filter (index-hint 0)
				  (pattern-hash-key nil)
				  (check-included-kbs-p t)
				  (top-level-call-p t))
  "Similar to fetch, but return the bindings for the FIRST match or
  :fail."
  (if (and top-level-call-p check-included-kbs-p)
      (let ((*visited-kbs* nil))
	(fetch-one-binding pattern kb filter index-hint pattern-hash-key
			   check-included-kbs-p nil))
      (let ((local-result
	     (if filter
		 (loop
		  with candidates =
		  (let ((c (get-candidates-maybe-with-full-index
			    pattern kb index-hint pattern-hash-key)))
		    ;;(let ((l (length c))) (when (> l 1000) (print l))) ;;;!!!
		    c)
		  for candidate in candidates
		  for bindings = (if (not (eq (funcall filter pattern
						       candidate)
					      :fail))
				     (unify pattern candidate)
				     :fail)
		  unless (bad-bindings-p bindings) ;;; (eq bindings :FAIL)
		  return bindings
		  finally (return :fail))
		 (loop
		  for candidate
		  in (get-candidates-maybe-with-full-index
		      pattern kb index-hint pattern-hash-key)
		  for bindings = (unify pattern candidate)
		  unless (bad-bindings-p bindings) ;;; (eq bindings :FAIL)
		  return bindings
		  finally (return :fail)))))
	(if check-included-kbs-p
	    (if (eq local-result :fail)
		(if (consp check-included-kbs-p)
		    (loop for k in check-included-kbs-p
			  unless (eq k kb)
			  do (let ((res (fetch-one-binding
					 pattern k filter index-hint
					 pattern-hash-key nil nil)))
			       (when (not (eq res :fail))
				 (return res)))
			  finally (return local-result))
		    (progn (push kb *visited-kbs*)
			   (loop for prev in (tuple-store-direct-parents kb)
				 unless (member prev *visited-kbs* :test #'eq)
				 do (let ((res (fetch-one-binding
						pattern prev filter index-hint
						pattern-hash-key t nil)))
				      (when (not (eq res :fail))
					(return res)))
				 finally (return local-result))))
		local-result)
	    local-result))))

(defun at-least-one-binding-available-p
    (pattern kb &optional filter (index-hint 0) (check-included-kbs-p t))
  (let ((result (fetch-one-bindingm pattern kb filter index-hint
				    check-included-kbs-p)))
    (not (eq result :fail))))


;=============================================================================

;;; Hash index type of indexing.....
;;; By AXF taken from ATP.

(defvar *hash-index-table-size* 5000)

(defstruct hash-index
  (table (make-hash-table :size *hash-index-table-size*
			  :rehash-size 5.0
                          #+lucid :use-cache #+lucid t
			  :test #+lucid #'eq #-lucid #'eql))
  kb 
  name)

(defmethod print-object ((x hash-index) (s t))
 (call-next-method))

(defun clear-hash-index (fi)
  (clrhash (hash-index-table fi))
  fi)


(eval-when (compile load eval)
  (defconstant +var-hash-key+ (sxhash '+var-hash-key+))
  (defconstant +null-hash-key+ (sxhash '+null-hash-key+)))

(eval-when (compile load eval)
  ;; A bit of lucid-specific magic.  The lucid::set-%symbol-sxhash form
  ;; is defined as a compiler macro that only exists when we are in the
  ;; production compiler, but we still want things to work when we're using
  ;; the development compiler.  Thus, we eval the form and compile it with
  ;; production compiler switched on by binding.  Note that just having
  ;; the declaration in the function dooesn't do the trick to force it
  ;; into production mode for this one function.
  (progn (eval '(defun fkey (pat)
		 "Return a numeric key for a patter sexpr (perhaps containing
                  vars)."
		 (declare (optimize (speed 3) (safety 0)))
		 (cond
		   ((consp pat)
		    (fkey (first pat)))
		   #-Lucid
		   ((ok-utils:variable? pat) +var-hash-key+)
		   #+Lucid
		   ((symbolp pat)
		    (if (let ((sn (symbol-name pat)))
			  (and (> (length (the simple-string sn)) 0)
			       (char= #\? (schar sn 0))))
			+var-hash-key+
			(lucid::%symbol-sxhash pat)))
		   (t (let ((key1 (ok-utils:fast-hash-key pat)))
			(if #+Lucid (symbolp key1)
			    #-Lucid nil
			    #+Lucid
			    (lucid::%symbol-sxhash key1)
			    #-Lucid (error "Should never get here in fkey!")
			    (let ((hash-key (sxhash (the atom key1))))
			      (declare (fixnum hash-key))
			      ;; (logxor <> (ldb (byte 16 17) hash-key))
			      (ldb (byte 16 0) hash-key))))))))
	 (let (#+Lucid (lucid:*use-sfc* nil))
	   (compile 'fkey))))

;;; We would like to do this by displacing a word array over a byte
;;; array, but neither HCL, nor EXCL seem to do the right thing, even though
;;; Lucid does.
(defparameter *okbc-hash-index-hash-buffer-char*
  (make-array 20 :element-type `(unsigned-byte 8)))

(defun set-bytes-in-array (array offset from-int)
  (loop for i from 0 below 4
	do (setf (aref array (+ offset i))
		 (logand (ash from-int (- (* i 8))) #xFF)))
  array)

#+Lucid
(defparameter *okbc-hash-index-hash-buffer-8bit*
  (make-array 10  :element-type `(unsigned-byte 8)))
#+Lucid
(defparameter *okbc-hash-index-hash-buffer-16bit*
  (make-array 5 :element-type `(unsigned-byte 16)
	      :displaced-to *okbc-hash-index-hash-buffer-8bit*))
	      
;;lucid::%symbol-sxhash
;; the bottleneck on assert is aref.  Might be faster with just the
;; 8bit array.

(defun hash4 (mask k0 k1 k2 k3 len)
  (declare (fixnum mask k0 k1 k2 k3 len))
  #+Lucid
  (locally
      (declare (type (array (unsigned-byte 16) 1)
		     *okbc-hash-index-hash-buffer-16bit*))
    (setf (aref *okbc-hash-index-hash-buffer-16bit* 0)
	  (if (logbitp 0 mask) k0 +var-hash-key+))
    (setf (aref *okbc-hash-index-hash-buffer-16bit* 1)
	  (if (logbitp 1 mask) k1 +var-hash-key+))
    (setf (aref *okbc-hash-index-hash-buffer-16bit* 2)
	  (if (logbitp 2 mask) k2 +var-hash-key+))
    (setf (aref *okbc-hash-index-hash-buffer-16bit* 3)
	  (if (logbitp 3 mask) k3 +var-hash-key+))
    (setf (aref *okbc-hash-index-hash-buffer-16bit* 4) len)
    (lucid::crc-8bit *okbc-hash-index-hash-buffer-8bit* 0 10))
  #-lucid
  (locally
      (declare (type (array (unsigned-byte 8) 1)
		     *okbc-hash-index-hash-buffer-char*))
    (set-bytes-in-array *okbc-hash-index-hash-buffer-char* 0
			(if (logbitp 0 mask) k0 +var-hash-key+))
    (set-bytes-in-array *okbc-hash-index-hash-buffer-char* 1
			(if (logbitp 1 mask) k1 +var-hash-key+))
    (set-bytes-in-array *okbc-hash-index-hash-buffer-char* 2
			(if (logbitp 2 mask) k2 +var-hash-key+))
    (set-bytes-in-array *okbc-hash-index-hash-buffer-char* 3
			(if (logbitp 3 mask) k3 +var-hash-key+))
    (set-bytes-in-array *okbc-hash-index-hash-buffer-char* 4 len)
    (loop with modulus = 7514797
	  with hash = 0
	  for i from 0 below (length *okbc-hash-index-hash-buffer-char*)
	  for char = (aref *okbc-hash-index-hash-buffer-char* i)
	  do (setq hash (mod (+ (ash hash 8) char) modulus))
           ;;;(print (list i (aref *okbc-hash-index-hash-buffer-char* i)))
	  finally (return hash))))
  

(defun pattern-hash-key (pat)
  (declare (cons pat))
  (let ((list pat)
	(len (length pat)))
    (hash4 (1- (min 16 (the fixnum (expt 2 len))))
	   (fkey (pop list))
	   (if list (fkey (pop list)) +null-hash-key+)
	   (if list (fkey (pop list)) +null-hash-key+)
	   (if list (fkey (pop list)) +null-hash-key+)
	   len)))

(defun get-matches (pat ft &optional (key (pattern-hash-key pat)))
  ;(break "Looking for ~s" pat)
  (queue-contents
   (gethash
    (the fixnum key)
    (the hash-table (hash-index-table ft)))))

(defun value-is-indexed-p (val ft &optional (key-int nil))
  (if key-int
      (first (member val (queue-contents
			  (gethash key-int (hash-index-table ft)))
		     :test #'equal))
      (let ((list val))
	(let ((k0 (fkey (pop list)))
	      (k1 (if list (fkey (pop list)) +null-hash-key+))
	      (k2 (if list (fkey (pop list)) +null-hash-key+))
	      (k3 (if list (fkey (pop list)) +null-hash-key+))
	      (len (length key-int)))
	  (let ((max (min 16 (the fixnum (expt 2 len)))))
	    (first (member val (queue-contents
				(gethash (hash4 (1- max) k0 k1 k2 k3 len)
					 (hash-index-table ft)))
			   :test #'equal)))))))

(defun put-in-table (key val ft)
  (declare (cons key))
  (let ((list key))
    (let ((k0 (fkey (pop list)))
	  (k1 (if list (fkey (pop list)) +null-hash-key+))
	  (k2 (if list (fkey (pop list)) +null-hash-key+))
	  (k3 (if list (fkey (pop list)) +null-hash-key+))
	  (len (length key)))
      (let ((max (min 16 (the fixnum (expt 2 len)))))
	(unless
	    (member val
		    (queue-contents
		     (gethash (hash4 (1- max) k0 k1 k2 k3 len)
			      (hash-index-table ft)))
		    :test #'equal)
	  (loop
	   with ht = (hash-index-table ft)
	   for mask below max
	   for hash-key = (hash4 mask k0 k1 k2 k3 len)
	   do
	   ;;(format t "~&offset=~s, key=~s~%" mask key)
	   (let ((q (gethash (the fixnum hash-key) (the hash-table ht))))
	     (if q
		 (enqueue val q)
		 (setf (gethash (the fixnum hash-key) (the hash-table ht))
		       (enqueue val (make-queue))))))
	  val)))))

(defun delete-from-table (pat item ft)
  (declare (cons pat))
  (when
      (setq item (first (member item (get-matches pat ft)
				:test #'equal)))
    (let ((list pat))
      (let ((k0 (fkey (pop list)))
	    (k1 (if list (fkey (pop list)) +null-hash-key+))
	    (k2 (if list (fkey (pop list)) +null-hash-key+))
	    (k3 (if list (fkey (pop list)) +null-hash-key+))
	    (len (length pat)))
	(let ((max (min 16 (the fixnum (expt 2 len)))))
	  (loop
	   for mask below max
	   for key = (hash4 mask k0 k1 k2 k3 len)
	   do
	   ;;(format t "~&mask=~s, key=~s~%" mask key)
	   (let ((q (gethash key (hash-index-table ft))))
	     (when q
	       (queue-delete q item))))))
      t)))

