(in-package :okbc-test)


;;;  To execute the test suite with Loom, eval  (test 'loom-kb)
;;;  (this of course requires that you have Loom loaded).

(defvar *all-frames* nil)

(defun appropriate-root-classes (&key kb)
  (declare (ignore kb))
  nil)

(defun test (kb-class &key
		      (initargs nil)
		      silent
      		      (copy t)
		      (tell-and-ask t)
		      (creator nil))
  "Runs a suite of tests on a new kb of type <code>kb-class</code> using
:initargs. If :copy is true, then attempts to copy from the kb into a
<code>ok-back:tuple-kb</code> (called <code>test-target-kb</code>).  If
<code>tell-and-ask</code> is true, then the tests will
then create another KB of the <code>kb-class</code> and test the tell&ask
interface as well.  The <code>creator</code> may be a function of one
argument, a kb-name, that should return an new kb of the type that is to be
tested.  This is useful for testing non-standard kbs."
  ;; Cleanup from previous call
  (let ((*package* (find-package :okbc-test)))
    ;; We bind *package* just in case there are any KBs that have the
    ;; frame names required behavior and that are sensitive to the
    ;; current package when configuring their IO environment.
    (let ((existing
	   (find-kb-of-type 'taxa :kb-type (get-kb-type kb-class))))
      (when existing 
	(close-kb :kb existing)))
    (let ((existing
	   (find-kb-of-type 'tell-and-ask :kb-type (get-kb-type kb-class))))
      (when existing 
	(close-kb :kb existing)))
    (loop for frame in *all-frames* do (makunbound frame))
  
    (test-kb
     (if creator
	 (funcall creator 'taxa)
	 (create-kb 'taxa
		    :kb-type (get-kb-type kb-class)
		    :initargs initargs))
     silent
     (when copy
       (make-instance 'ok-back:tuple-kb :name 'test-target-kb))
     (when tell-and-ask
       (if creator
	   (funcall creator 'tell-and-ask)
	   (create-kb 'tell-and-ask
		      :kb-type (get-kb-type kb-class)
		      :initargs initargs))))))


(defmacro defframe (name)
  `(progn (pushnew ',name *all-frames*)
    (defvar ,name)))

(defframe $living-thing)
(defframe $animal)
(defframe $plant)
(defframe $mammal)
(defframe $reptile)
(defframe $fish)
(defframe $grass)
(defframe $tree)
(defframe $palm)
(defframe $food)
(defframe $tiger)
(defframe $bird)
(defframe $human)
(defframe $elephant)
(defframe $lizard)
(defframe $dinosaur)
(defframe $salmon)
(defframe $trout)

(defframe $ted)
(defframe $bill)
(defframe $harry)
(defframe $edward)
(defframe $linda)
(defframe $derek)

(defframe $foods)
(defframe $has-tail)


(defframe $sally)
(defframe $trudy)
(defframe $something-edible)
(defframe $seeds)
(defframe $berries)
(defframe $fries)
(defframe $chips)
(defframe $default-food-for-animals)
(defframe $default-food-for-mammals)

(defframe $color)
(defframe $age)
(defframe $has-leaves)

(defframe $thing)
(defframe $number)
(defframe $integer)
(defframe $string)
(defframe $symbol)
(defframe $list)

(defframe $documentation)
(defframe $domain)
(defframe $slot-value-type)
(defframe $slot-inverse)
(defframe $slot-cardinality)
(defframe $slot-maximum-cardinality)
(defframe $slot-minimum-cardinality)
(defframe $slot-same-values)
(defframe $slot-not-same-values)
(defframe $slot-subset-of-values)
(defframe $slot-numeric-minimum)
(defframe $slot-numeric-maximum)
(defframe $slot-some-values)
(defframe $slot-collection-type)

(defframe $value-type)
(defframe $inverse)
(defframe $cardinality)
(defframe $maximum-cardinality)
(defframe $minimum-cardinality)
(defframe $same-values)
(defframe $not-same-values)
(defframe $subset-of-values)
(defframe $numeric-minimum)
(defframe $numeric-maximum)
(defframe $some-values)
(defframe $collection-type)

(defframe $single-valued)
(defframe $silly-facet)

(defun test-kb (kb silent &optional (new-kb nil) (ask-kb nil))
  "Runs the test suite on a particular KB.  If <code>silent</code> is
   true, it supresses output.  If <code>new-kb</code> is provided, the
   KB copying tests will be run.  If <code>ask-kb</code> is provided, the
   tell&ask tests will be run."
  (goto-kb kb)
  (create-classes silent)
  (create-individuals silent)
  (test-keywordified-frames silent)
  ;; (test-keywordified-slots silent)
  (test-frame-ops silent)
  (test-class-instance-relationships silent)
  (test-slot-attachment silent)
  (test-slot-values silent)
  (when (member :user-defined-facets (get-behavior-values :compliance))
    (test-facet-attachment silent)
    (test-facets kb silent))
  (test-constraints kb silent)
  (test-coerce-to-kb-value silent)
  (test-procedures kb silent)
  (test-cache-management silent)
  (test-get-frames-with-slot-or-facet-value kb silent)
  (when new-kb (test-copy-kb kb new-kb silent))
  (when ask-kb (test-tell-and-ask ask-kb (not silent))))

(defun reified-slots-p  () (member :slot  (get-behavior-values :are-frames)))
(defun reified-facets-p () (member :facet (get-behavior-values :are-frames)))

(defun get-unique-frame (symbol &optional (kb (current-kb)))
  (assert (symbolp symbol))
  (or (first (get-frames-matching symbol :wildcards-allowed-p nil :kb kb
				  :kb-local-only-p t))
      (error 'not-coercible-to-frame :frame symbol :kb kb)))

(defun create-pretty-frame (name &rest args)
  (apply 'create-frame name
	 (append args (list :pretty-name (string-capitalize name)))))

(defun create-pretty-class (name &rest args)
  (apply 'create-class name
	 (append args (list :pretty-name (string-capitalize name)))))

(defun create-pretty-slot (name &rest args)
  (apply 'create-slot name
	 (append args (list :pretty-name (string-capitalize name)))))

(defun create-pretty-facet (name &rest args)
  (apply 'create-facet name
	 (append args (list :pretty-name (string-capitalize name)))))

(defun create-pretty-individual (name &rest args)
  (apply 'create-individual name
	 (append args (list :pretty-name (string-capitalize name)))))

(defun create-classes (silent)
  (unless silent (format t "~%::: Creating classes~%"))
  (setq $living-thing
	(create-pretty-frame
	 'living-thing :class :direct-superclasses
	 ;; Note:  OR necessary because the KB might have no root
	 ;; classes and you must supply :class to force the frame
	 ;; to be a class.
	 (appropriate-root-classes :kb (current-kb))))
  (setq $animal
	(create-pretty-frame 'animal :class :direct-superclasses $living-thing
			     :template-slots
			     '((color) (age) (foods) (has-tail))))
  (cond ((reified-slots-p)
	 (setq $color (get-unique-frame 'color))
	 (setq $age (get-unique-frame 'age))
	 (setq $foods (get-unique-frame 'foods))
	 (setq $has-tail (get-unique-frame 'has-tail)))
	(t (setq $color 'color)
	   (setq $age 'age)
	   (setq $foods 'foods)
	   (setq $has-tail 'has-tail)))
  (setq $plant
	(create-pretty-frame 'plant :class :direct-superclasses $living-thing
			     :template-slots `((,$color) (has-leaves))))

  (cond ((reified-slots-p)
	 (setq $has-leaves (get-unique-frame 'has-leaves)))
	(t (setq $has-leaves 'has-leaves)))
  (setq $mammal
	(create-pretty-frame 'mammal :class :direct-superclasses $animal))
  (setq $reptile
	(create-pretty-frame 'reptile :class :direct-superclasses $animal))
  (setq $fish (create-pretty-frame 'fish :class :direct-superclasses $animal))
  (setq $grass (create-pretty-frame 'grass :class :direct-superclasses $plant))
  (setq $tree (create-pretty-frame 'tree :class :direct-superclasses $plant))
  (setq $palm (create-pretty-frame 'palm :class :direct-superclasses $tree))
  (setq $food
	(create-pretty-class 'food :direct-superclasses
			     (appropriate-root-classes :kb (current-kb))))
  (setq $tiger (create-pretty-class 'tiger :direct-superclasses $mammal))
  (setq $bird (create-pretty-class 'bird :direct-superclasses $animal))
  (setq $human (create-pretty-class 'human :direct-superclasses $mammal))
  (setq $elephant (create-pretty-class 'elephant :direct-superclasses $mammal))
  (setq $lizard (create-pretty-class 'lizard :direct-superclasses $reptile))
  (setq $dinosaur
	(create-pretty-class 'dinosaur :direct-superclasses $reptile))
  (setq $salmon (create-pretty-class 'salmon :direct-superclasses $fish))
  (setq $trout (create-pretty-class 'trout :direct-superclasses $fish)))


(defun create-individuals (silent)
  (unless silent
    (format t "~%::: Creating individuals~%"))
  (setq $ted (create-pretty-individual 'ted :direct-types $tiger))
  (setq $bill (create-pretty-individual 'bill :direct-types $bird))
  (setq $harry (create-pretty-individual 'harry :direct-types $human))
  (setq $edward (create-pretty-individual 'edward :direct-types $elephant))
  (setq $linda (create-pretty-individual 'linda :direct-types $lizard))
  (setq $derek (create-pretty-individual 'derek :direct-types $dinosaur))
  (setq $sally (create-pretty-individual 'sally :direct-types $salmon))
  (setq $trudy (create-pretty-individual 'trudy :direct-types $trout))
  (setq $something-edible
	(create-pretty-individual 'something-edible :direct-types $food))
  (setq $seeds (create-pretty-individual 'seeds :direct-types $food))
  (setq $berries (create-pretty-individual 'berries :direct-types $food))
  (setq $fries (create-pretty-individual 'fries :direct-types $food))
  (setq $chips (create-pretty-individual 'chips :direct-types $food))
  (setq $default-food-for-animals
	(create-pretty-individual
	 'default-food-for-animals :direct-types $food))
  (setq $default-food-for-mammals
	(create-pretty-individual
	 'default-food-for-mammals :direct-types $food)))

(defun test-keywordified-frames (silent)
  (unless silent (format t "~%::: Testing keywordified frames~%"))
  (loop for name in ok-back:*okbc-standard-names*
	unless (member name ok-back:*kif-meta-extension-symbols*)
	do (test-name-of-standard-frame name (current-kb))))

(defun test-name-of-standard-frame (name kb)
  (setf (symbol-value (intern (concatenate 'string "$" (symbol-name name))
			      :okbc-test))
	(cond ((coercible-to-frame-p name :kb kb)
	       (true? (list 'get-frame-name name))
	       (cond ((or (member name
				  ok-back:*okbc-standard-class-names*)
			  (member name
				  ok-back:*okbc-class-relation-symbols*))
		      (true? (list 'class-p name :kb kb)))
		     ((member name ok-back:*okbc-standard-slot-names*)
		      (true? (list 'slot-p name :kb kb)))
		     ((member name ok-back:*okbc-standard-facet-names*)
		      (true? (list 'facet-p name :kb kb)))
		     (t (error "Should never get here")))
	       (coerce-to-frame name :kb kb))
	      (t nil))))

;;**af change ,$tiger to $tiger, etc.
(defun test-frame-ops (silent)
  (unless silent (format t "~%::: Testing frame coersion, naming~%")) 
  (true? `(coercible-to-frame-p $tiger))
  (true? `(coercible-to-frame-p $ted))
  (true? `(coercible-to-frame-p (coerce-to-frame $ted)))
  (cond ((remove nil (get-behavior-values :frame-names-required))
	 (equal? 'ted `(get-frame-name (coerce-to-frame $ted))))
	(t nil)))

(defun test-class-instance-relationships (silent)
  (unless silent
    (format t "~%::: Testing relationships among classes and instances~%"))
  (true? `(class-p ,$tiger))
  (false? `(class-p ,$ted))
  (equal-sets? (list $grass $tree)
	       `(get-class-subclasses ,$plant :inference-level :direct))
  (equal-sets? (list $grass $tree $palm) `(get-class-subclasses ,$plant))
  (equal-sets? (list $ted)
	       `(get-class-instances ,$tiger :inference-level :direct))
  (equal-sets? `() `(get-class-instances ,$animal :inference-level :direct))
  (equal-sets? (list $ted $harry $edward) `(get-class-instances ,$mammal))
  (equal-sets? (list $animal)
	       `(get-class-superclasses ,$mammal :inference-level :direct))
  (true? `(subclass-of-p ,$lizard ,$animal))
  (true? `(instance-of-p ,$sally ,$animal))
  (true?  `(individual-p ,$derek))
  (false? `(individual-p ,$lizard))
  (let ((frames
	 (list $ted $bill $harry $edward $linda $derek $sally $trudy
	       $something-edible $seeds $berries $fries $chips
	       $default-food-for-animals $default-food-for-mammals)))
    ;; if we have slot frames then $foods, etc. will come out as a frame.
    (subsets? (if (reified-slots-p)
		     (append (list $has-tail $has-leaves $color $age $foods)
			     frames)
		     frames)
	      `(get-kb-individuals :kb-local-only-p t)))
  (subsets? (list $lizard)
	       `(get-instance-types ,$linda :inference-level :direct))
  (true? `(instance-of-p ,$linda ,$reptile)))


(defun test-slot-attachment (silent)
  (unless silent (format t "~%::: Testing slot attachment~%"))
  (equal-sets? (list $color $age $foods $has-tail)
	       `(get-frame-slots ,$animal :slot-type :template))
  (subsets? (list $color $age $foods $has-tail)
	       `(get-frame-slots ,$bill :slot-type :own))
  (attach-slot $bill $has-leaves :slot-type :own)
  (subsets? (list $color $age $foods $has-tail $has-leaves)
	       `(get-frame-slots ,$bill :slot-type :own))
  (detach-slot $bill $has-leaves :slot-type :own)
  (subsets? (list $color $age $foods $has-tail)
	       `(get-frame-slots ,$bill :slot-type :own)))


(defun test-slot-values (silent)
  (unless silent
    (format t "~%::: Testing get, put, add, and remove of slot values~%"))
  (equal-sets? `() `(get-slot-values ,$bill ,$foods))
  (put-slot-value $bill $foods $seeds)
  (equal? :own `(get-slot-type ,$bill ,$foods))
  (equal-sets? (list $seeds) `(get-slot-values ,$bill ,$foods))
  (put-slot-value $mammal $foods $something-edible :slot-type :template)
  (equal-sets? (list $seeds) `(get-slot-values ,$bill ,$foods))
  (put-slot-values $harry $foods (list $fries $chips))
  (equal-sets? (list $fries $chips)
	       `(get-slot-values ,$harry ,$foods :inference-level :direct))
  (equal-sets? (list $fries $chips $something-edible)
	       `(get-slot-values ,$harry ,$foods))
  (add-slot-value $bill $foods $berries)
  (equal-sets? (list $seeds $berries) `(get-slot-values ,$bill ,$foods))
  (remove-slot-value $bill $foods $seeds)
  (equal-sets? (list $berries)
	       `(get-slot-values ,$bill ,$foods :inference-level :direct))
  (equal-sets? (list $berries) `(get-slot-values ,$bill ,$foods))
  (when (get-behavior-values :defaults)
  (put-slot-value $animal $foods $default-food-for-animals 
		  :slot-type :template :value-selector :default-only)
  (print :1)
  (equal-sets? (list $default-food-for-animals)
	       `(get-slot-values ,$animal ,$foods :slot-type :template 
				 :value-selector :default-only
				 :inference-level :direct))
  (print :1b)
  (equal-sets? nil
	       `(get-slot-values ,$animal ,$foods :slot-type :template 
				 :value-selector :known-true
				 :inference-level :direct))
  (print :1c)
  (equal-sets? (list $default-food-for-animals)
	       `(get-slot-values ,$animal ,$foods :slot-type :template 
				 :value-selector :either
				 :inference-level :direct))
  (print :2)
  (equal-sets? (list $default-food-for-animals)
	       `(get-slot-values ,$animal ,$foods :slot-type :template 
				 :value-selector :default-only
				 :inference-level :taxonomic))
  (print :2b)
  (equal-sets? nil
	       `(get-slot-values ,$animal ,$foods :slot-type :template 
				 :value-selector :known-true
				 :inference-level :taxonomic))
  (print :2c)
  (equal-sets? (list $default-food-for-animals)
	       `(get-slot-values ,$animal ,$foods :slot-type :template 
				 :value-selector :either
				 :inference-level :taxonomic))

  (remove-slot-value $mammal $foods $something-edible :slot-type :template)

  (print :3)
  (equal-sets? nil
	       `(get-slot-values ,$mammal ,$foods :slot-type :template 
				 :value-selector :default-only
				 :inference-level :direct))
  (print :3b)
  (equal-sets? nil
	       `(get-slot-values ,$mammal ,$foods :slot-type :template 
				 :value-selector :known-true
				 :inference-level :direct))
  (print :3c)
  (equal-sets? nil
	       `(get-slot-values ,$mammal ,$foods :slot-type :template 
				 :value-selector :either
				 :inference-level :direct))
  (print :4)
  (equal-sets? (list $default-food-for-animals)
	       `(get-slot-values ,$mammal ,$foods :slot-type :template 
				 :value-selector :default-only
				 :inference-level :taxonomic))
  (print :4b)
  (equal-sets? nil
	       `(get-slot-values ,$mammal ,$foods :slot-type :template 
				 :value-selector :known-true
				 :inference-level :taxonomic))
  (print :4c)
  (equal-sets? (list $default-food-for-animals)
	       `(get-slot-values ,$mammal ,$foods :slot-type :template 
				 :value-selector :either
				 :inference-level :taxonomic))

  (put-slot-value $animal $foods $something-edible :slot-type :template)

  (print :4d)
  (equal-sets? (list $default-food-for-animals)
	       `(get-slot-values ,$mammal ,$foods :slot-type :template 
				 :value-selector :default-only
				 :inference-level :taxonomic))
  (print :4e)
  (equal-sets? (list $something-edible)
	       `(get-slot-values ,$mammal ,$foods :slot-type :template 
				 :value-selector :known-true
				 :inference-level :taxonomic))
  (print :4f)
  (equal-sets? (list $something-edible)
	       `(get-slot-values ,$mammal ,$foods :slot-type :template 
				 :value-selector :either
				 :inference-level :taxonomic))

  (remove-slot-value $animal $foods $something-edible :slot-type :template)

  (print :4g)
  (equal-sets? (list $default-food-for-animals)
	       `(get-slot-values ,$mammal ,$foods :slot-type :template 
				 :value-selector :default-only
				 :inference-level :taxonomic))
  (print :4h)
  (equal-sets? nil
	       `(get-slot-values ,$mammal ,$foods :slot-type :template 
				 :value-selector :known-true
				 :inference-level :taxonomic))
  (print :4i)
  (equal-sets? (list $default-food-for-animals)
	       `(get-slot-values ,$mammal ,$foods :slot-type :template 
				 :value-selector :either
				 :inference-level :taxonomic))


  
  (print :5)
  (equal-sets? nil
	       `(get-slot-values ,$human ,$foods :slot-type :template 
				 :value-selector :default-only
				 :inference-level :direct))
  (print :5b)
  (equal-sets? nil
	       `(get-slot-values ,$human ,$foods :slot-type :template 
				 :value-selector :known-true
				 :inference-level :direct))
  (print :5c)
  (equal-sets? nil
	       `(get-slot-values ,$human ,$foods :slot-type :template 
				 :value-selector :either
				 :inference-level :direct))
  (print :6)
  (equal-sets? (list $default-food-for-animals)
	       `(get-slot-values ,$human ,$foods :slot-type :template 
				 :value-selector :default-only
				 :inference-level :taxonomic))
  (print :6b)
  (equal-sets? nil
	       `(get-slot-values ,$human ,$foods :slot-type :template 
				 :value-selector :known-true
				 :inference-level :taxonomic))
  (print :6c)
  (equal-sets? (list $default-food-for-animals)
	       `(get-slot-values ,$human ,$foods :slot-type :template 
				 :value-selector :either
				 :inference-level :taxonomic))
  (print :7)
  (equal-sets? nil
	       `(get-slot-values ,$harry ,$foods :slot-type :own
				 :value-selector :default-only
				 :inference-level :direct))
  (print :7b)
  (equal-sets? (list $chips $fries)
	       `(get-slot-values ,$harry ,$foods :slot-type :own
				 :value-selector :known-true
				 :inference-level :direct))
  (print :7c)
  (equal-sets? (list $chips $fries)
	       `(get-slot-values ,$harry ,$foods :slot-type :own
				 :value-selector :either
				 :inference-level :direct))
  (print :8)
  (equal-sets? (list $default-food-for-animals)
	       `(get-slot-values ,$harry ,$foods :slot-type :own
				 :value-selector :default-only
				 :inference-level :taxonomic))
  (print :8b)
  (equal-sets? (list $chips $fries)
	       `(get-slot-values ,$harry ,$foods :slot-type :own
				 :value-selector :known-true
				 :inference-level :taxonomic))
  (print :8c)
  (equal-sets? (list $chips $fries)
	       `(get-slot-values ,$harry ,$foods :slot-type :own
				 :value-selector :either
				 :inference-level :taxonomic))
  

  (remove-slot-value $harry $foods $chips)
  (remove-slot-value $harry $foods $fries)

  (print :8d)
  (equal-sets? (list $default-food-for-animals)
	       `(get-slot-values ,$harry ,$foods :slot-type :own
				 :value-selector :either
				 :inference-level :taxonomic))




  (put-slot-value $mammal $foods $default-food-for-mammals
		  :slot-type :template :value-selector :default-only)
  (print :9)
  (equal-sets? (list $default-food-for-animals)
	       `(get-slot-values ,$animal ,$foods :slot-type :template 
				 :value-selector :default-only
				 :inference-level :direct))
  (print :9b)
  (equal-sets? nil
	       `(get-slot-values ,$animal ,$foods :slot-type :template 
				 :value-selector :known-true
				 :inference-level :direct))
  (print :9c)
  (equal-sets? (list $default-food-for-animals)
	       `(get-slot-values ,$animal ,$foods :slot-type :template 
				 :value-selector :either
				 :inference-level :direct))
  (print :10)
  (equal-sets? (list $default-food-for-animals)
	       `(get-slot-values ,$animal ,$foods :slot-type :template 
				 :value-selector :default-only
				 :inference-level :taxonomic))
  (print :10b)
  (equal-sets? nil
	       `(get-slot-values ,$animal ,$foods :slot-type :template 
				 :value-selector :known-true
				 :inference-level :taxonomic))
  (print :10c)
  (equal-sets? (list $default-food-for-animals)
	       `(get-slot-values ,$animal ,$foods :slot-type :template 
				 :value-selector :either
				 :inference-level :taxonomic))
  (print :11)
  (equal-sets? (list $default-food-for-mammals)
	       `(get-slot-values ,$mammal ,$foods :slot-type :template 
				 :value-selector :default-only
				 :inference-level :direct))
  (print :11b)
  (equal-sets? nil
	       `(get-slot-values ,$mammal ,$foods :slot-type :template 
				 :value-selector :known-true
				 :inference-level :direct))
  (print :11c)
  (equal-sets? (list $default-food-for-mammals)
	       `(get-slot-values ,$mammal ,$foods :slot-type :template 
				 :value-selector :either
				 :inference-level :direct))
  (print :12)
  (equal-sets? (list $default-food-for-mammals)
	       `(get-slot-values ,$mammal ,$foods :slot-type :template 
				 :value-selector :default-only
				 :inference-level :taxonomic))
  (print :12b)
  (equal-sets? nil
	       `(get-slot-values ,$mammal ,$foods :slot-type :template 
				 :value-selector :known-true
				 :inference-level :taxonomic))
  (print :12c)
  (equal-sets? (list $default-food-for-mammals)
	       `(get-slot-values ,$mammal ,$foods :slot-type :template 
				 :value-selector :either
				 :inference-level :taxonomic))
  (print :13)
  (equal-sets? (list $default-food-for-mammals)
	       `(get-slot-values ,$human ,$foods :slot-type :template 
				 :value-selector :default-only
				 :inference-level :taxonomic))
  (print :13b)
  (equal-sets? nil
	       `(get-slot-values ,$human ,$foods :slot-type :template 
				 :value-selector :known-true
				 :inference-level :taxonomic))
  (print :13c)
  (equal-sets? (list $default-food-for-mammals)
	       `(get-slot-values ,$human ,$foods :slot-type :template 
				 :value-selector :either
				 :inference-level :taxonomic))
  (print :14)
  (equal-sets? nil
	       `(get-slot-values ,$harry ,$foods :slot-type :own
				 :value-selector :default-only
				 :inference-level :direct))
  (print :14b)
  (equal-sets? nil
	       `(get-slot-values ,$harry ,$foods :slot-type :own
				 :value-selector :known-true
				 :inference-level :direct))
  (print :14c)
  (equal-sets? nil
	       `(get-slot-values ,$harry ,$foods :slot-type :own
				 :value-selector :either
				 :inference-level :direct))
  (print :15)
  (equal-sets? (list $default-food-for-mammals)
	       `(get-slot-values ,$harry ,$foods :slot-type :own
				 :value-selector :default-only
				 :inference-level :taxonomic))
  (print :15b)
  (equal-sets? nil
	       `(get-slot-values ,$harry ,$foods :slot-type :own
				 :value-selector :known-true
				 :inference-level :taxonomic))
  (print :15c)
  (equal-sets? (list $default-food-for-mammals)
	       `(get-slot-values ,$harry ,$foods :slot-type :own
				 :value-selector :either
				 :inference-level :taxonomic))

  (remove-slot-value $mammal $foods $default-food-for-mammals
		     :slot-type :template :value-selector :default-only)

  (print :16)
  (equal-sets? (list $default-food-for-animals)
	       `(get-slot-values ,$harry ,$foods :slot-type :own
				 :value-selector :either
				 :inference-level :taxonomic))

  (put-slot-value $mammal $foods $default-food-for-mammals
		  :slot-type :template :value-selector :default-only)

  (print :17)
  (equal-sets? (list $default-food-for-mammals)
	       `(get-slot-values ,$harry ,$foods :slot-type :own
				 :value-selector :either
				 :inference-level :taxonomic))

  (remove-slot-value $human $foods $default-food-for-mammals
		     :slot-type :template :value-selector :default-only)

  (print :18)
  (equal-sets? nil
	       `(get-slot-values ,$harry ,$foods :slot-type :own
				 :value-selector :default-only
				 :inference-level :taxonomic))
  (print :18b)
  (equal-sets? nil
	       `(get-slot-values ,$human ,$foods :slot-type :template
				 :value-selector :default-only
				 :inference-level :taxonomic))
  (print :18c)
  (equal-sets? (list $default-food-for-mammals)
	       `(get-slot-values ,$mammal ,$foods :slot-type :template
				 :value-selector :default-only
				 :inference-level :taxonomic))

  (print :19)
  (equal-sets? nil
	       `(get-slot-values ,$harry ,$foods :slot-type :own
				 :value-selector :either
				 :inference-level :taxonomic))
  (print :19b)
  (equal-sets? nil
	       `(get-slot-values ,$human ,$foods :slot-type :template
				 :value-selector :either
				 :inference-level :taxonomic))
  (print :19c)
  (equal-sets? (list $default-food-for-mammals)
	       `(get-slot-values ,$mammal ,$foods :slot-type :template
				 :value-selector :either
				 :inference-level :taxonomic))

 
  (print :20)
  (put-slot-value $human $foods $berries :slot-type :template
		  :value-selector :default-only)
  (equal-sets? (list $berries)
	       `(get-slot-values ,$harry ,$foods :inference-level
				 :all-inferable :value-selector :either))

  (print :21)
  (remove-slot-value $harry $foods $berries :slot-type :own
		     :value-selector :default-only)
  (equal-sets? nil
	       `(get-slot-values ,$harry ,$foods :inference-level
				 :all-inferable :value-selector :either))

  (print :22)
  (put-slot-value $human $foods $berries :slot-type :template)
  (equal-sets? (list $berries)
	       `(get-slot-values ,$harry ,$foods :inference-level
				 :all-inferable :value-selector :either)))
  )

(defun test-facet-attachment (silent)
  (unless silent (format t "~%::: Testing facet attachment~%")))

(defun test-facets (kb silent)
  (unless silent (format t "~%::: Testing facet operations~%"))
  (put-slot-value $bill $age 42 :kb kb)
  
  (setq $single-valued (create-pretty-facet 'single-valued :frame-or-nil $bill
					    :slot-or-nil $age
					    :kb kb))
  (put-facet-value $bill $age $single-valued "yes" :kb kb)
  (True? `(slot-has-facet-p ,$bill ,$age ,$single-valued :kb ,kb))
  (false? `(slot-has-facet-p ,$bill ,$color ,$single-valued :kb ,kb))
  (false? `(and (facet-p 'bogus-facet :kb ,kb)
	        (slot-has-facet-p ,$bill ,$age 'bogus-facet :kb ,kb)))
  (false? `(and (facet-p 'bogus-facet :kb ,kb)
	        (slot-has-facet-p ,$bill ,$has-tail 'bogus-facet :kb ,kb)))
  (setq $cardinality
	(if (facet-p :cardinality :kb kb)
	    (coerce-to-facet :cardinality :kb kb)
	    (if (member :user-defined-facets (get-behavior-values :compliance
								   :kb kb))
		(create-pretty-facet :cardinality :frame-or-nil $animal
				     :slot-or-nil $foods
				     :slot-type :template :kb kb)
		nil)))
  (when $cardinality
    (put-facet-value $animal $foods $cardinality 42
		     :slot-type :template :kb kb)
    (put-facet-value $bird $foods $cardinality 3
		     :slot-type :template :kb kb)
    (add-facet-value $bill $foods $cardinality 0 :kb kb)
    (equal-sets? (list 0 42 3)
		 `(get-facet-values ,$bill ,$foods ,$cardinality :kb ,kb))
    (remove-facet-value $bill $foods $cardinality 0 :kb kb)
    (equal-sets? (list 42 3)
		 `(get-facet-values ,$bill ,$foods ,$cardinality :kb ,kb))
    (remove-facet-value $bird $foods $cardinality 3
			:slot-type :template :kb kb)
    (equal-sets? (list 42)
		 `(get-facet-values ,$bill ,$foods ,$cardinality :kb ,kb)))
    ;; We add on $minimum-cardinality for Ontolingua.  This doesn't
    ;; affect the generality of the test.
  (equal-sets? (list :minimum-cardinality $single-valued)
	       `(cons :minimum-cardinality
		      (get-slot-facets ,$bill ,$age :kb ,kb)))
  (equal-sets? (if $cardinality
		   (list :minimum-cardinality $cardinality)
		   (list :minimum-cardinality))
	       `(cons :minimum-cardinality
		 (get-slot-facets ,$bill ,$foods :kb ,kb)))
  (setq $silly-facet
	(create-pretty-facet 'silly-facet :frame-or-nil $bill :slot-or-nil $age
			     :kb kb))
  (put-facet-value $bird $foods $silly-facet "yes" :slot-type :template :kb kb)
  (equal-sets? (if $cardinality
		   (list :minimum-cardinality $cardinality $silly-facet)
		   (list :minimum-cardinality $silly-facet))
	       `(cons :minimum-cardinality
		 (get-slot-facets ,$bill ,$foods :kb ,kb)))

  (when $cardinality
    (remove-facet-value $animal $foods $cardinality 42 :slot-type :template
			:kb kb)
    (equal-sets? (list)
		 `(get-facet-values ,$bill ,$foods ,$cardinality :kb ,kb)))
  (put-facet-value $harry $foods $silly-facet $chips :kb kb)
  (add-facet-value $harry $foods $silly-facet $fries :kb kb)
  (when (get-behavior-values :defaults :kb kb)
  (put-facet-value $animal $foods $silly-facet $default-food-for-animals 
		  :slot-type :template :value-selector :default-only :kb kb)
  (print :1)
  (equal-sets? (list $default-food-for-animals)
	       `(get-facet-values ,$animal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :default-only
				  :inference-level :direct :kb ,kb))
  (print :1b)
  (equal-sets? nil
	       `(get-facet-values ,$animal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :known-true
				  :inference-level :direct :kb ,kb))
  (print :1c)
  (equal-sets? (list $default-food-for-animals)
	       `(get-facet-values ,$animal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :either
				  :inference-level :direct :kb ,kb))
  (print :2)
  (equal-sets? (list $default-food-for-animals)
	       `(get-facet-values ,$animal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :default-only
				  :inference-level :taxonomic :kb ,kb))
  (print :2b)
  (equal-sets? nil
	       `(get-facet-values ,$animal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :known-true
				  :inference-level :taxonomic :kb ,kb))
  (print :2c)
  (equal-sets? (list $default-food-for-animals)
	       `(get-facet-values ,$animal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :either
				  :inference-level :taxonomic :kb ,kb))

  (remove-facet-value $mammal $foods $silly-facet
		      $something-edible
		      :slot-type :template :kb kb)

  (print :3)
  (equal-sets? nil
	       `(get-facet-values ,$mammal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :default-only
				  :inference-level :direct :kb ,kb))
  (print :3b)
  (equal-sets? nil
	       `(get-facet-values ,$mammal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :known-true
				  :inference-level :direct :kb ,kb))
  (print :3c)
  (equal-sets? nil
	       `(get-facet-values ,$mammal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :either
				  :inference-level :direct :kb ,kb))
  (print :4)
  (equal-sets? (list $default-food-for-animals)
	       `(get-facet-values ,$mammal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :default-only
				  :inference-level :taxonomic :kb ,kb))
  (print :4b)
  (equal-sets? nil
	       `(get-facet-values ,$mammal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :known-true
				  :inference-level :taxonomic :kb ,kb))
  (print :4c)
  (equal-sets? (list $default-food-for-animals)
	       `(get-facet-values ,$mammal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :either
				  :inference-level :taxonomic :kb ,kb))

  (put-facet-value $animal $foods $silly-facet 
		   $something-edible
		   :slot-type :template :kb kb)

  (print :4d)
  (equal-sets? (list $default-food-for-animals)
	       `(get-facet-values ,$mammal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :default-only
				  :inference-level :taxonomic :kb ,kb))
  (print :4e)
  (equal-sets? (list $something-edible)
	       `(get-facet-values ,$mammal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :known-true
				  :inference-level :taxonomic :kb ,kb))
  (print :4f)
  (equal-sets? (list $something-edible)
	       `(get-facet-values ,$mammal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :either
				  :inference-level :taxonomic :kb ,kb))

  (remove-facet-value $animal $foods $silly-facet $something-edible
		      :slot-type :template :kb kb)

  (print :4g)
  (equal-sets? (list $default-food-for-animals)
	       `(get-facet-values ,$mammal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :default-only
				  :inference-level :taxonomic :kb ,kb))
  (print :4h)
  (equal-sets? nil
	       `(get-facet-values ,$mammal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :known-true
				  :inference-level :taxonomic :kb ,kb))
  (print :4i)
  (equal-sets? (list $default-food-for-animals)
	       `(get-facet-values ,$mammal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :either
				  :inference-level :taxonomic :kb ,kb))
  
  (print :5)
  (equal-sets? nil
	       `(get-facet-values ,$human ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :default-only
				  :inference-level :direct :kb ,kb))
  (print :5b)
  (equal-sets? nil
	       `(get-facet-values ,$human ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :known-true
				  :inference-level :direct :kb ,kb))
  (print :5c)
  (equal-sets? nil
	       `(get-facet-values ,$human ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :either
				  :inference-level :direct :kb ,kb))
  (print :6)
  (equal-sets? (list $default-food-for-animals)
	       `(get-facet-values ,$human ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :default-only
				  :inference-level :taxonomic :kb ,kb))
  (print :6b)
  (equal-sets? nil
	       `(get-facet-values ,$human ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :known-true
				  :inference-level :taxonomic :kb ,kb))
  (print :6c)
  (equal-sets? (list $default-food-for-animals)
	       `(get-facet-values ,$human ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :either
				  :inference-level :taxonomic :kb ,kb))
  (print :7)
  (equal-sets? nil
	       `(get-facet-values ,$harry ,$foods ,$silly-facet
				  :slot-type :own
				  :value-selector :default-only
				  :inference-level :direct :kb ,kb))
  (print :7b)
  (equal-sets? (list $chips $fries)
	       `(get-facet-values ,$harry ,$foods ,$silly-facet
				  :slot-type :own
				  :value-selector :known-true
				  :inference-level :direct :kb ,kb))
  (print :7c)
  (equal-sets? (list $chips $fries)
	       `(get-facet-values ,$harry ,$foods ,$silly-facet
				  :slot-type :own
				  :value-selector :either
				  :inference-level :direct :kb ,kb))
  (print :8)
  (equal-sets? (list $default-food-for-animals)
	       `(get-facet-values ,$harry ,$foods ,$silly-facet
				  :slot-type :own
				  :value-selector :default-only
				  :inference-level :taxonomic :kb ,kb))
  (print :8b)
  (equal-sets? (list $chips $fries)
	       `(get-facet-values ,$harry ,$foods ,$silly-facet
				  :slot-type :own
				  :value-selector :known-true
				  :inference-level :taxonomic :kb ,kb))
  (print :8c)
  (equal-sets? (list $chips $fries)
	       `(get-facet-values ,$harry ,$foods ,$silly-facet
				  :slot-type :own
				  :value-selector :either
				  :inference-level :taxonomic :kb ,kb))
  

  (remove-facet-value $harry $foods $silly-facet $chips :kb kb)
  (remove-facet-value $harry $foods $silly-facet $fries :kb kb)

  (print :8d)
  (equal-sets? (list $default-food-for-animals)
	       `(get-facet-values ,$harry ,$foods ,$silly-facet
				  :slot-type :own
				  :value-selector :either
				  :inference-level :taxonomic :kb ,kb))

  (put-facet-value $mammal $foods $silly-facet $default-food-for-mammals
		  :slot-type :template :value-selector :default-only :kb kb)
  (print :9)
  (equal-sets? (list $default-food-for-animals)
	       `(get-facet-values ,$animal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :default-only
				  :inference-level :direct :kb ,kb))
  (print :9b)
  (equal-sets? nil
	       `(get-facet-values ,$animal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :known-true
				  :inference-level :direct :kb ,kb))
  (print :9c)
  (equal-sets? (list $default-food-for-animals)
	       `(get-facet-values ,$animal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :either
				  :inference-level :direct :kb ,kb))
  (print :10)
  (equal-sets? (list $default-food-for-animals)
	       `(get-facet-values ,$animal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :default-only
				  :inference-level :taxonomic :kb ,kb))
  (print :10b)
  (equal-sets? nil
	       `(get-facet-values ,$animal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :known-true
				  :inference-level :taxonomic :kb ,kb))
  (print :10c)
  (equal-sets? (list $default-food-for-animals)
	       `(get-facet-values ,$animal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :either
				  :inference-level :taxonomic :kb ,kb))
  (print :11)
  (equal-sets? (list $default-food-for-mammals)
	       `(get-facet-values ,$mammal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :default-only
				  :inference-level :direct :kb ,kb))
  (print :11b)
  (equal-sets? nil
	       `(get-facet-values ,$mammal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :known-true
				  :inference-level :direct :kb ,kb))
  (print :11c)
  (equal-sets? (list $default-food-for-mammals)
	       `(get-facet-values ,$mammal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :either
				  :inference-level :direct :kb ,kb))
  (print :12)
  (equal-sets? (list $default-food-for-mammals)
	       `(get-facet-values ,$mammal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :default-only
				  :inference-level :taxonomic :kb ,kb))
  (print :12b)
  (equal-sets? nil
	       `(get-facet-values ,$mammal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :known-true
				  :inference-level :taxonomic :kb ,kb))
  (print :12c)
  (equal-sets? (list $default-food-for-mammals)
	       `(get-facet-values ,$mammal ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :either
				  :inference-level :taxonomic :kb ,kb))
  (print :13)
  (equal-sets? (list $default-food-for-mammals)
	       `(get-facet-values ,$human ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :default-only
				  :inference-level :taxonomic :kb ,kb))
  (print :13b)
  (equal-sets? nil
	       `(get-facet-values ,$human ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :known-true
				  :inference-level :taxonomic :kb ,kb))
  (print :13c)
  (equal-sets? (list $default-food-for-mammals)
	       `(get-facet-values ,$human ,$foods ,$silly-facet
				  :slot-type :template 
				  :value-selector :either
				  :inference-level :taxonomic :kb ,kb))
  (print :14)
  (equal-sets? nil
	       `(get-facet-values ,$harry ,$foods ,$silly-facet
				  :slot-type :own
				  :value-selector :default-only
				  :inference-level :direct :kb ,kb))
  (print :14b)
  (equal-sets? nil
	       `(get-facet-values ,$harry ,$foods ,$silly-facet
				  :slot-type :own
				  :value-selector :known-true
				  :inference-level :direct :kb ,kb))
  (print :14c)
  (equal-sets? nil
	       `(get-facet-values ,$harry ,$foods ,$silly-facet
				  :slot-type :own
				  :value-selector :either
				  :inference-level :direct :kb ,kb))
  (print :15)
  (equal-sets? (list $default-food-for-mammals)
	       `(get-facet-values ,$harry ,$foods ,$silly-facet
				  :slot-type :own
				  :value-selector :default-only
				  :inference-level :taxonomic :kb ,kb))
  (print :15b)
  (equal-sets? nil
	       `(get-facet-values ,$harry ,$foods ,$silly-facet
				  :slot-type :own
				  :value-selector :known-true
				  :inference-level :taxonomic :kb ,kb))
  (print :15c)
  (equal-sets? (list $default-food-for-mammals)
	       `(get-facet-values ,$harry ,$foods ,$silly-facet
				  :slot-type :own
				  :value-selector :either
				  :inference-level :taxonomic :kb ,kb))

  (remove-facet-value $mammal $foods $silly-facet $default-food-for-mammals
		     :slot-type :template :value-selector :default-only
		     :kb kb)

  (print :16)
  (equal-sets? (list $default-food-for-animals)
	       `(get-facet-values ,$harry ,$foods ,$silly-facet
				  :slot-type :own
				  :value-selector :either
				  :inference-level :taxonomic :kb ,kb))

  (put-facet-value $mammal $foods $silly-facet $default-food-for-mammals
		  :slot-type :template :value-selector :default-only :kb kb)

  (print :17)
  (equal-sets? (list $default-food-for-mammals)
	       `(get-facet-values ,$harry ,$foods ,$silly-facet
				  :slot-type :own
				  :value-selector :either
				  :inference-level :taxonomic :kb ,kb))

  (remove-facet-value $human $foods $silly-facet $default-food-for-mammals
		     :slot-type :template :value-selector :default-only :kb kb)

  (print :18)
  (equal-sets? nil
	       `(get-facet-values ,$harry ,$foods ,$silly-facet
				  :slot-type :own
				  :value-selector :default-only
				  :inference-level :taxonomic :kb ,kb))
  (print :18b)
  (equal-sets? nil
	       `(get-facet-values ,$human ,$foods ,$silly-facet
				  :slot-type :template
				  :value-selector :default-only
				  :inference-level :taxonomic :kb ,kb))
  (print :18c)
  (equal-sets? (list $default-food-for-mammals)
	       `(get-facet-values ,$mammal ,$foods ,$silly-facet
				  :slot-type :template
				  :value-selector :default-only
				  :inference-level :taxonomic :kb ,kb))

  (print :19)
  (equal-sets? nil
	       `(get-facet-values ,$harry ,$foods ,$silly-facet
				  :slot-type :own
				  :value-selector :either
				  :inference-level :taxonomic :kb ,kb))
  (print :19b)
  (equal-sets? nil
	       `(get-facet-values ,$human ,$foods ,$silly-facet
				  :slot-type :template
				  :value-selector :either
				  :inference-level :taxonomic :kb ,kb))
  (print :19c)
  (equal-sets? (list $default-food-for-mammals)
	       `(get-facet-values ,$mammal ,$foods ,$silly-facet
				  :slot-type :template
				  :value-selector :either
				  :inference-level :taxonomic :kb ,kb))

  (print :20)
  (put-facet-value $human $foods $silly-facet $berries :slot-type :template
		   :value-selector :default-only :kb kb)
  (equal-sets? (list $berries)
	       `(get-facet-values ,$harry ,$foods ,$silly-facet
		 :inference-level :all-inferable :value-selector :either
		 :kb ,kb))

  (print :21)
  (remove-facet-value $harry $foods $silly-facet $berries :slot-type :own
		      :value-selector :default-only :kb kb)
  (equal-sets? nil
	       `(get-facet-values ,$harry ,$foods ,$silly-facet
		 :inference-level :all-inferable :value-selector :either
		 :kb ,kb))

  (print :22)
  (put-facet-value $human $foods $silly-facet $berries :slot-type
		   :template :kb kb)
  (equal-sets? (list $berries)
	       `(get-facet-values ,$harry ,$foods ,$silly-facet
		 :inference-level :all-inferable :value-selector :either
		 :kb ,kb))))

(defun find-constraint-facet (facet-name kb)
  (let ((facet-sym (intern (concatenate 'string "$" (symbol-name facet-name))
			   :okbc-test)))
    (multiple-value-bind (facet found-p) 
      (coerce-to-facet facet-name :error-p nil :kb kb)
      (setf (symbol-value facet-sym)
	    (if found-p
	        facet
	      (if (member :user-defined-facets
			  (get-behavior-values :compliance :kb kb))
		  (create-pretty-facet facet-name :kb kb)
		  nil))))))	      

(defun find-constraint-class (class-name kb)
  (let ((class-sym (intern (concatenate 'string "$" (symbol-name class-name))
			   :okbc-test)))
    (multiple-value-bind (class found-p) 
      (coerce-to-frame class-name :error-p nil :kb kb)
      (setf (symbol-value class-sym)
	    (if found-p
	        class
	        (create-pretty-class class-name :kb kb :direct-superclasses
				     (case class-name
				       (:thing nil)
				       (:integer '(:number))
				       (:list '(:individual))
				       (otherwise '(:thing)))))))))

(defun find-constraint-slot (slot-name kb)
  (let ((slot-sym (intern (concatenate 'string "$" (symbol-name slot-name))
			  :okbc-test)))
    (multiple-value-bind (slot found-p) 
      (coerce-to-slot slot-name :error-p nil :kb kb)
      (setf (symbol-value slot-sym)
	    (if found-p
	        slot
	        (create-pretty-slot slot-name :kb kb))))))	      

(defun test-constraints (kb silent)
  (declare (special ok-back:*okbc-standard-facet-names*
		    ok-back:*okbc-standard-slot-names*
		    ok-back:*okbc-standard-class-names*))
  (let ((supported-p (member :immediate (get-behavior-supported-values
					 :constraint-checking-time :kb kb)))
	(current (get-behavior-values :constraint-checking-time :kb kb)))
    (when supported-p
      (unwind-protect
	   (progn (put-behavior-values :constraint-checking-time '(:immediate)
				       :kb kb)
		  (unless silent (format t "~%::: Testing constraints"))
		  (loop for sym in ok-back:*okbc-standard-facet-names*
			do (find-constraint-facet sym kb))
		  (loop for sym in ok-back:*okbc-standard-class-names*
			do (find-constraint-class sym kb))
		  (loop for sym in ok-back:*okbc-standard-slot-names*
			do (find-constraint-slot sym kb))
		  (let ((checked (get-behavior-values :constraints-checked
						      :kb kb)))
		    (loop for slot in ok-back:*okbc-standard-slot-names*
			  when (member slot checked)
			  do (test-constraint-slot slot kb silent)
			     (unless silent (princ ".")))
		    (loop for c in checked
			  do (test-constraint-facet c kb silent)
			     (unless silent (princ ".")))))
	(put-behavior-values :constraint-checking-time current :kb kb)))))

(defmethod test-constraint-slot ((constraint t) (kb t) (silent t))
  (warn "Constraint checking test not implemented for slot ~S" constraint))

(defmethod test-constraint-slot 
  ((constraint (eql :slot-collection-type)) (kb t) (silent t))
  nil)

(defmethod test-constraint-slot ((constraint (eql :slot-some-values)) (kb t)
				 (silent t))
  nil)

(defmethod test-constraint-slot
    ((constraint (eql :slot-inverse)) (kb t) (silent t))
  (unwind-protect
       (progn
	 (handler-case
	  (progn (put-slot-values $foods :slot-inverse (list $ted) :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (put-slot-values $foods :slot-inverse (list $has-tail) :kb kb))
    ;; zero out constraints
    (put-slot-values $foods :slot-inverse nil :kb kb)))

(defmethod test-constraint-slot
  ((constraint (eql :slot-same-values)) (kb t) (silent t))
  (unwind-protect
       (progn
	 (handler-case
	  (progn (put-slot-values $foods :slot-same-values (list $ted) :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (put-slot-values $foods :slot-same-values (list (list $age $has-tail))
			  :kb kb))
    ;; zero out constraints
    (put-slot-values $foods :slot-same-values nil :kb kb)))

(defmethod test-constraint-slot
  ((constraint (eql :slot-not-same-values)) (kb t) (silent t))
  (unwind-protect
       (progn
	 (handler-case
	  (progn (put-slot-values $foods :slot-not-same-values (list $ted)
				  :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (put-slot-values $foods :slot-not-same-values
			  (list (list $age $has-tail)) :kb kb))
    ;; zero out constraints
    (put-slot-values $foods :slot-not-same-values nil :kb kb)))

(defmethod test-constraint-slot
    ((constraint (eql :slot-subset-of-values)) (kb t) (silent t))
  (unwind-protect
       (progn
	 (handler-case
	  (progn (put-slot-values $foods :slot-subset-of-values (list $ted)
				  :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (put-slot-values $foods :slot-subset-of-values
			  (list (list $age $has-tail)) :kb kb))
    ;; zero out constraints
    (put-slot-values $foods :slot-subset-of-values nil :kb kb)))

(defmethod test-constraint-slot 
  ((constraint (eql :slot-numeric-minimum)) (kb t) (silent t))
  (unwind-protect
       (progn
	 (handler-case
	  (progn (put-slot-values $foods :slot-numeric-minimum (list $ted)
				  :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (put-slot-values $foods :slot-numeric-minimum (list 42 3) :kb kb)
	 (put-slot-values $ted $foods (list 2001 101 42) :kb kb)
	 (handler-case 
	  (progn (put-slot-values $ted $foods (list 2001 101 42 3) :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition)))
    ;; zero out constraints
    (put-slot-values $foods :slot-numeric-minimum nil :kb kb)))

(defmethod test-constraint-slot 
  ((constraint (eql :slot-numeric-maximum)) (kb t) (silent t))
  (unwind-protect
       (progn
	 (handler-case
	  (progn (put-slot-values $foods :slot-numeric-maximum (list $ted)
				  :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (put-slot-values $foods :slot-numeric-maximum (list 42 3) :kb kb)
	 (put-slot-values $ted $foods (list 0 1 2 3) :kb kb)
	 (handler-case 
	  (progn (put-slot-values $ted $foods (list 0 1 2 3 42) :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition)))
    ;; zero out constraints
    (put-slot-values $foods :slot-numeric-maximum nil :kb kb)))

(defmethod test-constraint-slot 
  ((constraint (eql :slot-maximum-cardinality)) (kb t) (silent t))
  (unwind-protect
       (progn
	 (handler-case
	  (progn (put-slot-values $foods :slot-maximum-cardinality (list $ted)
				  :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (handler-case
	  (progn (put-slot-values $foods :slot-maximum-cardinality (list -1)
				  :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (put-slot-values $foods :slot-maximum-cardinality (list 3) :kb kb)
	 (put-slot-values $ted $foods (list $seeds) :kb kb)
	 (handler-case 
	  (progn (put-slot-values $ted $foods (list $ted $linda $seeds $chips)
				  :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition)))
    ;; zero out constraints
    (put-slot-values $foods :slot-maximum-cardinality nil :kb kb)))

(defmethod test-constraint-slot 
  ((constraint (eql :slot-minimum-cardinality)) (kb t) (silent t))
  (unwind-protect
       (progn
	 (handler-case
	  (progn (put-slot-values $foods :slot-minimum-cardinality (list $ted)
				  :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (handler-case
	  (progn (put-slot-values $foods :slot-minimum-cardinality (list -1)
				  :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (put-slot-values $foods :slot-minimum-cardinality (list 3) :kb kb)
	 (put-slot-values $ted $foods (list $seeds $chips $linda $ted) :kb kb)
	 (handler-case 
	  (progn (put-slot-values $ted $foods (list $ted $chips) :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition)))
    ;; zero out constraints
    (put-slot-values $foods :slot-minimum-cardinality nil :kb kb)))

(defmethod test-constraint-slot
  ((constraint (eql :slot-cardinality)) (kb t) (silent t))
  (unwind-protect
       (progn
	 (handler-case
	  (progn (put-slot-values $foods :slot-cardinality (list $ted) :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (handler-case
	  (progn (put-slot-values $foods :slot-cardinality (list 1 4) :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (handler-case
	  (progn (put-slot-values $foods :slot-cardinality (list -1) :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (put-slot-values $foods :slot-cardinality (list 1) :kb kb)
	 (put-slot-values $ted $foods (list $seeds) :kb kb)
	 (handler-case 
	  (progn (put-slot-values $ted $foods (list $seeds $chips) :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition)))
    ;; zero out constraints
    (put-slot-values $foods :slot-cardinality nil :kb kb)))

(defmethod test-constraint-slot
  ((constraint (eql :slot-value-type)) (kb t) (silent t))
  (unwind-protect
       (progn
	 (handler-case
	  (progn (put-slot-values $foods :slot-value-type (list $ted) :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (put-slot-values $foods :slot-value-type (list $food) :kb kb)
	 (put-slot-values $ted $foods (list $something-edible $seeds) :kb kb) 
	 (handler-case
	  (progn (put-slot-values $ted $foods
				  (list $something-edible $harry) :kb kb) 
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (put-slot-values $foods :slot-value-type
			  `(,$food (setof ,$berries ,$chips)) :kb kb)
	 (put-slot-values $harry $foods (list $chips) :kb kb)
	 (handler-case
	  (progn (put-slot-values $harry $foods (list $seeds) :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (put-slot-values $age :slot-value-type (list :number) :kb kb)
	 (put-slot-values $harry $age (list 42) :kb kb)
	 (handler-case
	  (progn (put-slot-values $harry $age (list $seeds) :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (put-slot-values $foods :slot-value-type `((union ,$food ,$reptile))
			  :kb kb)
	 (put-slot-values $harry $foods (list $linda) :kb kb)
	 (handler-case 
	  (progn (put-slot-values $harry $foods (list $ted) :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition)))
    ;; zero out constraints
    (put-slot-values $foods :slot-value-type nil :kb kb)
    (put-slot-values $age :slot-value-type nil :kb kb)))

(defmethod test-constraint-slot
  ((constraint (eql :domain)) (kb t) (silent t))
  (unwind-protect
       (progn
	 (handler-case
	  (progn (put-slot-values $foods :domain (list $ted) :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (put-slot-values $foods :domain (list $animal) :kb kb)
	 (handler-case
	  (progn (put-slot-values $chips $foods (list $chips) :kb kb) 
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (put-slot-values $foods :domain `(,$animal (setof ,$ted ,$linda))
			  :kb kb)
	 (put-slot-values $ted $foods (list $chips) :kb kb)
	 (handler-case
	  (progn (put-slot-values $harry $foods (list $seeds) :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (put-slot-values $foods :domain `((union ,$elephant ,$reptile))
			  :kb kb)
	 (put-slot-values $edward $foods (list $chips) :kb kb)
	 (handler-case 
	  (progn (put-slot-values $harry $foods (list $chips) :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition)))
    ;; zero out constraints
    (put-slot-values $foods :domain nil :kb kb)
    (put-slot-values $age :domain nil :kb kb)))

(defmethod test-constraint-facet ((constraint t) (kb t) (silent t))
  (warn "Constraint checking test not implemented for facet ~S" constraint))

(defmethods test-constraint-facet ((constraint ((eql :slot-value-type)
						(eql :slot-inverse)
						(eql :slot-cardinality)
						(eql :slot-minimum-cardinality)
						(eql :slot-maximum-cardinality)
						(eql :slot-same-values)
						(eql :slot-not-same-values)
						(eql :slot-subset-of-values)
						(eql :slot-numeric-minimum)
						(eql :slot-numeric-maximum)
						(eql :slot-some-values)
						(eql :slot-collection-type)))
				   (kb t) (silent t))
  nil)

(defmethod test-constraint-facet ((constraint (eql :collection-type)) (kb t)
				  (silent t))
  nil)

(defmethod test-constraint-facet ((constraint (eql :domain)) (kb t)
			    (silent t))
  nil)

(defmethod test-constraint-facet ((constraint (eql :some-values)) (kb t)
			    (silent t))
  nil)

(defmethod test-constraint-facet
  ((constraint (eql :inverse)) (kb t) (silent t))
  (unwind-protect
       (progn
	 (handler-case
	  (progn (put-facet-values $tiger $foods :inverse (list $ted) :kb kb 
				   :slot-type :template)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (put-facet-values $tiger $foods :inverse (list $has-tail) :kb kb 
			   :slot-type :template))
    ;; zero out constraints
    (put-facet-values $tiger $foods :inverse nil :kb kb 
		      :slot-type :template)))

(defmethod test-constraint-facet
  ((constraint (eql :same-values)) (kb t) (silent t))
  (unwind-protect
       (progn
	 (handler-case
	  (progn (put-facet-values $tiger $foods :same-values (list $ted)
				   :kb kb 
				   :slot-type :template)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (put-facet-values $tiger $foods :same-values
			   (list (list $age $has-tail))
			   :kb kb :slot-type :template))
    ;; zero out constraints
    (put-facet-values $tiger $foods :same-values nil :kb kb 
		      :slot-type :template)))

(defmethod test-constraint-facet
  ((constraint (eql :not-same-values)) (kb t) (silent t))
  (unwind-protect
       (progn
	 (handler-case
	  (progn (put-facet-values $tiger $foods :not-same-values (list $ted)
				   :kb kb 
				   :slot-type :template)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (put-facet-values $tiger $foods :not-same-values
			   (list (list $age $has-tail))
			   :kb kb :slot-type :template))
    ;; zero out constraints
    (put-facet-values $tiger $foods :not-same-values nil :kb kb 
		      :slot-type :template)))

(defmethod test-constraint-facet
  ((constraint (eql :subset-of-values)) (kb t) (silent t))
  (unwind-protect
       (progn
	 (handler-case
	  (progn (put-facet-values $tiger $foods :subset-of-values (list $ted)
				   :kb kb :slot-type :template)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (put-facet-values $tiger $foods :subset-of-values
			   (list (list $age $has-tail))
			   :kb kb :slot-type :template))
    ;; zero out constraints
    (put-facet-values $tiger $foods :subset-of-values nil :kb kb 
		      :slot-type :template)))

(defmethod test-constraint-facet 
  ((constraint (eql :numeric-minimum)) (kb t) (silent t))
  (unwind-protect
       (progn
	 (handler-case
	  (progn (put-facet-values $tiger $foods :numeric-minimum (list $ted)
				   :kb kb :slot-type :template)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (put-facet-values $tiger $foods :numeric-minimum (list 42 3) :kb kb 
			   :slot-type :template)
	 (put-slot-values $ted $foods (list 2001 101 42) :kb kb)
	 (handler-case 
	  (progn (put-slot-values $ted $foods (list 2001 101 42 3) :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition)))
    ;; zero out constraints
    (put-facet-values $tiger $foods :numeric-minimum nil :kb kb 
		      :slot-type :template)))

(defmethod test-constraint-facet 
  ((constraint (eql :numeric-maximum)) (kb t) (silent t))
  (unwind-protect
       (progn
	 (handler-case
	  (progn (put-facet-values $tiger $foods :numeric-maximum (list $ted)
				   :kb kb :slot-type :template)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (put-facet-values $tiger $foods :numeric-maximum (list 42 3) :kb kb 
			   :slot-type :template)
	 (put-slot-values $ted $foods (list 0 1 2 3) :kb kb)
	 (handler-case 
	  (progn (put-slot-values $ted $foods (list 0 1 2 3 42) :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition)))
    ;; zero out constraints
    (put-facet-values $tiger $foods :numeric-maximum nil :kb kb 
		      :slot-type :template)))

(defmethod test-constraint-facet 
  ((constraint (eql :maximum-cardinality)) (kb t) (silent t))
  (unwind-protect
       (progn
	 (handler-case
	  (progn (put-facet-values $tiger $foods :maximum-cardinality
				   (list $ted) :kb kb :slot-type :template)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (handler-case
	  (progn (put-facet-values $tiger $foods :maximum-cardinality (list -1)
				   :kb kb :slot-type :template)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (put-facet-values $tiger $foods :maximum-cardinality (list 3) :kb kb 
			   :slot-type :template)
	 (put-slot-values $ted $foods (list $seeds) :kb kb)
	 (handler-case 
	  (progn (put-slot-values $ted $foods (list $ted $linda $seeds $chips)
				  :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition)))
    ;; zero out constraints
    (put-facet-values $tiger $foods :maximum-cardinality nil :kb kb 
		      :slot-type :template)))

(defmethod test-constraint-facet 
  ((constraint (eql :minimum-cardinality)) (kb t) (silent t))
  (unwind-protect
       (progn
	 (handler-case
	  (progn (put-facet-values $tiger $foods :minimum-cardinality
				   (list $ted) :kb kb :slot-type :template)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (handler-case
	  (progn (put-facet-values $tiger $foods :minimum-cardinality (list -1)
				   :kb kb :slot-type :template)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (put-facet-values $tiger $foods :minimum-cardinality (list 3) :kb kb 
			   :slot-type :template)
	 (put-slot-values $ted $foods (list $seeds $chips $linda $ted) :kb kb)
	 (handler-case 
	  (progn (put-slot-values $ted $foods (list $ted $chips) :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition)))
    ;; zero out constraints
    (put-facet-values $tiger $foods :minimum-cardinality nil :kb kb 
		      :slot-type :template)))

(defmethod test-constraint-facet
  ((constraint (eql :cardinality)) (kb t) (silent t))
  (unwind-protect
       (progn
	 (handler-case
	  (progn (put-facet-values $tiger $foods :cardinality (list $ted)
				   :kb kb :slot-type :template)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (handler-case
	  (progn (put-facet-values $tiger $foods :cardinality (list 1 4)
				   :kb kb :slot-type :template)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (handler-case
	  (progn (put-facet-values $tiger $foods :cardinality (list -1) :kb kb 
				   :slot-type :template)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition))
	 (put-facet-values $tiger $foods :cardinality (list 1) :kb kb 
			   :slot-type :template)
	 (put-slot-values $ted $foods (list $seeds) :kb kb)
	 (handler-case 
	  (progn (put-slot-values $ted $foods (list $seeds $chips) :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error."))
	  (constraint-violation (condition) condition)))
    ;; zero out constraints
    (put-facet-values $tiger $foods :cardinality nil :kb kb 
		      :slot-type :template)))

(defmethod test-constraint-facet
  ((constraint (eql :value-type)) (kb t) (silent t))
  (unwind-protect
       (progn
	 (handler-case
	  (progn (put-facet-values $tiger $foods :value-type (list $ted)
				   :kb kb :slot-type :template)
		 (cerror "Go ahead anyway" "Should have signaled an error 1."))
	  (constraint-violation (condition) condition))
	 (put-facet-values $tiger $foods :value-type (list $food) :kb kb 
			   :slot-type :template)
	 (put-slot-values $ted $foods (list $something-edible $seeds) 
			  :kb kb) 
	 (handler-case
	  (progn (put-slot-values $ted $foods 
				  (list $something-edible $harry) :kb kb) 
		 (cerror "Go ahead anyway" "Should have signaled an error 2."))
	  (constraint-violation (condition) condition))
	 (put-facet-values $human $foods :value-type 
			   `(,$food (setof ,$berries ,$chips))
			   :kb kb :slot-type :template)
	 (put-slot-values $harry $foods (list $chips) :kb kb)
	 (handler-case
	  (progn (put-slot-values $harry $foods (list $seeds) :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error 3."))
	  (constraint-violation (condition) condition))
	 (put-facet-values $human $age :value-type (list :number)
			   :kb kb :slot-type :template)
	 (put-slot-values $harry $age (list 42) :kb kb)
	 (handler-case
	  (progn (put-slot-values $harry $age (list $seeds) :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error 4."))
	  (constraint-violation (condition) condition))
	 (put-facet-values $human $foods :value-type 
			   `((union ,$food ,$reptile))
			   :kb kb :slot-type :template)
	 (put-slot-values $harry $foods (list $linda) :kb kb)
	 (handler-case 
	  (progn (put-slot-values $harry $foods (list $ted) :kb kb)
		 (cerror "Go ahead anyway" "Should have signaled an error 5."))
	  (constraint-violation (condition) condition)))
    ;; zero out constraints
    (put-facet-values $tiger $foods :value-type nil :kb kb 
		      :slot-type :template)
    (put-facet-values $human $foods :value-type nil :kb kb 
		      :slot-type :template)
    (put-facet-values $human $age :value-type nil :kb kb 
		      :slot-type :template)))


(defun test-copy-kb-internal (kb new-kb silent)
  (when (not silent) (format t "~%:::     Testing copy-kb~%"))
  (let ((ht (copy-kb kb new-kb :error-p t :kb-local-only-p t
		     :missing-frame-action :allocate)))
    (perform-tests-for-copy-kb kb new-kb)
    ht))

(defun perform-tests-for-copy-kb (kb new-kb)
  (let ((extra `(:pretty-name ,@ok-back:*okbc-standard-names*)))
    ;;; extra frames might appear as frames in some implementations
    ;;; discount these.
    (let ((from-new-kb (loop for f in (get-kb-roots :kb new-kb
						    :kb-local-only-p t
						    :selector :user)
			     when (frame-in-kb-p f :kb new-kb
						 :kb-local-only-p t)
			     collect (get-frame-pretty-name f :kb new-kb)))
	  (from-kb (loop for f in (get-kb-roots :kb kb :kb-local-only-p t
						:selector :user)
			 when (frame-in-kb-p f :kb kb
					     :kb-local-only-p t)
			 collect (get-frame-pretty-name f :kb kb))))
      ;; Note that in the target KB we may end up with a smaller number
      ;; of roots because the copy from the source KB may have copied frames
      ;; from included KBs including the kernel ontology.  The kb-local-only-p
      ;; roots are likely to be fewer in the target because of this.
      (subsets? (append extra from-new-kb) `(append ',extra ',from-kb)))
    (let ((from-new-kb (loop for f in (get-kb-classes :kb new-kb
						      :selector :frames
						      :kb-local-only-p t)
			     when (frame-in-kb-p f :kb new-kb
						 :kb-local-only-p t)
			     collect (get-frame-pretty-name f :kb new-kb)))
	  (from-kb (loop for f in (get-kb-classes :kb kb :kb-local-only-p t
						  :selector :frames)
			 when (frame-in-kb-p f :kb kb
					     :kb-local-only-p t)
			 collect (get-frame-pretty-name f :kb kb))))
      (subsets? (append extra from-kb) `(append ',extra ',from-new-kb)))
    (let ((from-new-kb (loop for f in (get-kb-individuals :kb new-kb
							  :selector :frames
							  :kb-local-only-p t)
			     when (frame-in-kb-p f :kb new-kb
						 :kb-local-only-p t)
			     collect (get-frame-pretty-name f :kb new-kb)))
	  (from-kb (loop for f in (get-kb-individuals :kb kb 
						      :selector :frames
						      :kb-local-only-p t)
			 when (frame-in-kb-p f :kb kb
					     :kb-local-only-p t)
			 collect (get-frame-pretty-name f :kb kb))))
      (subsets? (append extra from-kb) `(append ',extra ',from-new-kb)))))

(defun iterate-test-over-behaviors (function kb string silent)
  (when (not silent)
    (format t "~%::: Iterating ~A test over behaviors of ~S~%"
	    string kb))
  (let ((behaviors (get-kb-behaviors :kb-type-or-kb kb)))
    (let ((alist (loop for b in behaviors
		       for values = (get-behavior-supported-values
				     b :kb kb)
		       when (and (rest values)
				 (not (member b '(:constraints-checked
						  :compliance
						  :are-frames
						  :class-slot-types))))
		       collect (cons b values))))
      (let ((current (loop for spec in alist
			   collect (cons (first spec)
					 (get-behavior-values (first spec)
							      :kb kb)))))
      (labels ((rec (remaining)
		 (if remaining
		     (destructuring-bind (b . values) (first remaining)
		       (when (not silent)
			 (format t "~%;;;   Testing with ~A = ~{~A~^, ~}"
				 b values))
		       (rec (rest remaining))
		       (let ((changed-p nil))
			 (when (rest values)
			   (loop for value in values
				 when (handler-case
				       (progn (put-behavior-values
					       b (list value) :kb kb)
					      (setq changed-p t)
					      t)
				       (illegal-behavior-values
					(condition)
					(declare (ignore condition))
					(format t "~%;;;   Behavior ~A = ~A ~
                                                         can't be tested."
						b value)
					nil))
				 do (when (not silent)
				      (format t "~%;;;   Testing with ~A = ~A"
					      b value))
				 (rec (rest remaining))))
			 (when changed-p
			   (put-behavior-values b (rest (assoc b current))
						:kb kb))))
		     (funcall function))))
	(rec alist))))))

(defun test-copy-kb (kb new-kb silent)
  (iterate-test-over-behaviors
   #'(lambda () 
       (test-copy-kb-internal kb new-kb silent)
       (loop for frame in (get-kb-frames :kb new-kb)
	     do (delete-frame frame :kb new-kb)))
   new-kb "Copy-kb" silent))

(defun test-coerce-to-kb-value (silent)
  (unless silent (format t "~%::: Testing coerce-to-kb-value~%"))
  (let ((cookie `((1 2 "a string" (,$food ,$bill)) t nil))
	(cookie-with-names `((1 2 "a string" (food bill)) t nil))
	(string "(1 2 \"a string\" (food bill))")
	(wild-string "(1 2 \"a string\" (food* bill))")
	(just-frames (list $food $bill $living-thing))
	(just-frames-string "(food bill living-thing)")
	(alist-string "(food* *t)")
	(alist-result `((*t "" ,$trout ,$elephant ,$plant
			 ,@(if (member :user-defined-facets
				       (get-behavior-values :compliance))
			       (list $silly-facet)
			       nil)
			 ,@(if (boundp '$list)
			       (list $list)
			       nil))
			(FOOD* "FOOD" ,$FOOD ,$FOODS))))
    (declare (special just-frames-string string wild-string))
    (equal? cookie
	    `(multiple-value-list
	      (coerce-to-kb-value string :value
	       :wildcards-allowed-p nil
	       :force-case-insensitive-p nil
	       :error-p t
	       :frame-action :error-if-not-unique
	       :kb-local-only-p nil)))
    (equal? cookie
	    `(multiple-value-list
	      (coerce-to-kb-value string :value
	       :wildcards-allowed-p t
	       :force-case-insensitive-p nil
	       :error-p t
	       :frame-action :error-if-not-unique
	       :kb-local-only-p nil)))
    (handler-case
     (progn (coerce-to-kb-value wild-string :value
				:wildcards-allowed-p t
				:force-case-insensitive-p nil
				:error-p t
				:frame-action :error-if-not-unique
				:kb-local-only-p nil)
	    (generic-error "Should never get here!"))
     (not-unique-error (condition) (declare (ignore condition))))
    (string-equal-except-packages?
     cookie-with-names
     `(multiple-value-list
       (coerce-to-kb-value string :value
	:wildcards-allowed-p nil
	:force-case-insensitive-p nil
	:error-p t
	:frame-action
	:do-not-coerce-to-frames
	:kb-local-only-p nil)))
    (handler-case
     (progn (coerce-to-kb-value string :value
				:wildcards-allowed-p nil
				:force-case-insensitive-p nil
				:error-p t
				:frame-action :must-name-frames
				:kb-local-only-p nil)
	    (warn  "The string \"a string\" has been coerced to a frame"))
     (not-coercible-to-frame
      (condition)
      (with-condition-slots (okbc:frame) condition
			    (continuable-assert
			     (equal "a string" okbc:frame)))))
    (string-equal-except-packages?
     (list just-frames t nil)
     `(multiple-value-list
       (coerce-to-kb-value just-frames-string :value
	:wildcards-allowed-p nil
	:force-case-insensitive-p nil
	:error-p t
	:frame-action :must-name-frames
	:kb-local-only-p nil)))
    (multiple-value-bind (found-p coerce-worked-ok-p alist)
	(coerce-to-kb-value alist-string :value
			    :wildcards-allowed-p t
			    :force-case-insensitive-p nil
			    :error-p t
			    :frame-action :options-if-not-unique
			    :kb-local-only-p nil)
      (declare (ignore coerce-worked-ok-p))
      (false? found-p)
      (loop for (patterna match-stringa . framesa) in alist
	    for (patternb match-stringb . framesb) in alist-result
	    do (string-equal-except-packages? patterna (list 'quote patternb))
	       (equal? match-stringa (list 'quote match-stringb))
	       (subsets? framesb (list 'quote framesa))))))

(defun test-procedures (kb silent)
  (when (not silent) (format t "~%::: Testing procedures~%"))
  (let ((test1
	 (procedure test1
		    "(frame kb)"
		    "(list frame (get-frame-pretty-name frame :kb kb) kb)")))
    (register-procedure nil test1 :kb kb))
  (let ((test2
	 (procedure
	  test2
	  "(frame kb)"
	  "    (do-list (subclass (get-class-subclasses
                                     frame :inference-level :direct :kb kb
                                           :kb-local-only-p nil))
                (list subclass (call-procedure 'test1 :kb kb :arguments
				   	       (list subclass kb))
                      (test1 subclass kb)))")))
    (register-procedure nil test2 :kb kb)
    (let ((expected-result
	   (list (list $animal
		       (list $animal
			     (get-frame-pretty-name $animal :kb kb)
			     kb)
		       (list $animal
			     (get-frame-pretty-name $animal :kb kb)
			     kb))
		 (list $plant
		       (list $plant
			     (get-frame-pretty-name $plant :kb kb)
			     kb)
		       (list $plant
			     (get-frame-pretty-name $plant :kb kb)
			     kb)))))
      (equal-sets? expected-result
		   `(call-procedure 'test2 :arguments (list ,$living-thing ,kb)
				    :kb ,kb))
      (equal-sets? expected-result
		   `(call-procedure ,test2 :arguments (list ,$living-thing ,kb)
				    :kb ,kb)))))
      
(defun test-cache-management (silent)
  (when (and ok-cache:*allow-okbc-caching-p*
	     (or (typep (current-kb) 'ok-back:caching-mixin)
		 (typep (current-kb) 'ok-back:caching-structure-kb)))
    (unless silent (format t "~%::: Testing cache management~%"))
    (let ((values (multiple-value-list
		      (get-slot-values $bill $foods :slot-type :own))))
      (true? (cached-p-get-slot-values $bill $foods :slot-type :own))
      (flush-cache (current-kb))
      (false? (cached-p-get-slot-values $bill $foods :slot-type :own))
      (encache-get-slot-values (cons :values values)
			       $bill $foods :slot-type :own)
      (true? (cached-p-get-slot-values $bill $foods :slot-type :own)))
    (progn (get-frame-details $harry :inference-level :direct)
	   (true? (cached-p-get-frame-slots $harry :slot-type :own
					    :inference-level :direct)))))

(defframe c1)
(defframe c2)
(defframe c3)
(defframe c4)
(defframe s1)
(defframe s2)
(defframe fa)
(defframe i1)
(defframe i2)
(defframe i3)
(defframe i4)

(defun test-get-frames-with-slot-or-facet-value (kb silent)
  (unless silent (format t "~%::: Testing Get-frames-with-slot/facet-value~%"))
  ;; Set up the kb
  (setq c1 (create-pretty-class 'c1 :kb kb :direct-superclasses nil))
  (setq c2 (create-pretty-class 'c2 :kb kb :direct-superclasses c1))
  (setq c3 (create-pretty-class 'c3 :kb kb :direct-superclasses c1))
  (setq c4 (create-pretty-class 'c4 :kb kb :direct-superclasses c2))
  (setq s1 (create-pretty-slot  's1 :kb kb))
  (setq s2 (create-pretty-slot  's2 :kb kb))
  (setq fa (create-pretty-facet 'fa :kb kb))
  (setq i1 (create-pretty-individual 'i1 :direct-types c1 :kb kb))
  (setq i2 (create-pretty-individual 'i2 :direct-types c2 :kb kb))
  (setq i3 (create-pretty-individual 'i3 :direct-types c3 :kb kb))
  (setq i4 (create-pretty-individual 'i4 :direct-types c4 :kb kb))
  (put-slot-value c1 s1 42 :kb kb :slot-type :template
		  :value-selector :known-true)
  (put-slot-value i1 s1 43 :kb kb :slot-type :own
		  :value-selector :known-true)
  (put-facet-value c1 s1 fa 42 :kb kb :slot-type :template
		   :value-selector :known-true)
  (put-facet-value i1 s1 fa 43 :kb kb :slot-type :own
		   :value-selector :known-true)
  ;; Now the defaults
  (when (get-behavior-values :defaults)
    (put-slot-value c1 s2 42 :kb kb :slot-type :template
		    :value-selector :default-only)
    (remove-slot-value c4 s2 42 :kb kb :slot-type :template
		       :value-selector :default-only)
    (put-facet-value c1 s2 fa 42 :kb kb :slot-type :template
		     :value-selector :default-only)
    (remove-facet-value c4 s2 fa 42 :kb kb :slot-type :template
			:value-selector :default-only))
  ;; First test the slots
  (equal-sets?
   `(,c1)
   `(get-frames-with-slot-value ,s1 42 :kb ,kb :slot-type :template
     :inference-level :direct
     :value-selector :known-true :kb-local-only-p nil))
  (equal-sets?
   `(,c1)
   `(get-frames-with-slot-value ,s1 42 :kb ,kb :slot-type :all
     :inference-level :direct
     :value-selector :known-true :kb-local-only-p nil))
  (equal-sets?
   `(,i1)
   `(get-frames-with-slot-value ,s1 43 :kb ,kb :slot-type :own
     :inference-level :direct
     :value-selector :known-true :kb-local-only-p nil))
  (equal-sets?
   `(,c1 ,c2 ,c3 ,c4)
   `(get-frames-with-slot-value ,s1 42 :kb ,kb :slot-type :template
     :inference-level :taxonomic
     :value-selector :known-true :kb-local-only-p nil))
  (equal-sets?
   `(,i1)
   `(get-frames-with-slot-value ,s1 43 :kb ,kb :slot-type :own
     :inference-level :taxonomic
     :value-selector :known-true :kb-local-only-p nil))
  (equal-sets?
   `(,i1 ,i2, i3 ,i4)
   `(get-frames-with-slot-value ,s1 42 :kb ,kb :slot-type :own
     :inference-level :taxonomic
     :value-selector :known-true :kb-local-only-p nil))
  (equal-sets?
   `(,c1 ,c2 ,c3 ,c4 ,i1 ,i2, i3 ,i4)
   `(get-frames-with-slot-value ,s1 42 :kb ,kb :slot-type :all
     :inference-level :taxonomic
     :value-selector :known-true :kb-local-only-p nil))
  ;; Now test the facets
  (equal-sets?
   `(,c1)
   `(get-frames-with-facet-value ,s1 ,fa 42 :kb ,kb :slot-type :template
     :inference-level :direct
     :value-selector :known-true :kb-local-only-p nil))
  (equal-sets?
   `(,c1)
   `(get-frames-with-facet-value ,s1 ,fa 42 :kb ,kb :slot-type :all
     :inference-level :direct
     :value-selector :known-true :kb-local-only-p nil))
  (equal-sets?
   `(,i1)
   `(get-frames-with-facet-value ,s1 ,fa 43 :kb ,kb :slot-type :own
     :inference-level :direct
     :value-selector :known-true :kb-local-only-p nil))
  
  (equal-sets?
   `(,c1 ,c2 ,c3 ,c4)
   `(get-frames-with-facet-value ,s1 ,fa 42 :kb ,kb :slot-type :template
     :inference-level :taxonomic
     :value-selector :known-true :kb-local-only-p nil))
  (equal-sets?
   `(,i1)
   `(get-frames-with-facet-value ,s1 ,fa 43 :kb ,kb :slot-type :own
     :inference-level :taxonomic
     :value-selector :known-true :kb-local-only-p nil))
  (equal-sets?
   `(,i1 ,i2, i3 ,i4)
   `(get-frames-with-facet-value ,s1 ,fa 42 :kb ,kb :slot-type :own
     :inference-level :taxonomic
     :value-selector :known-true :kb-local-only-p nil))
  (equal-sets?
   `(,c1 ,c2 ,c3 ,c4 ,i1 ,i2, i3 ,i4)
   `(get-frames-with-facet-value ,s1 ,fa 42 :kb ,kb :slot-type :all
     :inference-level :taxonomic
     :value-selector :known-true :kb-local-only-p nil))
  ;; Now do defaults
  (when (get-behavior-values :defaults)
	;; First test slots
	(equal-sets?
	 `(,c1)
	 `(get-frames-with-slot-value ,s2 42 :kb ,kb :slot-type :template
				      :inference-level :direct
				      :value-selector :default-only
				      :kb-local-only-p nil))
	(equal-sets?
	 `()
	 `(get-frames-with-slot-value ,s2 43 :kb ,kb :slot-type :own
				      :inference-level :direct
				      :value-selector :default-only
				      :kb-local-only-p nil))
	(equal-sets?
	 `(,c1)
	 `(get-frames-with-slot-value ,s2 42 :kb ,kb :slot-type :all
				      :inference-level :direct
				      :value-selector :default-only
				      :kb-local-only-p nil))
	(equal-sets?
	 `(,c1 ,c2 ,c3)
	 `(get-frames-with-slot-value ,s2 42 :kb ,kb :slot-type :template
				      :inference-level :taxonomic
				      :value-selector :default-only
				      :kb-local-only-p nil))
	(equal-sets?
	 `(,i1 ,i2 ,i3)
	 `(get-frames-with-slot-value ,s2 42 :kb ,kb :slot-type :own
				      :inference-level :taxonomic
				      :value-selector :default-only
				      :kb-local-only-p nil))
	(equal-sets?
	 `(,c1 ,c2 ,c3 ,i1 ,i2 ,i3)
	 `(get-frames-with-slot-value ,s2 42 :kb ,kb :slot-type :all
				      :inference-level :taxonomic
				      :value-selector :default-only
				      :kb-local-only-p nil))
	;; Now do facets
	(equal-sets?
	 `(,c1)
	 `(get-frames-with-facet-value ,s2 ,fa 42 :kb ,kb :slot-type :template
				       :inference-level :direct
				       :value-selector :default-only
				       :kb-local-only-p nil))
	(equal-sets?
	 `()
	 `(get-frames-with-facet-value ,s2 ,fa 43 :kb ,kb :slot-type :own
				       :inference-level :direct
				       :value-selector :default-only
				       :kb-local-only-p nil))
	(equal-sets?
	 `(,c1)
	 `(get-frames-with-facet-value ,s2 ,fa 42 :kb ,kb :slot-type :all
				       :inference-level :direct
				       :value-selector :default-only
				       :kb-local-only-p nil))
	(equal-sets?
	 `(,c1 ,c2 ,c3)
	 `(get-frames-with-facet-value ,s2 ,fa 42 :kb ,kb :slot-type :template
				       :inference-level :taxonomic
				       :value-selector :default-only
				       :kb-local-only-p nil))
	(equal-sets?
	 `(,i1 ,i2 ,i3)
	 `(get-frames-with-facet-value ,s2 ,fa 42 :kb ,kb :slot-type :own
				       :inference-level :taxonomic
				       :value-selector :default-only
				       :kb-local-only-p nil))
	(equal-sets?
	 `(,c1 ,c2 ,c3 ,i1 ,i2 ,i3)
	 `(get-frames-with-facet-value ,s2 ,fa 42 :kb ,kb :slot-type :all
				       :inference-level :taxonomic
				       :value-selector :default-only
				       :kb-local-only-p nil))))


;==============================================================================
; ======== Test harness for tell and ask
;==============================================================================

(defun test-tell-and-ask-on-its-own (kb-class &key
					      (initargs nil)
					      silent (creator nil))
  (let ((kb (if creator
		(funcall creator 'tell-and-ask)
		(create-kb 'tell-and-ask
			   :kb-type (get-kb-type kb-class)
			   :initargs initargs))))
    (goto-kb kb)
    (test-tell-and-ask kb (not silent))))

(defun test-tell-and-ask (kb verbose-p &optional (kb-local-only-p t))
  (let ((?class '?class)
	(?frame '?frame)
	(?slot '?slot)
	(?facet '?facet)
	(?value '?value)
	(?super '?super)
	(?sub '?sub)
	(?instance '?instance)
	(?individual '?individual)
	;;(kb-local-only-p t)
	(value-selector :known-true)
	(ask-result nil)
	(fact nil)
	(ts1 'ts1)
	(os2 'os2)
	(fa1 'fa1)
	(fa2 'f22)
	(c1 'c1)
	(c2 'c2)
	(c3 'c3)
	(c4 'c4)
	(c5 'c5)
	(i1 'i1)
	(i2 'i2)
	(i3 'i3)
	(i4 'i4)
	(ts1f nil)
	(os2f nil)
	(fa1f nil)
	(fa2f nil)
	(c1f nil)
	(c2f nil)
	(c3f nil)
	(c4f nil)
	(c5f nil)
	(i1f nil)
	(i2f nil)
	(i3f nil)
	(i4f nil)
	(query nil))
    (declare (special ?class ?frame ?slot ?facet ?value ?super ?sub ?instance
		      ?individual ts1 os2 fa1 fa2 c1 c2 c3 c4 c5 i1 i2 i3 i4
		      ts1f os2f fa1f fa2f c1f c2f c3f c4f c5f i1f i2f i3f i4f
		      query))
    ;; Test creation.
    ;; Classes
    (when verbose-p (format t "~%::: Testing tell and ask~%"))
    (tell (list :class c1) :frame nil :value-selector value-selector :kb kb
	  :kb-local-only-p kb-local-only-p)
    (setq c1f (get-unique-frame c1 kb))
    (test-true kb "class-p(c1)"
	       (class-p c1f :kb kb :kb-local-only-p kb-local-only-p)
	       verbose-p)
    (test-ask-against-pattern
     "Ask (:class c1f)" (list :class c1f)
     :value-selector value-selector :kb kb :kb-local-only-p kb-local-only-p
     :verbose-p verbose-p)

    (tell (list :and (list :class c2) (list :subclass-of c2 c1f))
	  :frame nil :value-selector value-selector :kb kb
	  :kb-local-only-p kb-local-only-p)
    (setq c2f (get-unique-frame c2 kb))
    (test-true kb "class-p(c2f)"
	       (class-p c2f :kb kb :kb-local-only-p kb-local-only-p)
	       verbose-p)
    (test-true kb "subclass-of-p(c2f c1f)" 
	       (subclass-of-p c2f c1f :inference-level :taxonomic :kb kb
			      :kb-local-only-p kb-local-only-p)
	       verbose-p)
    (test-ask-against-pattern "Ask (:class c2f)" (list :class c2f)
			      :value-selector value-selector :kb kb
			      :kb-local-only-p kb-local-only-p
			      :verbose-p verbose-p)

    (tell (list :and (list :class c3) (list :superclass-of c1f c3))
	  :frame nil :value-selector value-selector :kb kb :kb-local-only-p
	  kb-local-only-p)
    (setq c3f (get-unique-frame c3 kb))
    (test-true kb "class-p(c3f)"
	       (class-p c3f :kb kb :kb-local-only-p kb-local-only-p)
	       verbose-p)
    (test-true kb "(:subclass-of c3f c1f)" 
	       (subclass-of-p c3f c1f :inference-level :taxonomic :kb kb
			      :kb-local-only-p kb-local-only-p)
	       verbose-p)
    (test-ask-against-pattern "Ask (:class c3f)" (list :class c3f)
			      :value-selector value-selector :kb kb
			      :kb-local-only-p kb-local-only-p
			      :verbose-p verbose-p)

    (tell (list :and (list :class c4) (list :superclass-of c2f c4))
	  :frame nil :value-selector value-selector
	  :kb kb :kb-local-only-p kb-local-only-p)
    (setq c4f (get-unique-frame c4 kb))
    (test-true kb "class-p(c4f)"
	       (class-p c4f :kb kb :kb-local-only-p kb-local-only-p) verbose-p)
    (test-true kb "(:subclass-of c4f c1f)" 
	       (subclass-of-p c4f c1f :inference-level :taxonomic :kb kb
			      :kb-local-only-p kb-local-only-p)
	       verbose-p)
    (test-ask-against-pattern "Ask (:class c4f)" (list :class c4f)
			      :value-selector value-selector :kb kb
			      :kb-local-only-p kb-local-only-p
			      :verbose-p verbose-p)


    (setq ask-result (ask (setq query (list :subclass-of ?class c1f))
			  :reply-pattern ?class
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list c2f c3f c4f) 
		       "Ask (:subclass-of ?class c1f)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list :subclass-of ?class c1f))
			  :reply-pattern ?class
			  :inference-level :direct :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list c2f c3f) 
		       "Ask (:subclass-of ?class c1f) - direct"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list :superclass-of c1f ?class))
			  :reply-pattern ?class
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list c2f c3f c4f) 
		       "Ask (:superclass-of c1f ?class)"
		       ask-result verbose-p)

    (setq ask-result (ask (setq query (list :subclass-of c1f ?class))
			  :reply-pattern ?class
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-all-in-list kb '(:thing)
		      "Ask (:subclass-of c1f ?class)"
		      ask-result verbose-p)
    (setq ask-result (ask (setq query (list :superclass-of ?class c1f))
			  :reply-pattern ?class
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-all-in-list kb '(:thing)
		      "Ask (:superclass-of ?class c1f)"
		      ask-result verbose-p)

    (setq ask-result (ask (setq query (list :subclass-of ?class c2f))
			  :reply-pattern ?class
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list c4f) 
		       "Ask (:subclass-of ?class c2f)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list :superclass-of c2f ?class))
			  :reply-pattern ?class
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list c4f)
		       "Ask (:superclass-of c2f ?class)"
		       ask-result verbose-p)

    (setq ask-result (ask (setq query (list :subclass-of c2f ?class))
			  :reply-pattern ?class
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-all-in-list kb (list c1f :thing)
		      "Ask (:subclass-of c2f ?class)"
		      ask-result verbose-p)
    (setq ask-result (ask (setq query (list :superclass-of ?class c2f))
			  :reply-pattern ?class
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-all-in-list kb (list c1f :thing)
		      "Ask (:superclass-of ?class c2f)"
		      ask-result verbose-p)

    (setq ask-result (ask (setq query (list :superclass-of ?super ?sub))
			  :reply-pattern (list ?sub ?super)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-at-least kb (list (list c2f c1f)
			    (list c3f c1f)
			    (list c4f c1f)
			    (list c4f c2f))
		  "Ask (:superclass-of ?sub ?super)"
		  ask-result verbose-p)

    ;; Now test to get all classes.
    (setq ask-result (ask (setq query (list :class ?class))
			  :reply-pattern ?class
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-at-least kb (list c1f c2f c3f c4f :class) "Ask (:class ?class)"
		   (cons :class ask-result) verbose-p)

    ;; Individuals
    (tell (list :and (list :individual i1) (list :instance-of i1 c1f))
	  :frame nil :value-selector value-selector :kb kb
	  :kb-local-only-p kb-local-only-p)
    (setq i1f (get-unique-frame i1 kb))
    (test-true kb "individual-p(i1f)"
	       (individual-p i1f :kb kb :kb-local-only-p kb-local-only-p)
	       verbose-p)
    (test-true kb "instance-of-p(i1f c1f)" 
	       (instance-of-p i1f c1f :inference-level :taxonomic :kb kb
			      :kb-local-only-p kb-local-only-p)
	       verbose-p)
    (test-ask-against-pattern
     "Ask (:individual i1f)" (list :individual i1f)
     :value-selector value-selector :kb kb :kb-local-only-p kb-local-only-p
     :verbose-p verbose-p)

    (tell (list :and (list :individual i2) (list :type-of c2f i2))
	  :frame nil :value-selector value-selector :kb kb
	  :kb-local-only-p kb-local-only-p)
    (setq i2f (get-unique-frame i2 kb))
    (test-true kb "(individual-p(i2f)"
	       (individual-p i2f :kb kb :kb-local-only-p kb-local-only-p)
	       verbose-p)
    (test-true kb "instance-of-p(i2f c2f)" 
	       (instance-of-p i2f c2f :inference-level :taxonomic :kb kb
			      :kb-local-only-p kb-local-only-p)
	       verbose-p)
    (test-ask-against-pattern
     "Ask (:individual i2f)" (list :individual i2f)
     :value-selector value-selector :kb kb :kb-local-only-p kb-local-only-p
     :verbose-p verbose-p)

    (tell (list :and (list :individual i3) (list :instance-of i3 c3f))
	  :frame nil :value-selector value-selector :kb kb
	  :kb-local-only-p kb-local-only-p)
    (setq i3f (get-unique-frame i3 kb))
    (test-true kb "individual-p(i3f)"
	       (individual-p i3f :kb kb :kb-local-only-p kb-local-only-p)
	       verbose-p)
    (test-true kb "instance-of-pi3f c3f)" 
	       (instance-of-p i3f c3f :inference-level :taxonomic :kb kb
			      :kb-local-only-p kb-local-only-p)
	       verbose-p)
    (test-ask-against-pattern
     "Ask (:individual i3f)" (list :individual i3f)
     :value-selector value-selector :kb kb :kb-local-only-p kb-local-only-p
     :verbose-p verbose-p)

    (tell (list :and (list :individual i4) (list :type-of c4f i4))
	  :frame nil :value-selector value-selector :kb kb
	  :kb-local-only-p kb-local-only-p)
    (setq i4f (get-unique-frame i4 kb))
    (test-true kb "individual-p(i4f)"
	       (individual-p i4f :kb kb :kb-local-only-p kb-local-only-p)
	       verbose-p)
    (test-true kb "instance-of-p(i4f c4f)" 
	       (instance-of-p i4f c4f :inference-level :taxonomic :kb kb
			      :kb-local-only-p kb-local-only-p)
	       verbose-p)
    (test-ask-against-pattern
     "Ask (:individual i4f)" (list :individual i4f)
     :value-selector value-selector :kb kb :kb-local-only-p kb-local-only-p
     :verbose-p verbose-p)

    
    (setq ask-result (ask (setq query (list :instance-of ?frame c1f))
			  :reply-pattern ?frame
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list i1f i2f i3f i4f) 
		       "Ask (:instance-of ?frame c1f)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list :type-of c1f ?frame))
			  :reply-pattern ?frame
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list i1f i2f i3f i4f) 
		       "Ask (:type-of c1f ?frame)"
		       ask-result verbose-p)

    (setq ask-result (ask (setq query (list :instance-of c1f ?class))
			  :reply-pattern ?class
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-at-least kb '(:class :primitive)
		       "Ask (:instance-of c1f ?class)"
		       (append '(:class :primitive) ask-result) verbose-p)
    (setq ask-result (ask (setq query (list :type-of ?class c1f))
			  :reply-pattern ?class
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-at-least kb '(:class :primitive)
		       "Ask (:type-of ?class c1f)"
		       (append '(:class :primitive) ask-result) verbose-p)


    (setq ask-result (ask (setq query (list :instance-of ?frame c2f))
			  :reply-pattern ?frame
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list i2f i4f) 
		       "Ask (:instance-of ?frame c2f)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list :type-of c2f ?frame))
			  :reply-pattern ?frame
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list i2f i4f)
		       "Ask (:type-of c2f ?frame)"
		       ask-result verbose-p)

    (setq ask-result (ask (setq query (list :instance-of c2f ?class))
			  :reply-pattern ?class
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-at-least kb '(:class :primitive)
		       "Ask (:instance-of c2f ?class)"
		       (append '(:class :primitive) ask-result) verbose-p)
    (setq ask-result (ask (setq query (list :type-of ?class c2f))
			  :reply-pattern ?class
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-at-least kb '(:class :primitive)
		       "Ask (:type-of ?class c2f)"
		       (append '(:class :primitive) ask-result) verbose-p)

    (setq ask-result (ask (setq query (list :type-of ?class ?instance))
			  :reply-pattern (list ?instance ?class)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-at-least kb (list (list i1f c1f)
			    (list i2f c1f)
			    (list i3f c1f)
			    (list i4f c1f)

			    (list i2f c2f)
			    (list i4f c2f)

			    (list i3f c3f)
			    (list i4f c4f))
		   "Ask (:type-of ?class ?instance)"
		   ask-result verbose-p)

    ;; Now test to get all individuals.
    (setq ask-result (ask (setq query (list :individual ?individual))
			  :reply-pattern ?individual
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-at-least kb (list i1f i2f i3f i4f) 
		   "Ask (:individual ?individual)"
		   ask-result verbose-p)

    ;; Now test frame properties
    (setq ask-result (ask (setq query (list :name c2f ?value))
			  :reply-pattern ?value
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal kb "Ask (:name c2f ?value)" ask-result (list c2)
		  verbose-p)
    (setq ask-result (ask (setq query (list :name ?class 'c2))
			  :reply-pattern ?class
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal kb "Ask (:name ?frame c2f)" ask-result (list c2f)
		  verbose-p)
    (setq ask-result (ask (setq query (list :name ?frame ?value))
			  :reply-pattern (list ?frame ?value)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-at-least kb (list (list c1f c1)
			    (list c2f c2)
			    (list c3f c3)
			    (list c4f c4)
			    (list i1f i1)
			    (list i2f i2)
			    (list i3f i3)
			    (list i4f i4))
		   "Ask (:name ?frame ?value)"
		   ask-result verbose-p)
    (setq ask-result (ask (setq query (list :pretty-name c2f ?value))
			  :reply-pattern ?value
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal kb "Ask (:pretty-name c2f ?value)"
		  ask-result
		  (list (get-frame-pretty-name
			 c2f :kb kb :kb-local-only-p kb-local-only-p))
		  verbose-p)
    (setq ask-result (ask (setq query (list :handle c2f ?value))
			  :reply-pattern ?value
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal kb "Ask (:handle c2f ?value)"
		  ask-result
		  (list (get-frame-handle
			 c2f :kb kb :kb-local-only-p kb-local-only-p))
		  verbose-p)

    (tell (list :name c2f 'c2-alternate-name)
          :frame nil :value-selector value-selector
	  :kb kb :kb-local-only-p kb-local-only-p)
    (test-equal kb "get-frame-name(c2f) = c2-altername-name"
		  'c2-alternate-name
		  (get-frame-name c2f :kb kb :kb-local-only-p kb-local-only-p)
		  verbose-p)
    (setq ask-result (ask (setq query (list :name c2f ?value))
			  :reply-pattern ?value
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal kb "Ask (:name c2 ?value)"
		  ask-result
		  (list (get-frame-name
			 c2f :kb kb :kb-local-only-p kb-local-only-p))
		  verbose-p)
    (tell (list :name c2f c2) :frame nil :value-selector value-selector
	  :kb kb :kb-local-only-p kb-local-only-p)
    (setq ask-result (ask (setq query (list :name c2f ?value))
			  :reply-pattern ?value
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal kb "get-frame-name(c2f) = c2"
		  c2
		  (get-frame-name c2f :kb kb :kb-local-only-p kb-local-only-p)
		  verbose-p)
    (test-equal kb "Ask (:name c2f ?value)"
		  ask-result
		  (list (get-frame-name
			 c2f :kb kb :kb-local-only-p kb-local-only-p))
		  verbose-p)



    (let ((c2-pretty-name "C2's pretty name"))
      (tell (list :pretty-name c2f c2-pretty-name) :frame nil 
	    :value-selector value-selector :kb kb
	    :kb-local-only-p kb-local-only-p)
      (setq ask-result (ask (setq query (list :pretty-name c2f ?value))
			    :reply-pattern ?value
			    :inference-level :taxonomic :number-of-values
			    :all :value-selector value-selector
			    :kb kb :kb-local-only-p kb-local-only-p))
      (test-equal kb "get-frame-pretty-name(c2f)"
		  c2-pretty-name
		  (get-frame-pretty-name
		   c2f :kb kb :kb-local-only-p kb-local-only-p)
		  verbose-p)
      (test-equal kb "Ask (:pretty-name c2f ?value)"
		  ask-result
		  (list (get-frame-pretty-name
			 c2f :kb kb :kb-local-only-p kb-local-only-p))
		  verbose-p))


    ;; Slots
    (tell (list :and (list :slot ts1) (list :template-slot-of ts1 c1f))
	  :frame nil :value-selector value-selector
	  :kb kb :kb-local-only-p kb-local-only-p)
    (setq ts1f (get-unique-frame ts1 kb))
    (test-true kb "slot-p(ts1f)"
	       (slot-p ts1f :kb kb :kb-local-only-p kb-local-only-p)
	       verbose-p)
    (test-true kb "frame-has-slot-p(c1f ts1f template)" 
	       (frame-has-slot-p c1f ts1f :inference-level :taxonomic
				 :slot-type :template
				 :kb kb :kb-local-only-p kb-local-only-p)
	       verbose-p)
    (test-ask-against-pattern
     "Ask (:slot ts1)" (list :slot ts1f)
     :value-selector value-selector :kb kb :kb-local-only-p kb-local-only-p
     :verbose-p verbose-p)
    (setq ask-result (ask (setq query (list :template-slot-of ts1f ?class))
			  :reply-pattern ?class
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list c1f c2f c3f c4f) 
		       "Ask (:slot-type :template-slot-of ts1f ?class)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list :template-slot-of ?slot c2f))
			  :reply-pattern ?slot
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list ts1f) 
		       "Ask (:slot-type :template-slot-of ?slot c2f)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list :template-slot-of ?slot ?class))
			  :reply-pattern (list ?class ?slot)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list c1f ts1f)
			     (list c2f ts1f)
			     (list c3f ts1f)
			     (list c4f ts1f))
		       "Ask (:slot-type :template-slot-of ?slot ?class)"
		       ask-result verbose-p)

    ;; Own slots
    (tell (list :and (list :slot os2) (list :slot-of os2 c2f))
	  :frame nil :value-selector value-selector
	  :kb kb :kb-local-only-p kb-local-only-p)
    (setq os2f (get-unique-frame os2 kb))
    (test-true kb "slot-p(os2f)"
	       (slot-p os2f :kb kb :kb-local-only-p kb-local-only-p)
	       verbose-p)
    (test-true kb "frame-has-slot-p(c2f os2f :slot-type :own)" 
	       (frame-has-slot-p c2f os2f :inference-level :taxonomic
				 :slot-type :own
				 :kb kb :kb-local-only-p kb-local-only-p)
	       verbose-p)
    (test-ask-against-pattern
     "Ask (:slot os2)" (list :slot os2f)
     :value-selector value-selector :kb kb :kb-local-only-p kb-local-only-p
     :verbose-p verbose-p)
    (setq ask-result (ask (setq query (list :slot-of os2f ?frame))
			  :reply-pattern ?frame
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list c2f) 
		       "Ask (:slot-of os2f ?frame)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list :slot-of ?slot c2f))
			  :reply-pattern ?slot
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-at-least kb (list os2f) 
		       "Ask (:slot-of ?slot c2f)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list :slot-of ?slot ?frame))
			  :reply-pattern (list ?frame ?slot)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-at-least kb (list (list c2f os2f)
			    (list i1f ts1f)
			    (list i2f ts1f)
			    (list i3f ts1f)
			    (list i4f ts1f))
		   "Ask (:slot-of ?slot ?frame)"
		   ask-result verbose-p)


    ;; Facets
    ;; Template Facets
    (tell (list :and (list :facet fa1) (list :template-facet-of fa1 ts1f c1f))
	  :frame nil :value-selector value-selector
    :kb kb :kb-local-only-p kb-local-only-p)
    (setq fa1f (get-unique-frame fa1 kb))
    (test-true kb "facet-p(fa11f)"
	       (facet-p fa1f :kb kb :kb-local-only-p kb-local-only-p)
	       verbose-p)
    (test-true kb "slot-has-facet-p(c1f ts1f fa1f template)" 
	       (slot-has-facet-p c1f ts1f fa1f
				 :inference-level :taxonomic
				 :slot-type :template
				 :kb kb :kb-local-only-p kb-local-only-p)
	       verbose-p)
    (test-ask-against-pattern
     "Ask (:facet fa1f)" (list :facet fa1f)
     :value-selector value-selector :kb kb :kb-local-only-p kb-local-only-p
     :verbose-p verbose-p)
    (setq ask-result (ask (setq query
				(list :template-facet-of fa1f ts1f ?class))
			  :reply-pattern ?class
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list c1f c2f c3f c4f) 
		       "Ask (:slot-type :template-facet-of fa1f ts1f ?class)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list :template-facet-of fa1f ?slot c2f))
			  :reply-pattern ?slot
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list ts1f) 
		       "Ask (:slot-type :template-facet-of fa1f ?slot c2f)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query
				(list :template-facet-of ?facet ts1f c2f))
			  :reply-pattern ?facet
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list fa1f) 
		       "Ask (:slot-type :template-facet-of ?facet ts1f c2f)"
		       ask-result verbose-p)

    (setq ask-result (ask (setq query
				(list :template-facet-of fa1f ?slot ?class))
			  :reply-pattern (list ?class ?slot)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list c1f ts1f)
			     (list c2f ts1f)
			     (list c3f ts1f)
			     (list c4f ts1f))
		       "Ask (:slot-type :template-facet-of fa1f ?slot ?class)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list :template-facet-of ?facet ts1f 
					    ?class))
			  :reply-pattern (list ?class ?facet)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list c1f fa1f)
			     (list c2f fa1f)
			     (list c3f fa1f)
			     (list c4f fa1f))
		       "Ask (:slot-type :template-facet-of ?facet ts1f ?class)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list :template-facet-of ?facet ?slot 
					    c1f))
			  :reply-pattern (list ?slot ?facet)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list ts1f fa1f))
		       "Ask (:slot-type :template-facet-of ?facet ?slot c1f)"
		       ask-result verbose-p)

    (setq ask-result (ask (setq query (list :template-facet-of ?facet ?slot
					    ?class))
			  :reply-pattern (list ?class ?slot ?facet)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list c1f ts1f fa1f)
			      (list c2f ts1f fa1f)
			      (list c3f ts1f fa1f)
			      (list c4f ts1f fa1f))
		     "Ask (:slot-type :template-facet-of ?facet ?slot ?class)"
		     ask-result verbose-p)

    ;; Own facets
    (tell (list :and (list :facet fa2) (list :facet-of fa2 os2f c2f))
	  :frame nil :value-selector value-selector :kb kb
	  :kb-local-only-p kb-local-only-p)
    (setq fa2f (get-unique-frame fa2 kb))
    (test-true kb "facet-p(fa21f)"
	       (facet-p fa2f :kb kb :kb-local-only-p kb-local-only-p)
	       verbose-p)
    (test-true kb "slot-has-facet-p(c2f os2f fa2f :slot-type :own)" 
	       (slot-has-facet-p
		c2f os2f fa2f :inference-level :taxonomic :slot-type :own
		:kb kb :kb-local-only-p kb-local-only-p)
	       verbose-p)
    (test-ask-against-pattern
     "Ask (:facet fa2f)" (list :facet fa2f)
     :value-selector value-selector :kb kb :kb-local-only-p kb-local-only-p
     :verbose-p verbose-p)
    (setq ask-result (ask (setq query (list :facet-of fa2f os2f ?frame))
			  :reply-pattern ?frame
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list c2f) 
		       "Ask (:facet-of fa2f os2f ?class)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list :facet-of fa2f ?slot c2f))
			  :reply-pattern ?slot
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list os2f) 
		       "Ask (:facet-of fa2f ?slot c2f)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list :facet-of ?facet os2f c2f))
			  :reply-pattern ?facet
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list fa2f) 
		       "Ask (:facet-of ?facet os2f c2f)"
		       ask-result verbose-p)

    (setq ask-result (ask (setq query (list :facet-of fa2f ?slot ?frame))
			  :reply-pattern (list ?frame ?slot)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list c2f os2f))
		       "Ask (:facet-of fa2f ?slot ?class)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list :facet-of ?facet os2f ?frame))
			  :reply-pattern (list ?frame ?facet)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list c2f fa2f))
		       "Ask (:facet-of ?facet os2f ?class)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list :facet-of ?facet ?slot c2f))
			  :reply-pattern (list ?slot ?facet)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list os2f fa2f))
		       "Ask (:facet-of ?facet ?slot c2f)"
		       ask-result verbose-p)

    (setq ask-result (ask (setq query (list :facet-of ?facet ?slot ?frame))
			  :reply-pattern (list ?frame ?slot ?facet)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list c2f os2f fa2f)
			     (list i1f ts1f fa1f)
			     (list i2f ts1f fa1f)
			     (list i3f ts1f fa1f)
			     (list i4f ts1f fa1f))
		       "Ask (:facet-of ?facet ?slot ?class)"
		       ask-result verbose-p)


    ;; Slot values
    ;; Template slots
    (tell (list :template-slot-value ts1f c1f 1)
	  :frame nil :value-selector value-selector :kb kb
	  :kb-local-only-p kb-local-only-p)
    (test-true kb "member-slot-value-p(c1f ts1f 1 template)"
	       (member-slot-value-p
		c1f ts1f 1 :inference-level :taxonomic :test :equal
		:slot-type :template :value-selector value-selector 
		:kb kb :kb-local-only-p kb-local-only-p)
	       verbose-p)
    (test-equal kb "get-slot-values(c1f ts1f template)"
		(get-slot-values c1f ts1f :inference-level :taxonomic
				 :slot-type :template :number-of-values :all
				 :value-selector value-selector 
				 :kb kb :kb-local-only-p kb-local-only-p)
		  (list 1) verbose-p)
    (setq ask-result (ask (setq query (list :template-slot-value ts1f c1f 1))
			  :reply-pattern ?class
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-true kb "Ask (:slot-type :template-slot-value ts1f c1f 1)"
	       ask-result verbose-p)
    (setq ask-result (ask (setq query
				(list :template-slot-value ts1f c1f ?value))
			  :reply-pattern ?value
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list 1) 
		       "Ask (:slot-type :template-slot-value ts1f c1f ?v)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query
				(list :template-slot-value ts1f ?class 1))
			  :reply-pattern ?class
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list c1f c2f c3f c4f) 
		       "Ask (:slot-type :template-slot-value ts1f ?class 1)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list :template-slot-value ?slot c1f 1))
			  :reply-pattern ?slot
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list ts1f) 
		       "Ask (:slot-type :template-slot-value ?slot c1f 1)"
		       ask-result verbose-p)

    (setq ask-result (ask (setq query (list :template-slot-value ts1f ?class
					    ?value))
			  :reply-pattern (list ?class ?value)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list c1f 1)
			     (list c2f 1)
			     (list c3f 1)
			     (list c4f 1))
		       "Ask (:slot-type :template-slot-value ts1f ?class ?v)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list :template-slot-value ?slot c1f
					    ?value))
			  :reply-pattern (list ?slot ?value)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list ts1f 1))
		       "Ask (:slot-type :template-slot-value ?slot c1f ?v)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list :template-slot-value ?slot ?class
					    1))
			  :reply-pattern (list ?slot ?class)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list ts1f c1f)
			     (list ts1f c2f)
			     (list ts1f c3f)
			     (list ts1f c4f))
		       "Ask (:slot-type :template-slot-value ?slot ?class 1)"
		       ask-result verbose-p)

    (setq ask-result (ask (setq query (list :template-slot-value ?slot ?class
					    ?value))
			  :reply-pattern (list ?slot ?class ?value)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets
     kb (list (list ts1f c1f 1)
	      (list ts1f c2f 1)
	      (list ts1f c3f 1)
	      (list ts1f c4f 1))
     "Ask (:slot-type :template-slot-value ?slot ?class ?value)"
     ask-result verbose-p)


    ;; Own slots
    (tell (list os2f c2f 3)
	  :frame nil :value-selector value-selector :kb kb
	  :kb-local-only-p kb-local-only-p)
    (test-true kb "member-slot-value-p(c2f os2f 3 :slot-type :own)"
	       (member-slot-value-p
		c2f os2f 3 :inference-level :taxonomic :test :equal
		:slot-type :own :value-selector value-selector 
		:kb kb :kb-local-only-p kb-local-only-p)
	       verbose-p)
    (test-equal kb "get-slot-values(c2f os2f :slot-type :own)"
		(get-slot-values
		 c2f os2f :inference-level :taxonomic
		 :slot-type :own :number-of-values :all
		 :value-selector value-selector 
		 :kb kb :kb-local-only-p kb-local-only-p)
		  (list 3) verbose-p)
    (setq ask-result (ask (setq query (list os2f c2f 3))
			  :reply-pattern ?frame
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-true kb "(Ask os2f c2f 3)" ask-result verbose-p)
    (setq ask-result (ask (setq query (list os2f c2f ?value))
			  :reply-pattern ?value
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list 3) 
		       "(Ask os2f c2f ?v)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list os2f ?frame 3))
			  :reply-pattern ?frame
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list c2f) 
		       "(Ask os2f ?class 3)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list :holds ?slot c2f 3))
			  :reply-pattern ?slot
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list os2f) 
		       "(Ask :holds ?slot c2f 3)"
		       ask-result verbose-p)

    (setq ask-result (ask (setq query (list os2f ?frame ?value))
			  :reply-pattern (list ?frame ?value)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list c2f 3))
		       "(Ask os2f ?class ?v)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list :holds ?slot c2f ?value))
			  :reply-pattern (list ?slot ?value)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-at-least kb (list (list os2f 3))
		   "(Ask :holds ?slot c2f ?v)"
		   ask-result verbose-p)
    (setq ask-result (ask (setq query (list :holds ?slot ?frame 3))
			  :reply-pattern (list ?slot ?frame)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-at-least kb (list (list os2f c2f))
		   "(Ask :holds ?slot ?frame 3)"
		   ask-result verbose-p)

    ;; Now all 3 as vars.
    (setq ask-result (ask (setq query (list :holds ?slot ?frame ?value))
			  :reply-pattern (list ?slot ?frame ?value)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-at-least kb (list (list os2f c2f 3)
			    (list ts1f i1f 1)
			    (list ts1f i2f 1)
			    (list ts1f i3f 1)
			    (list ts1f i4f 1))
		   "(Ask :holds ?slot ?class ?value)"
		   ask-result verbose-p)

    ;; Now all 3 as vars with holds.
    (setq ask-result (ask (setq query (list :holds ?slot ?frame ?value))
			  :reply-pattern (list ?slot ?frame ?value)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-at-least kb (list (list os2f c2f 3)
			    (list ts1f i1f 1)
			    (list ts1f i2f 1)
			    (list ts1f i3f 1)
			    (list ts1f i4f 1))
		   "Ask (:holds ?slot ?class ?value)"
		   ask-result verbose-p)


    ;; Facet values
    ;; Template facets
    (tell (list :template-facet-value fa1f ts1f c1f 1)
	  :frame nil :value-selector value-selector :kb kb
	  :kb-local-only-p kb-local-only-p)
    (test-true kb "member-facet-value-p(c1f ts1f fa1f 1 template)"
	       (member-facet-value-p
		c1f ts1f fa1f 1 :inference-level :taxonomic :test :equal
		:slot-type :template :value-selector value-selector 
		:kb kb :kb-local-only-p kb-local-only-p)
	       verbose-p)
    (test-equal kb "get-facet-values(c1f ts1f fa1f template)"
		(get-facet-values
		 c1f ts1f fa1f :inference-level :taxonomic
		 :slot-type :template :number-of-values :all
		 :value-selector value-selector 
		 :kb kb :kb-local-only-p kb-local-only-p)
		  (list 1) verbose-p)
    (setq ask-result (ask (setq query
				(list :template-facet-value fa1f ts1f c1f 1))
			  :reply-pattern ?class
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-true kb "Ask (:template-facet-value fa1f ts1f c1f 1)"
	       ask-result verbose-p)
    ;; Test combinations with 1 var
    (setq ask-result (ask (setq query (list :template-facet-value fa1f ts1f c1f
					    ?value))
			  :reply-pattern ?value
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list 1) 
		       "Ask (:template-facet-value fa1f ts1f c1f ?v)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list :template-facet-value fa1f ts1f 
					    ?class 1))
			  :reply-pattern ?class
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list c1f c2f c3f c4f) 
		       "Ask (:template-facet-value fa1f ts1f ?class 1)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query
				(list :template-facet-value fa1f ?slot c1f 1))
			  :reply-pattern ?slot
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list ts1f) 
		       "Ask (:template-facet-value fa1f ?slot c1f 1)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list :template-facet-value ?facet
					    ts1f c1f 1))
			  :reply-pattern ?facet
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list fa1f) 
		       "Ask (:template-facet-value ?facet ts1f c1f 1)"
		       ask-result verbose-p)

    ;; Test combinations with 2.0 vars
    ;; Loop over Value
    (setq ask-result (ask (setq query (list :template-facet-value fa1f ts1f
					    ?class ?value))
			  :reply-pattern (list ?class ?value)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list c1f 1)
			     (list c2f 1)
			     (list c3f 1)
			     (list c4f 1))
		       "Ask (:template-facet-value fa1f ts1f ?class ?v)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query
				(list :template-facet-value fa1f ?slot c1f
				      ?value))
			  :reply-pattern (list ?slot ?value)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list ts1f 1))
		       "Ask (:template-facet-value fa1f ?slot c1f ?v)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list :template-facet-value ?facet ts1f
					    c1f ?value))
			  :reply-pattern (list ?facet ?value)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list fa1f 1))
		       "Ask (:template-facet-value ?facet ts1f c1f ?v)"
		       ask-result verbose-p)
    ;; Loop over Class
    (setq ask-result (ask (setq query (list :template-facet-value fa1f ?slot
					    ?class 1))
			  :reply-pattern (list ?slot ?class)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list ts1f c1f)
			     (list ts1f c2f)
			     (list ts1f c3f)
			     (list ts1f c4f))
		       "Ask (:template-facet-value fa1f ?slot ?class 1)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list :template-facet-value ?facet ts1f
					    ?class 1))
			  :reply-pattern (list ?facet ?class)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list fa1f c1f)
			     (list fa1f c2f)
			     (list fa1f c3f)
			     (list fa1f c4f))
		       "Ask (:template-facet-value ?facet ts1f ?class 1)"
		       ask-result verbose-p)
    ;; Loop over slot
    (setq ask-result (ask (setq query (list :template-facet-value ?facet
					    ?slot c1f 1))
			  :reply-pattern (list ?facet ?slot)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list fa1f ts1f))
		       "Ask (:template-facet-value ?facet ?slot c1f 1)"
		       ask-result verbose-p)

    ;; Now groups of 3 vars
    (setq ask-result (ask (setq query (list :template-facet-value fa1f ?slot
					    ?class ?value))
			  :reply-pattern (list ?slot ?class ?value)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list ts1f c1f 1)
			     (list ts1f c2f 1)
			     (list ts1f c3f 1)
			     (list ts1f c4f 1))
		       "Ask (:template-facet-value fa1f ?slot ?class ?value)"
		       ask-result verbose-p)

    (setq ask-result (ask (setq query (list :template-facet-value ?facet ts1f
					    ?class ?value))
			  :reply-pattern (list ?facet ?class ?value)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list fa1f c1f 1)
			     (list fa1f c2f 1)
			     (list fa1f c3f 1)
			     (list fa1f c4f 1))
		       "Ask (:template-facet-value ?facet ts1f ?class ?value)"
		       ask-result verbose-p)

    (setq ask-result (ask (setq query (list :template-facet-value ?facet 
					    ?slot c1f ?value))
			  :reply-pattern (list ?facet ?slot ?value)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list fa1f ts1f 1))
		       "Ask (:template-facet-value ?facet ?slot c1f ?value)"
		       ask-result verbose-p)

    (setq ask-result (ask (setq query (list :template-facet-value ?facet 
					    ?slot ?class 1))
			  :reply-pattern (list ?facet ?slot ?class)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list fa1f ts1f c1f)
			     (list fa1f ts1f c2f)
			     (list fa1f ts1f c3f)
			     (list fa1f ts1f c4f))
		       "Ask (:template-facet-value ?facet ?slot ?class 1)"
		       ask-result verbose-p)

    ;; Now all four as vars.
    (setq ask-result (ask (setq query (list :template-facet-value ?facet 
					    ?slot ?class ?value))
			  :reply-pattern (list ?facet ?slot ?class
				?value)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list fa1f ts1f c1f 1)
			     (list fa1f ts1f c2f 1)
			     (list fa1f ts1f c3f 1)
			     (list fa1f ts1f c4f 1))
		       "Ask (:template-facet-value ?facet ?slot ?class ?value)"
		       ask-result verbose-p)

    ;; Own facets
    (tell (list fa2f os2f c2f 3)
	  :frame nil :value-selector value-selector :kb kb
	  :kb-local-only-p kb-local-only-p)
    (test-true kb "member-facet-value-p(c2f os2f fa2f 1 :slot-type :own)"
	       (member-facet-value-p
		c2f os2f fa2f 3 :inference-level :taxonomic
		:test :equal :slot-type :own :value-selector value-selector 
		:kb kb :kb-local-only-p kb-local-only-p)
	       verbose-p)
    (test-equal kb "get-facet-values(c2f os2f fa2f :slot-type :own)"
		(get-facet-values
		 c2f os2f fa2f :inference-level :taxonomic
		 :slot-type :own :number-of-values :all
		 :value-selector value-selector 
		 :kb kb :kb-local-only-p kb-local-only-p)
		  (list 3) verbose-p)
    (setq ask-result (ask (setq query (list fa2f os2f c2f 3))
			  :reply-pattern ?frame
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-true kb "(Ask fa2f os2f c2f 3)"
	       ask-result verbose-p)
    ;; Test combinations with 3 var
    (setq ask-result (ask (setq query (list fa2f os2f c2f ?value))
			  :reply-pattern ?value
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list 3) 
		       "(Ask fa2f os2f c2f ?v)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list fa2f os2f ?frame 3))
			  :reply-pattern ?frame
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list c2f) 
		       "(Ask fa2f os2f ?frame 3)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list fa2f ?slot c2f 3))
			  :reply-pattern ?slot
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list os2f) 
		       "(Ask fa2f ?slot c2f 3)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list :holds ?facet os2f c2f 3))
			  :reply-pattern ?facet
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list fa2f) 
		       "(Ask :holds ?facet os2f c2f 3)"
		       ask-result verbose-p)

    ;; Test combinations with 2.0 vars
    ;; Loop over Value
    (setq ask-result (ask (setq query (list fa2f os2f ?frame ?value))
			  :reply-pattern (list ?frame ?value)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list c2f 3))
		       "(Ask fa2f os2f ?frame ?v)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list fa2f ?slot c2f ?value))
			  :reply-pattern (list ?slot ?value)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list os2f 3))
		       "(Ask fa2f ?slot c2f ?v)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list :holds ?facet os2f c2f ?value))
			  :reply-pattern (list ?facet ?value)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list fa2f 3))
		       "(Ask :holds ?facet os2f c2f ?v)"
		       ask-result verbose-p)
    ;; Loop over Frame
    (setq ask-result (ask (setq query (list fa2f ?slot ?frame 3))
			  :reply-pattern (list ?slot ?frame)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list os2f c2f))
		       "(Ask fa2f ?slot ?frame 3)"
		       ask-result verbose-p)
    (setq ask-result (ask (setq query (list :holds ?facet os2f ?frame 3))
			  :reply-pattern (list ?facet ?frame)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list fa2f c2f))
		       "(Ask :holds ?facet os2f ?frame 3)"
		       ask-result verbose-p)
    ;; Loop over slot
    (setq ask-result (ask (setq query (list :holds ?facet ?slot c2f 3))
			  :reply-pattern (list ?facet ?slot)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list fa2f os2f))
		       "(Ask :holds ?facet ?slot c2f 3)"
		       ask-result verbose-p)

    ;; Now groups of 3 vars
    (setq ask-result (ask (setq query (list fa2f ?slot ?frame ?value))
			  :reply-pattern (list ?slot ?frame ?value)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list os2f c2f 3))
		       "(Ask fa2f ?slot ?frame ?value)"
		       ask-result verbose-p)

    (setq ask-result (ask (setq query (list :holds ?facet os2f ?frame ?value))
			  :reply-pattern (list ?facet ?frame ?value)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list fa2f c2f 3))
		       "(Ask :holds ?facet os2f ?frame ?value)"
		       ask-result verbose-p)

    (setq ask-result (ask (setq query (list :holds ?facet ?slot c2f ?value))
			  :reply-pattern (list ?facet ?slot ?value)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list fa2f os2f 3))
		       "(Ask :holds ?facet ?slot c2f ?value)"
		       ask-result verbose-p)

    (setq ask-result (ask (setq query (list :holds ?facet ?slot ?frame 3))
			  :reply-pattern (list ?facet ?slot ?frame)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list fa2f os2f c2f))
		       "(Ask :holds ?facet ?slot ?frame 3)"
		       ask-result verbose-p)

    ;; Now all four as vars.
    (setq ask-result (ask (setq query (list :holds ?facet ?slot ?frame ?value))
			  :reply-pattern (list ?facet ?slot ?frame
					       ?value)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list fa2f os2f c2f 3)
			     (list fa1f ts1f i1f 1)
			     (list fa1f ts1f i2f 1)
			     (list fa1f ts1f i3f 1)
			     (list fa1f ts1f i4f 1))
		       "(Ask :holds ?facet ?slot ?frame ?value)"
		       ask-result verbose-p)

    ;; Now all four as vars with holds.
    (setq ask-result (ask (setq query (list :holds ?facet 
					    ?slot ?frame ?value))
			  :reply-pattern (list ?facet ?slot ?frame
				?value)
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-equal-sets kb (list (list fa2f os2f c2f 3)
			      (list fa1f ts1f i1f 1)
			      (list fa1f ts1f i2f 1)
			      (list fa1f ts1f i3f 1)
			      (list fa1f ts1f i4f 1))
		     "Ask (:holds ?facet ?slot ?frame ?value)"
		     ask-result verbose-p)


    ;; Test primitivity.
    (setq c5f (create-pretty-frame c5 :class :direct-superclasses c4f
				   :primitive-p nil
				   :kb kb :kb-local-only-p kb-local-only-p))
    (test-true kb "primitive-p(c1f)"
	       (primitive-p c1f :kb kb :kb-local-only-p kb-local-only-p)
	       verbose-p)
    (test-false kb "primitive-p(c5f)"
		(primitive-p c5f :kb kb :kb-local-only-p kb-local-only-p)
		verbose-p)
    (test-ask-against-pattern "Ask (:primitive c1f)" 
			      (list :primitive c1f)
			      :value-selector value-selector :kb kb
			      :kb-local-only-p kb-local-only-p
			      :verbose-p verbose-p)
    (test-ask-against-pattern-not "Ask (:primitive c5f)"
				  (list :primitive c5f)
				  :value-selector value-selector :kb kb
				  :kb-local-only-p kb-local-only-p 
				  :verbose-p verbose-p)
    (setq ask-result (ask (setq query (list :primitive ?class))
			  :reply-pattern ?class
			  :inference-level :taxonomic :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-at-least kb (list c1f c2f c3f c4f)
		   "Ask (:primitive ?class)"
		   ask-result verbose-p)


    ;; Now test evaluable predicates.
    (setq fact '(= 1 1))
    (setq ask-result (ask (setq query fact)
			  :reply-pattern fact :inference-level :taxonomic
			  :number-of-values :all
			  :value-selector value-selector
			  :kb kb :kb-local-only-p kb-local-only-p))
    (test-true kb "(= 1 1)" ask-result verbose-p)
    (setq fact '(= 2.0 2.0))
    (setq ask-result (ask (setq query fact)
			  :reply-pattern fact :inference-level :taxonomic
			  :number-of-values :all
			  :value-selector value-selector :kb kb
			  :kb-local-only-p kb-local-only-p))
    (test-true kb "(= 2.0 2.0)" ask-result verbose-p)
    (setq fact '(= 1 2.0))
    (setq ask-result (ask (setq query fact)
			  :reply-pattern fact :inference-level :taxonomic
			  :number-of-values :all
			  :value-selector value-selector :kb kb
			  :kb-local-only-p kb-local-only-p))
    (test-false kb "(= 1 2.0)" ask-result verbose-p)

    (setq fact '(/= 1 1))
    (setq ask-result (ask (setq query fact)
			  :reply-pattern fact :inference-level :taxonomic
			  :number-of-values :all
			  :value-selector value-selector :kb kb
			  :kb-local-only-p kb-local-only-p))
    (test-false kb "(/= 1 1)" ask-result verbose-p)
    (setq fact '(/= 2.0 2.0))
    (setq ask-result (ask (setq query fact)
			  :reply-pattern fact :inference-level :taxonomic
			  :number-of-values :all
			  :value-selector value-selector :kb kb
			  :kb-local-only-p kb-local-only-p))
    (test-false kb "(/= 2.0 2.0)" ask-result verbose-p)
    (setq fact '(/= 1 2.0))
    (setq ask-result (ask (setq query fact)
			  :reply-pattern fact :inference-level :taxonomic
			  :number-of-values :all
			  :value-selector value-selector :kb kb
			  :kb-local-only-p kb-local-only-p))
    (test-true kb "(/= 1 2.0)" ask-result verbose-p)

    (setq fact '(< 1 2.0))
    (setq ask-result (ask (setq query fact)
			  :reply-pattern fact :inference-level :taxonomic
			  :number-of-values :all
			  :value-selector value-selector :kb kb
			  :kb-local-only-p kb-local-only-p))
    (test-true kb "(< 1 2.0)" ask-result verbose-p)
    (setq fact '(< 1 3))
    (setq ask-result (ask (setq query fact)
			  :reply-pattern fact :inference-level :taxonomic
			  :number-of-values :all
			  :value-selector value-selector :kb kb
			  :kb-local-only-p kb-local-only-p))
    (test-true kb "(< 1 3)" ask-result verbose-p)

    (setq fact '(< 2.0 1))
    (setq ask-result (ask (setq query fact)
			  :reply-pattern fact :inference-level :taxonomic
			  :number-of-values :all
			  :value-selector value-selector :kb kb
			  :kb-local-only-p kb-local-only-p))
    (test-false kb "(< 2.0 1)" ask-result verbose-p)
    (setq fact '(< 3 1))
    (setq ask-result (ask (setq query fact)
			  :reply-pattern fact :inference-level :taxonomic
			  :number-of-values :all
			  :value-selector value-selector :kb kb
			  :kb-local-only-p kb-local-only-p))
    (test-false kb "(< 3 1)" ask-result verbose-p)

    (setq fact '(> 2.0 1))
    (setq ask-result (ask (setq query fact)
			  :reply-pattern fact :inference-level :taxonomic
			  :number-of-values :all
			  :value-selector value-selector :kb kb
			  :kb-local-only-p kb-local-only-p))
    (test-true kb "(> 2.0 1)" ask-result verbose-p)
    (setq fact '(> 3 1))
    (setq ask-result (ask (setq query fact)
			  :reply-pattern fact :inference-level :taxonomic
			  :number-of-values :all
			  :value-selector value-selector :kb kb
			  :kb-local-only-p kb-local-only-p))
    (test-true kb "(> 3 1)" ask-result verbose-p)

    (setq fact '(> 1 2.0))
    (setq ask-result (ask (setq query fact)
			  :reply-pattern fact :inference-level :taxonomic
			  :number-of-values :all
			  :value-selector value-selector :kb kb
			  :kb-local-only-p kb-local-only-p))
    (test-false kb "(> 1 2.0)" ask-result verbose-p)
    (setq fact '(> 1 3))
    (setq ask-result (ask (setq query fact)
			  :reply-pattern fact :inference-level :taxonomic
			  :number-of-values :all
			  :value-selector value-selector :kb kb
			  :kb-local-only-p kb-local-only-p))
    (test-false kb "(> 1 3)" ask-result verbose-p)

    (setq fact '(>= 1 3))
    (setq ask-result (ask (setq query fact)
			  :reply-pattern fact :inference-level :taxonomic
			  :number-of-values :all
			  :value-selector value-selector :kb kb
			  :kb-local-only-p kb-local-only-p))
    (test-false kb "(>= 1 3)" ask-result verbose-p)
    (setq fact '(>= 1 1))
    (setq ask-result (ask (setq query fact)
			  :reply-pattern fact :inference-level :taxonomic
			  :number-of-values :all
			  :value-selector value-selector :kb kb
			  :kb-local-only-p kb-local-only-p))
    (test-true kb "(>= 1 1)" ask-result verbose-p)
    (setq fact '(>= 2.0 1))
    (setq ask-result (ask (setq query fact)
			  :reply-pattern fact :inference-level :taxonomic
			  :number-of-values :all
			  :value-selector value-selector :kb kb
			  :kb-local-only-p kb-local-only-p))
    (test-true kb "(>= 2 1)" ask-result verbose-p)

    (setq fact '(=< 1 3))
    (setq ask-result (ask (setq query fact)
			  :reply-pattern fact :inference-level :taxonomic
			  :number-of-values :all
			  :value-selector value-selector :kb kb
			  :kb-local-only-p kb-local-only-p))
    (test-true kb "(=< 1 3)" ask-result verbose-p)
    (setq fact '(=< 1 1))
    (setq ask-result (ask (setq query fact)
			  :reply-pattern fact :inference-level :taxonomic
			  :number-of-values :all
			  :value-selector value-selector :kb kb
			  :kb-local-only-p kb-local-only-p))
    (test-true kb "(=< 1 1)" ask-result verbose-p)
    (setq fact '(=< 2.0 1))
    (setq ask-result (ask (setq query fact)
			  :reply-pattern fact :inference-level :taxonomic
			  :number-of-values :all
			  :value-selector value-selector :kb kb
			  :kb-local-only-p kb-local-only-p))
    (test-false kb "(=< 2 1)" ask-result verbose-p)))

;==============================================================================

(defun test-true (kb string value verbose-p)
  (declare (ignore kb))
  (if value
      (progn (when verbose-p (format t "~&  Ok: ~A" string)) t)
      (bugmsg string t value)))

(defun test-false (kb string value verbose-p)
  (declare (ignore kb))
  (if value
      (bugmsg string nil value)
      (progn (when verbose-p (format t "~&  Ok: ~A" string)) t)))

(defun test-equal (kb string value original verbose-p)
  (if (equal-in-kb value original :kb kb :kb-local-only-p nil)
      (progn (when verbose-p (format t "~&  Ok: ~A" string)) t)
      (bugmsg string original value)))

(defun test-equal-sets (kb original string value verbose-p)
  (let ((difference (set-exclusive-or original value :test
				      #'(lambda (x y)
					  (equal-in-kb x y :kb kb
						     :kb-local-only-p nil)))))
    (if difference
	(bugmsg string original value difference)
	(progn (when verbose-p (format t "~&  Ok: ~A" string)) t))))

(defun test-all-in-list (kb must-all-be-in-this-list string all-in-this-list
			    verbose-p)
  (let ((difference (set-difference all-in-this-list must-all-be-in-this-list
				    :test
				    #'(lambda (x y)
					(equal-in-kb x y :kb kb
						     :kb-local-only-p nil)))))
    (if difference
	(bugmsg string must-all-be-in-this-list all-in-this-list difference)
	(progn (when verbose-p (format t "~&  Ok: ~A" string)) t))))

(defun test-at-least (kb all-these-must-be-in-result string result verbose-p)
  (let ((difference (set-difference all-these-must-be-in-result result :test
				    #'(lambda (x y)
					(equal-in-kb x y :kb kb
						   :kb-local-only-p nil)))))
    (if difference
	(bugmsg string all-these-must-be-in-result result difference)
	(progn (when verbose-p (format t "~&  Ok: ~A" string)) t))))

(defun test-ask-against-pattern
    (string pattern &key kb value-selector kb-local-only-p verbose-p)
  (let ((ask-result (ask pattern
			 :reply-pattern pattern :kb kb
			 :inference-level :taxonomic :number-of-values :all
			 :value-selector value-selector
			 :kb-local-only-p kb-local-only-p)))
    (test-equal kb string ask-result (list pattern) verbose-p))) 


(defun test-ask-against-pattern-not
    (string pattern &key kb  value-selector kb-local-only-p verbose-p)
  (let ((ask-result (ask pattern :reply-pattern pattern :kb kb
			 :inference-level :taxonomic :number-of-values :all
			 :value-selector value-selector
			 :kb-local-only-p kb-local-only-p)))
    (test-equal kb string ask-result nil verbose-p))) 

;==============================================================================

(defun equal-except-packages (a b)
  (if (consp a)
      (and (consp b)
	   (equal-except-packages (first a) (first b))
	   (equal-except-packages (rest a) (rest b)))
      (if (symbolp a)
	  (and (symbolp b)
	       (string= a b))
	  (equal-in-kb a b))))

(defun string-equal-except-packages (a b)
  (if (consp a)
      (and (consp b)
	   (string-equal-except-packages (first a) (first b))
	   (string-equal-except-packages (rest a) (rest b)))
      (if (symbolp a)
	  (and (symbolp b)
	       (string-equal a b))
	  (equal-in-kb a b))))

;(defun frame-name (frame-name)
;  (let ((frame (and (coercible-to-frame-p-internal frame-name (current-kb)
;                                                   nil)
;                    (get-frame-name-internal frame-name (current-kb) nil))))
;    (or frame frame-name)))

(defvar *catch-errors-in-test-suite-p* nil)

(defun eval-safe-for-test (form)
  (if *catch-errors-in-test-suite-p*
      (handler-case
       (eval form)
       (error (condition)
	      (warn (concatenate 'string
				 "!!! Error found during test execution: "
				 (princ-to-string condition)))
	      nil))
      (eval form)))

(Defun true? (form)
  (let ((y (eval-safe-for-test form)))
    (if y
	t
	(bugmsg form t y))))

(defun false? (form)
  (let ((y (eval-safe-for-test form)))
    (if y
	(bugmsg form nil y)
	t)))


(defun equal? (x form)
  (let ((y (eval-safe-for-test form)))
    (if (equal-in-kb x y)
	t
	(bugmsg form x y))))

(defun equal-except-packages? (x form)
  (let ((y (eval-safe-for-test form)))
    (if (equal-except-packages x y)
	t
	(bugmsg form x y))))

(defun string-equal-except-packages? (x form)
  (let ((y (eval-safe-for-test form)))
    (if (string-equal-except-packages x y)
	t
	(bugmsg form x y))))

(defun equal-sets? (x form &optional (map-form-fn #'identity))
  (let ((x (mapcar map-form-fn x))
	(y (mapcar map-form-fn (eval-safe-for-test form))))
    (let ((difference (set-exclusive-or x y :test 
					#'(lambda (x y) (equal-in-kb x y)))))
      (if difference
	  (bugmsg form x y difference)
	  t))))

(defun subsets? (all-these-must-be-present in-the-result-of-this-form
					   &optional (map-form-fn #'identity))
  (let ((all-these-must-be-present
	 (mapcar map-form-fn all-these-must-be-present))
	(y (mapcar map-form-fn
		   (eval-safe-for-test in-the-result-of-this-form))))
    (let ((difference (set-difference all-these-must-be-present y :test 
				      #'(lambda (x y) (equal-in-kb x y)))))
      (if difference
	  (bugmsg in-the-result-of-this-form all-these-must-be-present
		  y difference)
	  t))))


(defun equal-sets-except-packages? (x form &optional (map-form-fn #'identity))
  (let ((y (mapcar map-form-fn (eval-safe-for-test form))))
    (let ((difference (set-exclusive-or x y :test
					#'equal-except-packages)))
      (if difference
	  (bugmsg form x y difference)
	  t))))


(defvar *err-on-test-suite-bug-p* nil)

(defun bugmsg (form x y &optional (difference nil supplied-p))
  (let ((*package* (find-package :okbc-test)))
    (format t "~%Bug detected in execution of form ~%~S~%Expected: ~
             ~S~%Actual result: ~S~%"
	    form x y)
    (when supplied-p (format t "~%  Difference was: ~S~%" difference)))
  (when *err-on-test-suite-bug-p* (user::break)))

