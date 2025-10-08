(in-package :ok-kernel)

(defmethods ok-back:decontextualize-aux
    ((value (kb structure-kb)) (from-context t) (kb meta-kb))
  value)

(defmethod get-frame-pretty-name-internal
    ((frame abstract-kb-locator) (kb meta-kb) (kb-local-only-p t))
    (string (name frame)))

(defmethod ok-cache:allow-caching-p ((instance meta-kb)) :ephemeral)

(defmethod delete-frame-internal :after
    ((frame t) (kb meta-kb) (kb-local-only-p t))
  (when (kb-p frame) (close-kb-internal frame nil)))

(defmethod get-frame-name-internal
    ((frame abstract-kb-locator) (kb meta-kb) (kb-local-only-p t))
    (name frame))

(defmethod get-frame-name-internal
    ((frame kb) (kb meta-kb) (kb-local-only-p t))
  (name frame))

(defmethod get-frame-name-internal
    ((frame structure-kb) (kb meta-kb) (kb-local-only-p t))
  (name frame))

(defmethod get-frame-name-internal
    ((frame class) (kb meta-kb) (kb-local-only-p t))
  (class-name frame))

(defmethod coerce-to-frame-internal
    ((thing (eql :kb-locator)) (kb meta-kb) (error-p t) (kb-local-only-p t))
  (values thing t))

(defmethod coerce-to-class-internal
    ((thing (eql :kb-locator)) (kb meta-kb) (error-p t) (kb-local-only-p t))
  (values thing t))

(defmethod coerce-to-frame-internal
    ((thing symbol) (kb meta-kb) (error-p t) (kb-local-only-p t))
  (let ((class (find-class thing nil)))
    (if class
	(if (kb-p (ignore-errors (class-prototype-safe class)))
	    (values class t)
	    (if error-p
		(error 'not-coercible-to-frame :frame thing :kb kb)
		(values nil nil)))
	(let ((frame? (tuple-kb:get-simple-frame-with-slot-value
		       'tuple-kb::__name thing kb kb-local-only-p)))
	  (if (and frame? (not (eq thing frame?)))
	      (values frame? t)
	      ;; If we go taxonomic here we can get infinite recursions!
	      (let ((result (without-recursion-in-stack
			     (meta-kb-coerce-to-frame thing nil)
			     (default-find-kb thing (connection kb) :direct))))
		(if (kb-p result)
		    (values result t)
		    (let ((locators (get-class-instances-internal
				     :kb-locator kb :taxonomic :all nil)))
		      (loop for l in locators
			    when (and (typep l 'abstract-kb-locator)
				      (eq thing (name l)))
			    return (values l t)
			    finally
			    (if error-p
				(error 'not-coercible-to-frame
				       :frame thing :kb kb)
				(return (values nil nil))))))))))))

(defmethod coerce-to-frame-internal
    ((thing kb) (kb meta-kb) (error-p t) (kb-local-only-p t))
  (values thing t))

(defmethod coerce-to-frame-internal
    ((thing structure-kb) (kb meta-kb) (error-p t) (kb-local-only-p t))
  (values thing t))

(defmethod coerce-to-frame-internal
    ((thing abstract-kb-locator) (kb meta-kb) (error-p t) (kb-local-only-p t))
  (values thing t))

(defmethod coerce-to-frame-internal
    ((thing structure-class) (kb meta-kb) (error-p t) (kb-local-only-p t))
  (if (subtypep thing 'structure-kb)
      (values thing t)
      (if error-p
	  (error 'not-coercible-to-frame :frame thing :kb kb)
	  (values nil nil))))

(defmethod coerce-to-frame-internal
    ((thing standard-class) (kb meta-kb) (error-p t) (kb-local-only-p t))
  (if (subtypep thing 'kb)
      (values thing t)
      (if error-p
	  (error 'not-coercible-to-frame :frame thing :kb kb)
	  (values nil nil))))

(defmethod coerce-to-class-internal
    ((thing t) (kb meta-kb) (error-p t) (kb-local-only-p t))
  (multiple-value-bind (frame found-p)
      (coerce-to-frame-internal thing kb nil kb-local-only-p)
    (if (and found-p
	     (typep frame 'class)
	     (or (subtypep frame 'kb) (subtypep frame 'structure-kb)))
        (values frame found-p)
	(call-next-method))))

(defmethod get-kb-roots-internal
    ((kb meta-kb) (selector t) (kb-local-only-p t))
  (list (find-class 'kb) (find-class 'structure-kb)))

(defmethod get-kb-frames-internal ((kb meta-kb) (kb-local-only-p t))
  ;; classes only computed once because we're inside the cache wrapper.
  (remove-duplicates
   (append (get-kb-classes-internal kb :frames kb-local-only-p)
	   (get-kb-individuals-internal kb :frames kb-local-only-p)
	   (call-next-method))))

(defmethod get-kb-classes-internal
    ((kb meta-kb) (selector t) (kb-local-only-p t))
  (remove-duplicates
   (cons :kb-locator (all-compliant-okbc-implementations :read))))

(defmethod get-kb-individuals-internal
    ((kb meta-kb) (selector t) (kb-local-only-p t))
  (remove-duplicates
   (append
    (loop for class in (get-kb-classes-internal kb :frames kb-local-only-p)
	  for proto = (class-prototype-safe class)
	  when (kb-p proto)
	  append (get-kbs-of-type-internal proto (connection kb)))
    (call-next-method))))

(defmethod get-class-instances-internal
    ((class t) (kb meta-kb) (inference-level (eql :direct))
     (number-of-values t) (kb-local-only-p t))
  (let ((kb-frame (coerce-to-frame-internal class kb nil kb-local-only-p)))
    (if (and kb-frame (not (eq kb-frame class)))
	(get-class-instances-internal kb-frame kb :direct number-of-values
				kb-local-only-p)
	(call-next-method))))

(defmethod get-class-instances-internal
    ((class standard-class) (kb meta-kb) (inference-level (eql :direct))
     (number-of-values t) (kb-local-only-p t))
  (if (member (class-name class) *abstract-kb-class-names*)
      (values nil t)
      (let ((proto (class-prototype-safe class)))
	(if (kb-p proto)
	    (values (ignore-errors
		     (get-kbs-of-type-internal proto (connection kb)))
		    t)
	    (values nil t)))))

(defmethod get-class-instances-internal
    ((class structure-class) (kb meta-kb) (inference-level (eql :direct))
     (number-of-values t) (kb-local-only-p t))
  (if (member (class-name class) *abstract-kb-class-names*)
      (values nil t)
      (let ((proto (class-prototype-safe class)))
	(if (kb-p proto)
	    (values (ignore-errors
		     (get-kbs-of-type-internal proto (connection kb))) t)
	    (values nil t)))))

(defmethod find-kb-of-type-internal
    ((name-or-kb t) (kb-type meta-kb) (connection t))
  ;; Any sort of request of this type finds the one and only meta-kb
  ;; whatever name the user asked for.
  (meta-kb-internal connection))

;;; There can only ever be one of these.
(defmethod get-kbs-of-type-internal ((kb-type meta-kb) (connection t))
  (list (meta-kb-internal connection)))

(defmethod abstract-kb-class-name-from-kb ((instance meta-kb))
  'abstract-meta-kb-kb)

(defmethod concrete-kb-class-from-abstract-kb-class-name
    ((name (eql 'abstract-meta-kb-kb)))
  'meta-kb)

(defmethod save-kb-internal ((kb meta-kb) (error-p t))
  (continuable-error "Not supported by Meta-kb"))

(defmethod save-kb-as-internal ((new-name-or-locator t) (kb meta-kb))
  (continuable-error "Not supported by Meta-kb"))

(defmethod close-kb-internal ((kb meta-kb) (save-p t))
  (continuable-error "Not supported by Meta-kb"))

(defmethod open-kb-internal
    ((kb-locator t) (kb-type meta-kb) (connection t) (error-p t))
  (continuable-error "Not supported by Meta-kb"))

(defmethod expunge-kb-internal ((kb-locator t) (kb-type meta-kb)
				(connection t) (error-p t))
  (continuable-error "Not supported by Meta-kb"))

(defmethod get-kb-behaviors-internal ((kb-type-or-kb meta-kb) (connection t))
  (mapcar #'first *meta-kb-supported-behaviors*))

(defmethod get-behavior-supported-values-internal
    ((behavior t) (kb meta-kb))
  (rest (rest (assoc behavior *meta-kb-supported-behaviors*))))

(defmethod get-behavior-values-internal ((behavior t) (kb meta-kb))
  (rest (rest (assoc behavior *meta-kb-supported-behaviors*))))

(defmethod put-behavior-values-internal
    ((behavior t) (values t) (kb meta-kb))
  (continuable-assert
     nil illegal-behavior-values :behavior behavior :proposed-values values))

(defmethod-with-cache-method get-kb-types-from-meta-kb
    ((kb meta-kb))
  (remove-duplicates
   (loop for implementation
	 ;; Minimal compliance is OK
	 in (all-compliant-okbc-implementations :read)
	 for kb-type = (class-prototype-safe implementation)
	 for name = (clos::class-name implementation)
	 unless (member name *abstract-kb-class-names*)
	 collect kb-type)))

(defmethod-with-cache-method get-kbs-from-meta-kb
    ((kb meta-kb) (connection local-connection))
  (remove-duplicates
   (loop for kb-type in (get-kb-types-from-meta-kb kb)
	 append (get-kbs-of-type-internal
		 kb-type (connection-arg-default kb-type connection)))))

(defmethod frs-name-internal
    ((kb-type meta-kb) (connection local-connection))
  "Meta KB")

