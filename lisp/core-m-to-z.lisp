;;; -*- MODE :Lisp; Syntax:Common-Lisp; Package:OK-kernel; Base:10  -*- 

(in-package :ok-kernel)

(defokbcop okbc:member-behavior-values-p
    ((behavior :value) (value :value) &key (kb (current-kb)))
  :returned-values boolean
  :manual-category :behavior
  :doc-string
  "Returns \\true\\ when \\karg{value} is one of the variants of
   \\karg{behavior} that is currently active for \\karg{kb}, and returns
   \\false\\ otherwise."
  :default-body
  (member value (get-behavior-values-internal behavior kb) :test #'equal))

(defokbcop okbc:member-facet-value-p
    (frame slot facet value &key (kb (current-kb))
	   (inference-level :taxonomic)
	   (test :equal)
	   (slot-type :own)
	   (value-selector :either)
	   (kb-local-only-p nil))
  :returned-values (boolean exact-p)
  :manual-category :facet
  :doc-string
  "Returns \\true\\ iff \\karg{value} is a value in the specified \\karg{facet}
   of \\karg{slot} on \\karg{frame}, as determined by the predicate 
   \\karg{test}, and returns \\false\\ otherwise."
  :standard-default-body
  (multiple-value-bind (values exact-p)
      (get-facet-values-internal
       frame slot facet kb inference-level slot-type :all value-selector
       kb-local-only-p)
    (values (member value values :test
		    (decanonicalize-testfn test kb kb-local-only-p)) exact-p))
  :tell&ask-default-body
  ((declare (ignore test))
   (ask-internal
    (ecase slot-type
      (:own `(,facet ,slot ,frame ,value))
      (:template `(:template-facet-value ,facet ,slot ,frame ,value)))
    kb t inference-level 1
    t nil (timeout-for-tell&ask-defaults kb) value-selector kb-local-only-p))
  :monitor-body
  (record-reference frame slot t nil kb))

(defokbcop okbc:member-slot-value-p (frame slot value
					   &key (kb (current-kb))
					   (inference-level :taxonomic)
					   (test :equal) (slot-type :own)
					   (value-selector :either)
					   (kb-local-only-p nil))
  :returned-values (boolean exact-p)
  :manual-category :slot
  :doc-string
  "Returns \\true\\ iff \\karg{value} is a value in \\karg{slot} of
   \\karg{frame}, as determined by the predicate \\karg{test}, and returns
   \\false\\ otherwise."
  :standard-default-body
  (multiple-value-bind (values exact-p)
      (get-slot-values-internal frame slot kb inference-level
				slot-type :all value-selector kb-local-only-p)
    (values (or ;; We duplicate the member test because the eql-in-kb test
		;; is generally so expensive with its frame coercions that
		;; it's worth going out of our way to avoid it!
		(case test
		  (:eql (member value values :test #'eql))
		  (:equal (member value values :test #'equal))
		  (:equalp (member value values :test #'equalp))
		  (otherwise nil))
		(member value values :test
			(decanonicalize-testfn test kb kb-local-only-p)))
	    exact-p))
  :tell&ask-default-body
  ((declare (ignore test))
   (ask-internal
    (ecase slot-type
      (:own `(,slot ,frame ,value))
      (:template `(:template-slot-value ,slot ,frame ,value)))
    kb t inference-level 1
    t nil (timeout-for-tell&ask-defaults kb) value-selector kb-local-only-p))
  :monitor-body
  (record-reference frame slot t nil kb))


(defokbcop okbc:meta-kb (&key (connection (local-connection)))
  :returned-values meta-kb
  :manual-category :kb
  :doc-string
  "Returns the \\karg{Meta-KB} for the server accessed through the
   \\karg{connection}."
  :compliance-classes :read
  :arguments-to-kb-specialize ()
  :default-body ((declare (special $meta-kb$))
		 (declare (ignore connection))
		 $meta-kb$))

(defokbcop okbc:next (enumerator)
  :returned-values value
  :doc-string
  "Return the next value for the \\karg{enumerator}.  It is an error to
   call \\kfn{next} if \\kfn{has-more} would return \\false\\ for the
   enumerator.  If \\kfn{next} is called on an enumerator that has been 
   exhausted, an \\kcond{enumerator-exhausted} error should be signaled."
  :manual-category :enumerator
  :default-body (enumerator-next enumerator))

(defokbcop okbc:open-kb ((kb-locator :value)
			 &key (kb-type nil)
			 (connection (local-connection)) (error-p t))
  :returned-values kb
  :manual-category :kb
  :doc-string
  "Given a \\karg{kb-locator}, a \\karg{kb-type}, and a
   \\karg{connection}, returns a KB object
   for that KB locator that will behave as if all the objects in the
   KB are accessible (the implementation is not actually required to load the
   whole KB into memory).

   Implementations are at liberty to accept other values in place of the
   \\karg{kb-locator}, such as a pathname that identifies the location of
   the KB to the system.  Such usage is convenient, but is not portable.  It
   is not portable for an OKBC application to use anything other than
   a KB locator for this argument.  If \\karg{error-p} is \\false, catches
   errors that occur, and attempts to continue with the opening/loading
   process.  If the KB could not be successfully opened, returns \\false."
  :compliance-classes (:write :kb)
  :causes-side-effects-p t)



(defokbcop okbc:openable-kbs
    (&key (kb-type nil) (connection (local-connection))
	  (place nil))
  :returned-values list-of-kb-locators
  :manual-category :kb
  :doc-string
  "Given a \\karg{kb-type} and a \\karg{connection}, returns
   \\karg{list-of-kb-locators}, a list of frame handles to
   frames in the \\kfn{meta-kb} that are instances of the class 
   {\\tt kb-locator}.
   Each kb-locator instance describes one openable KB, identified at the
   time of the call.  Subsequent calls to openable-kbs will refresh the
   set of kb-locator instances in the meta-kb.  Kb-locators refering to
   KBs of \\karg{kb-type} that are no longer openable will be removed.  KBs
   of \\karg{kb-type} that have become openable since the last call will
   become represented in the \\kfn{meta-kb}.

   \\karg{Place} allows the application to communicate to the KRS in an
   KRS-specific way where to look for the openable KBs (e.g., a directory).
   The use of the \\karg{place} argument is not portable.
   If a particular \\karg{kb-type} does not understand the value of
   the \\karg{place} argument supplied, \\kfn{openable-kbs} returns
   \\emptylist, that is, there are no known openable KBs consistent
   with the supplied \\karg{place}."
  :arguments-to-kb-specialize (kb-type)
  :compliance-classes :read)

(defokbcop okbc:prefetch (enumerator &key (number-of-values :all)
				     (increment nil))
  :returned-values :void
  :doc-string
  "The \\kfn{prefetch} operator is an important optimization in network
   settings.  The client will attempt to prefetch sufficient elements in
   \\karg{enumerator} from the server so that \\karg{number-of-values} elements
   will be immediately available (cached) at the \\karg{enumerator}, using
   only a single network call rather than executing network calls for each 
   element.

   If it is discovered that there are fewer than \\karg{number-of-values}
   elements cached locally by \\karg{enumerator}, a minimum chunk of
   \\karg{increment} elements will be prefetched, when available.  Thus, if
   the enumerator already holds five elements locally, and the call
   \\verb|(prefetch enumerator 7 20)|
   is made, the fact that seven elements are requested, but only five are 
   available means that a request will in fact be made to the server for more
   elements, and at least another 20 (as opposed to 2) elements will be 
   prefetched.  When \\karg{increment} is \\false, the number of elements 
   prefetched will be the difference between the number currently cached in 
   the enumerator and \\karg{number-of-values}.

   Note that unlike other operations taking a \\karg{number-of-values} 
   argument, this operation does not return a \\karg{more-status} value.  
   Returns no values."
  :manual-category :enumerator
  :default-body (enumerator-prefetch
		 enumerator number-of-values increment))

(defokbcop okbc:primitive-p
    (class &key (kb (current-kb)) (kb-local-only-p nil))
  :returned-values boolean
  :manual-category :class
  :doc-string
  "Returns \\true\\ iff \\karg{class} is a class whose definition is
   primitive, and \\false\\ otherwise.  For KRSs that do not distinguish
   primitive from defined classes, \\kfn{primitive-p}
   must return \\true\\ for all classes."
  :compliance-classes :read
  :tell&ask-default-body
  (first (ask-internal `(:primitive ,class) kb t
		       (inference-level-for-tell&ask-defaults kb) 1
		       t nil (timeout-for-tell&ask-defaults kb)
		       :known-true kb-local-only-p))
  :monitor-body
  (record-reference class nil t nil kb))

;------------------------------------------------------------------------------

(defokbcop okbc:print-frame (frame &key
				   (kb (current-kb))
				   (slots :filled)
				   (facets :filled)
				   (stream t)
				   (inference-level :taxonomic)
				   (number-of-values :all)
				   (value-selector :either)
				   (kb-local-only-p nil))
  :returned-values false-or-string
  :manual-category :frame
  :doc-string
  "Prints a textual representation to \\karg{stream} of the
   \\karg{frame}.  A warning is printed when \\karg{frame} is not
   coercible to a frame.  Stream objects as values to the \\karg{stream}
   argument are generally system- and implementation-specific, so stream
   objects will not in general be
   transmissible in networked implementations.  Two special values for the
   \\karg{stream} argument are also supported.  If \\karg{stream} is \\false,
   then \\kfn{print-frame} prints to a string stream and
   that string is returned as \\karg{false-or-string}.
   If \\karg{stream} is \\true, \\kfn{print-frame} attempts to print to the
   standard output stream {\\em of the server on which} \\kfn{print-frame}
   {\\em runs.}  When \\karg{kb} is
   a network-acessed KB, this latter option is unlikely to have a useful
   effect.  Unless \\karg{stream} is \\false, \\karg{false-or-string} is
   \\false.

   The \\karg{slots} and \\karg{facets} arguments control which slots (facets) 
   are to be displayed.  They can each take on one of the following values:
   \\bitem
   \\item {\\tt :all} -- Shows all applicable slots (facets)
   \\item {\\tt :none} -- Shows no slots (facets)
   \\item {\\tt :filled} -- Shows the subset of slots (facets) that have at
   least one value for \\karg{frame}
   \\item list of slots (facets) -- Only the listed slots (facets) are shown,
   if present
   \\eitem"
  :default-body
  (case stream
    ((t) (print-frame-internal frame kb slots facets *standard-output*
			       inference-level number-of-values
			       value-selector kb-local-only-p)
     nil)
    ((nil) (with-output-to-string (stream)
	     (print-frame-internal frame kb slots facets stream
				   inference-level number-of-values
				   value-selector kb-local-only-p)))
    (otherwise 
      (defaut-print-frame-internal-body frame kb slots facets stream
	inference-level number-of-values value-selector kb-local-only-p)
      nil))
  :monitor-body
  (record-reference frame nil t nil kb))

(defun defaut-print-frame-internal-body
  (frame kb slots facets stream inference-level number-of-values
	 value-selector kb-local-only-p)
  (setq frame (coerce-to-frame-internal frame kb nil kb-local-only-p))
  (implement-with-kb-io-syntax-internal
   #'(lambda ()
       (let (print-slots print-facets)
	 (format stream "~%~%--- ~A ~S --- ~%"
		 (ecase (get-frame-type-internal frame kb kb-local-only-p)
		   (:class      "Class")
		   (:individual "Individual")
		   (:slot       "Slot")
		   (:facet      "Facet"))
		 (get-frame-pretty-name-internal frame kb kb-local-only-p))
	 (if (class-p-internal frame kb kb-local-only-p)
	     (progn
	       (output-list "    Superclasses:    "
			    (loop for x in (get-class-superclasses-internal
					    frame kb inference-level
					    number-of-values kb-local-only-p)
				  collect (value-as-string-internal
					   x kb :user-interface t
					   kb-local-only-p))

			    stream t)
	       (output-list "    Subclasses:      "
			    (loop for x in (get-class-subclasses-internal
					    frame kb inference-level
					    number-of-values kb-local-only-p) 
				  collect (value-as-string-internal
					   x kb :user-interface t
					   kb-local-only-p))

			    stream t)
	       (output-list "    Instances: "
			    (loop for x in (get-class-instances-internal
					    frame kb inference-level
					    number-of-values kb-local-only-p)
				  collect (value-as-string-internal
					   x kb :user-interface t
					   kb-local-only-p))

			    stream t))
	     (output-list "    Types:  "
			  (loop for x in (get-instance-types-internal
					  frame kb inference-level
					  number-of-values kb-local-only-p)
				collect (value-as-string-internal
					 x kb :user-interface t
					 kb-local-only-p))
			  stream t))
	 (loop for (slot-type string)
	       in (if (class-p-internal frame kb kb-local-only-p)
		      '((:own "Own slots") (:template "Template slots"))
		      '((:own "Own slots")))
	       do
	       (format stream "~%~A:~%" string)
	       (setq print-slots
		     (if (listp slots)
			 (intersection slots
				       (get-frame-slots-internal
					frame kb inference-level slot-type
					kb-local-only-p))
			 (ecase slots
			   (:none nil)
			   ((:all :filled)
			    (get-frame-slots-internal
			     frame kb inference-level slot-type
			     kb-local-only-p)))))
	       (setq print-slots
		     (sort (copy-list print-slots) #'string-lessp :key
			   #'(lambda (s)
			       (or (value-as-string-internal
				    s kb :user-interface t
				    kb-local-only-p)
				   (prin1-to-string s)))))
	       (loop for slot in print-slots
		     for slot-label =
		     (format nil "  ~A: "
			     (or (value-as-string-internal
				  slot kb :user-interface t
				  kb-local-only-p)
				 slot))
		     for facets-p =
		     (member :facets-supported
			     (get-behavior-values-internal :compliance kb))
		     for computed-facets =
		     (and facets-p
			  (get-slot-facets-internal
			   frame slot kb inference-level
			   slot-type kb-local-only-p))
		     for print-slot?
		     = (or (not (eq :filled slots))
			   (slot-has-value-p-internal
			    frame slot kb inference-level
			    slot-type value-selector
			    kb-local-only-p)
			   (and facets-p
				(loop for facet in
				      (if (listp facets)
					  facets
					  computed-facets)
				      thereis
				      (ecase facets
					(:none nil)
					(:all t)
					(:filled (facet-has-value-p-internal
						  frame slot facet kb
						  inference-level
						  slot-type value-selector
						  kb-local-only-p))))))
		     when print-slot?
		     do
		     (progn
		       (terpri stream)
		       (output-list slot-label
				    (get-slot-values-internal
				     frame slot kb inference-level slot-type
				     number-of-values value-selector
				     kb-local-only-p)
				    stream)
		       (terpri stream))
		     (when facets-p
		       (setq print-facets
			     (if (listp facets)
				 (intersection facets computed-facets)
				 (ecase facets
				   (:none nil)
				   ((:filled :all) computed-facets))))
		       (setq print-facets
			     (sort (copy-list print-facets) #'string-lessp :key
				   #'(lambda (f)
				       (or (value-as-string-internal
					    f kb :user-interface t
					    kb-local-only-p)
					   (prin1-to-string f)))))
		       (loop for facet in print-facets
			     for facet-label
			     = (format nil "~%    >>~A: "
				       (or (value-as-string-internal
					    facet kb :user-interface t
					    kb-local-only-p)
					   facet))
			     for fvalues = (get-facet-values-internal
					    frame slot facet kb inference-level
					    slot-type number-of-values
					    value-selector kb-local-only-p)
			     when (or (not (eq :filled facets))
				      fvalues)
			     do (output-list facet-label fvalues stream))))))
       (values))
   kb :user-interface kb-local-only-p)
  nil)


; ======================================================  break-output-stream

; This function can be used to format a sequence of strings into a
; paragraph of given width.  Each time this function is called it
; outputs the String argument, preceding String with a newline if the
; function determines that without a newline the string will overrun
; the paragraph.

; Returns: A Position value in the current line that should be used as
; the Position parameter in the next call to this function.

(defun break-output-stream (position
			    string
			    &key
			    (file *standard-output*)
			    (width-limit 75)
			    (prepend "")    ; String to prepend to each line
			    first? ; If T then we always print one item even if
			           ; the width-limit is exceeded.
			    )
  (let (test-position)
    (if (eql -1 position)
	(progn
	  (princ prepend file)
	  (setq position 0)
	  ))
    (if (or (> width-limit (setq test-position
				 (compute-position position string)))
	    first? )
	(progn
	 (princ string file)
	 (setq position test-position))
	(progn
	  (setq string (concatenate 'string prepend string))
	  (terpri file)
	  (princ string file)
	  (setq position (compute-position 0 string))))

    position))


(defun compute-position (start-position string)
  (let ((position start-position))
    (dotimes (i (length string))
      (if (eql (char string i)
	       #\Tab)
	  (setq position (* 8 (1+ (floor (1+ position) 8))))
	  (setq position (1+ position))))
    position))
    
(defun undefined-method (method-name kb)
  (error 'method-missing :okbcop method-name :kb kb
	 :continuable t))

(defun output-list (label xx stream &optional newline?)
  (let ((position (length label))
	len
	(indent (make-string (length label)
			     :initial-element #\Space)))

    (princ label stream)

    ;; xx should really be a list but there are occasional times that
    ;; it is not.
    (unless (listp xx)
      (princ "." stream)
      (setq xx (list xx)))

    (setq len (length xx))

    (loop for x in xx
	  for i from 1
	  do
	  (setq position
		(break-output-stream
		 position
		 (if (stringp x)
		     (format nil "~A~A" x (if (eq i len) "" ", "))
		     (format nil "~S~A" x (if (eq i len) "" ", ")))
		 :file stream
		 :prepend indent
		 :first? (eql i 1))))
    (when newline?
      (terpri stream))))

;------------------------------------------------------------------------------

(defokbcop okbc:put-behavior-values
    ((behavior :value) values &key (kb (current-kb)))
  :returned-values :void
  :manual-category :behavior
  :doc-string
  "Sets the list of active \\karg{values} of the \\karg{behavior} under
   which the KB is to operate.  The elements in \\karg{values} must be a
   subset of the values returned by a call to
   \\kfn{get-behavior-supported-values} for the same \\karg{behavior}.
   If they are not, an \\kcond{illegal-behavior-values} error will be signaled.
   Note that for some behaviors, the order of values is significant (e.g.,
    {\\tt :collection-type}).  Returns no values."
  :compliance-classes :read)

(defmethods put-behavior-values-internal :before
  (behavior values (kb (kb structure-kb)))
  (continuable-assert
   (listp values)
   illegal-behavior-values
   :behavior behavior
   :proposed-values values)
  (continuable-assert
   (not (set-difference
	 values (get-behavior-supported-values-internal behavior kb)))
   illegal-behavior-values
   :behavior behavior
   :proposed-values values))

;------------------------------------------------------------------------------

(defokbcop okbc:put-class-superclasses (class (new-superclasses (:class))
					      &key (kb (current-kb))
					      (kb-local-only-p nil))
  :returned-values :void
  :manual-category :class
  :doc-string
  "Changes \\karg{class} to be a subclass of all the classes listed in
   \\karg{new-superclasses}.  If \\karg{frame} was a subclass of any
   superclasses not mentioned in \\karg{new-superclasses}, these superclasses
   are removed.
   This operation may signal constraint violation conditions
   (see Section~\\ref{sec:errors}).  Returns no values."
  :compliance-classes :write
  :tell&ask-default-body
  ((untell-internal `(:subclass-of ,class ?x)
		    kb class :known-true kb-local-only-p)
   (loop for s in new-superclasses
	 do (tell-internal `(:subclass-of ,class ,s)
			   kb class :known-true kb-local-only-p)))
  :causes-side-effects-p t
  :monitor-body
  (progn 
    (record-reference class nil t nil kb)
    (mapcar #'(lambda (class)
		(record-reference class nil t nil kb))
	    new-superclasses))
  :modification-body 
  (record-modification class kb :modify))

(defokbcop okbc:put-facet-value (frame slot facet value
				       &key (kb (current-kb)) (slot-type :own)
				       (value-selector :known-true)
				       (kb-local-only-p nil))
  :returned-values :void
  :manual-category :facet
  :doc-string
  "Sets the values of the specified facet to be a singleton set
   consisting of a single element: \\karg{value}.  Returns no values."
  :causes-side-effects-p t
  :default-body ;; SMP added 10/24/94
  (put-facet-values-internal frame slot facet (list value) kb slot-type
			     value-selector kb-local-only-p)
  :monitor-body
  (record-reference frame slot t nil kb)
  :modification-body
  (if frame
      (record-modification frame kb :modify slot)
    (record-modification slot kb :modify)))


(defokbcop okbc:put-facet-values (frame slot facet values
					&key (kb (current-kb)) (slot-type :own)
					(value-selector :known-true)
					(kb-local-only-p nil))
  :returned-values :void
  :manual-category :facet
  :doc-string
  "Sets the values of the specified facet to be
   \\karg{values}, which is assumed to be a set.  Any existing facet values
   that are not in \\karg{values} will be removed.  The order of the elements of
   \\karg{values} will not necessarily be maintained by the KRS.
   This operation may signal constraint violation conditions
   (see Section~\\ref{sec:errors}).  Returns no values."
  :compliance-classes (:write :facets)
  :causes-side-effects-p t
  :tell&ask-default-body
  ((untell-internal
    (ecase slot-type
      (:own `(,facet ,slot ,frame ?value))
      (:template `(:template-facet-value ,facet ,slot ,frame ?value)))
    kb frame value-selector kb-local-only-p)
   (loop for value in values
	 do (tell-internal
	     (ecase slot-type
	       (:own `(,facet ,slot ,frame ,value))
	       (:template
		`(:template-facet-value ,facet ,slot ,frame ,value)))
	     kb frame value-selector kb-local-only-p)))
  :monitor-body
  (record-reference frame slot t nil kb)
  :modification-body
  (if frame
      (record-modification frame kb :modify slot)
    (record-modification slot kb :modify)))


(defokbcop okbc:put-frame-details
    (frame (details :value) &key (kb (current-kb)) (kb-local-only-p nil))
  :returned-values :void
  :manual-category :frame
  :causes-side-effects-p t
  :doc-string
  "Redefines \\karg{frame} to have the specified \\karg{details}.
   \\karg{Details} is a property list as specified for
   \\kfn{get-frame-details}.  This operation is useful for systems that allow
   transaction-oriented editing of multiple aspects of a frame.
   The properties {\\tt :handle}, {\\tt :frame-type}, and {\\tt :primitive-p}
   are ignored, since these may not be put.
   Returns no values."
  :monitor-body
  (progn (record-reference frame nil t nil kb))
  :default-body
  (destructuring-bind (&key handle name pretty-name frame-type primitive-p
			    superclasses subclasses types own-slots
			    template-slots own-facets template-facets
			    &allow-other-keys) details
    (declare (ignore frame-type primitive-p handle))
    (let ((frame (coerce-to-frame-internal frame kb t kb-local-only-p)))
      (put-frame-name-internal        frame name         kb kb-local-only-p)
      (put-frame-pretty-name-internal frame pretty-name  kb kb-local-only-p)
      (put-instance-types-internal    frame types        kb kb-local-only-p)
      (multiple-value-bind (defined-slot-alist defined-facet-alist)
	  (initialize-slots-and-facets
	   frame kb own-slots own-facets :own kb-local-only-p)
	(cond ((class-p-internal frame kb kb-local-only-p)
	       (put-class-superclasses-internal
		frame superclasses kb kb-local-only-p)
	       (let ((subclasses-to-remove
		      (set-difference
		       (get-class-subclasses-internal
			frame kb :direct :all kb-local-only-p)
		       subclasses
		       :test (decanonicalize-testfn :eql kb kb-local-only-p)))
		     (subclasses-to-add
		      (set-difference
		       subclasses
		       (get-class-subclasses-internal
			frame kb :direct :all kb-local-only-p)
		       :test (decanonicalize-testfn :eql kb kb-local-only-p))))
		 (loop for s in subclasses-to-remove
		       do (put-class-superclasses-internal
			   s (remove frame
				     (get-class-superclasses-internal
				      s kb :direct :all kb-local-only-p)
				     :test (decanonicalize-testfn
					    :eql kb kb-local-only-p))
			   kb kb-local-only-p))
		 (loop for s in subclasses-to-add
		       do (add-class-superclass-internal
			   s frame kb kb-local-only-p)))
	       (initialize-slots-and-facets
		frame kb template-slots template-facets :template
		kb-local-only-p defined-slot-alist defined-facet-alist))
	      ((and (not template-slots) (not template-facets) 
		    (not subclasses) (not superclasses))
	       nil)
	      (t (continuable-error
		  "~S is not a class, so cannot have template slots/facets, ~
                   or super/subclasses."
		  frame)))))))

(defun add-frame-details
    (frame details &key (kb (current-kb)) (kb-local-only-p nil))
  "Just like put-frame-details, only it adds rather than replacing.
   Useful in merging frames."
  (destructuring-bind (&key handle name pretty-name frame-type primitive-p
			    superclasses subclasses types own-slots
			    template-slots own-facets template-facets
			    &allow-other-keys) details
    (declare (ignore name pretty-name frame-type primitive-p handle))
    ;; There's only one name or pretty name, so ignore these!
    (let ((frame (coerce-to-frame-internal frame kb t kb-local-only-p)))
      (loop for type in types
	    do (add-instance-type-internal frame type kb kb-local-only-p))
      (multiple-value-bind (defined-slot-alist defined-facet-alist)
	  (add-to-slots-and-facets
	   frame kb own-slots own-facets :own kb-local-only-p :equal)
	(cond ((class-p-internal frame kb kb-local-only-p)
	       (loop for class in superclasses
		     do (add-class-superclass-internal
			 frame class kb kb-local-only-p))
	       (add-to-slots-and-facets
		frame kb template-slots template-facets :template
		kb-local-only-p :equal
		defined-slot-alist defined-facet-alist))
	      ((and (not template-slots) (not template-facets) 
		    (not subclasses) (not superclasses))
	       nil)
	      (t (continuable-error
		  "~S is not a class, so cannot have template slots/facets, ~
                   or super/subclasses."
		  frame)))))))

(defokbcop okbc:put-frame-name (frame new-name &key (kb (current-kb))
				      (kb-local-only-p nil))
  :returned-values renamed-frame
  :manual-category :frame
  :compliance-classes :write
  :doc-string
  "Changes the name of \\karg{frame} to be \\karg{new-name}.  All references
   to \\karg{frame} in \\karg{kb} (e.g., in slot values) will point to the
   frame named \\karg{new-name}.  Returns the frame with the new name,
   \\karg{renamed-frame}.  It is not necessary that the frame object identified
   by \\karg{frame} be identical ({\\tt ==}/{\\tt EQLness}) to the frame
   object called \\karg{new-name}, only that the KB consistently use the
   new frame instead of the old one.
   
   Implementation note:  KRSs that use frame names as frame handles must
   replace {\\em all} references to the old name of \\karg{frame} with
   \\karg{new-name}.  This specification allows for implementations that
   are forced to replace the representation of the frame with a new, renamed
   version."
  :causes-side-effects-p t
  :tell&ask-default-body
  ((untell-internal `(:name ,frame ?x)
		    kb frame :known-true kb-local-only-p)
   (tell-internal `(:name ,frame ,new-name)
		  kb frame :known-true kb-local-only-p)
   frame)
  :monitor-body
  (progn
    (record-reference frame nil t nil kb)
    (record-reference new-name nil t nil kb))
  :modification-body
  ;; In addition to this modification body, the method itself records
  ;; the deletion of frame because once the frame is deleted, this after
  ;; method has no way of determining what KB the frame was in.
  (record-modification
   (coerce-to-frame-internal new-name kb t kb-local-only-p) kb :create))


(defokbcop okbc:put-frame-pretty-name
    (frame (name :value) &key (kb (current-kb)) (kb-local-only-p nil))
  :returned-values :void
  :manual-category :frame
  :doc-string
  "Stores the \\karg{name}, a string, as the new pretty-name of the
   \\karg{frame}.  OKBC mandates no constraints on the new pretty-\\karg{name},
   but to maximize the liklihood that applications will interoperate smoothly,
   implementations are encouraged to make pretty-names be short, and are
   strongly encouraged to include no whitespace characters other than the space
   characters, or any display device-specific control characters.  Returns no
   values."
  :compliance-classes :write
  :tell&ask-default-body
  ((untell-internal `(:pretty-name ,frame ?x)
		    kb frame :known-true kb-local-only-p)
   (tell-internal `(:pretty-name ,frame ,name)
		  kb frame :known-true kb-local-only-p))
  :causes-side-effects-p t
  :monitor-body
  (record-reference frame nil t nil kb))

(defokbcop okbc:put-instance-types (frame (new-types (:class))
					  &key (kb (current-kb))
					  (kb-local-only-p nil))
  :returned-values :void
  :manual-category :instance
  :doc-string
  "Changes \\karg{frame} to be an instance of all the classes listed in
   \\karg{new-types}.  If \\karg{frame} was an instance of any types not
   mentioned in \\karg{new-types}, these types are removed.
   This operation may signal constraint violation conditions
   (see Section~\\ref{sec:errors}).  Returns no values."
  :causes-side-effects-p t
  :compliance-classes :write
  :tell&ask-default-body
  ((untell-internal `(:instance-of ,frame ?x)
		    kb frame :known-true kb-local-only-p)
   (loop for type in new-types
	 do (tell-internal `(:instance-of ,frame ,type)
			   kb frame :known-true kb-local-only-p)))
  :monitor-body
  (progn 
    (record-reference frame nil t nil kb)
    (mapcar #'(lambda (class)
		(record-reference class nil t nil kb))
	    new-types))
  :modification-body 
  (record-modification frame kb :modify))

(defokbcop okbc:put-slot-value (frame slot value &key
				      (kb (current-kb)) (slot-type :own)
				      (value-selector :known-true)
				      (kb-local-only-p nil))
  :returned-values :void
  :manual-category :slot
  :doc-string
  "Sets the values of \\karg{slot} in \\karg{frame} to be a singleton set
   consisting of a single element:  \\karg{value}.
   This operation may signal constraint violation conditions
   (see Section~\\ref{sec:errors}).  Returns no values."
  :causes-side-effects-p t
  :default-body
  (put-slot-values-internal frame slot (list value) kb slot-type
			    value-selector kb-local-only-p)
  :monitor-body
  (record-reference frame slot t nil kb)
  :modification-body
  (record-modification frame kb :modify slot))

(defokbcop okbc:put-slot-values (frame slot values
				       &key (kb (current-kb)) (slot-type :own)
				       (value-selector :known-true)
				       (kb-local-only-p nil))
  :returned-values :void
  :manual-category :slot
  :doc-string
  "Sets the values of \\karg{slot} in \\karg{frame} to
   be \\karg{values}.  Any existing slot values that are not in \\karg{values}
   will be removed.  The order of the elements
   of \\karg{values} will not necessarily be maintained by the KRS, unless the
   {\\tt :collection-type} of the slot is {\\tt :list}.
   This operation may signal constraint violation conditions
   (see Section~\\ref{sec:errors}).  Returns no values."
  :compliance-classes :write
  :causes-side-effects-p t
  :tell&ask-default-body
  ((untell-internal
    (ecase slot-type
      (:own `(,slot ,frame ?value))
      (:template `(:template-slot-value ,slot ,frame ?value)))
    kb frame value-selector kb-local-only-p)
   (loop for value in values
	 do (tell-internal
	     (ecase slot-type
	       (:own `(,slot ,frame ,value))
	       (:template
		`(:template-slot-value ,slot ,frame ,value)))
	     kb frame value-selector kb-local-only-p)))
  :monitor-body
  (record-reference frame slot t nil kb)
  :modification-body
  (record-modification frame kb :modify slot))


(defokbcop okbc:register-procedure
    ((name :value) procedure &key (kb (current-kb)))
  :returned-values :void
  :manual-category :funspec
  :causes-side-effects-p t
  :doc-string
  "Associates the \\karg{procedure} with \\karg{name} in \\karg{kb}.
   Subsequent calls to \\kfn{call-procedure} may invoke the procedure merely by
   using the name.  If \\karg{name} is \\false, then \\karg{procedure}
   must be a {\\em named} procedure, in which case the \\karg{name}
   argument will default to the name of the procedure.
   Returns no values."
  :default-body
  ((continuable-assert (typep procedure 'procedure) ()
		       "~S should be a procedure." procedure)
   (if name
       (progn (setf (gethash (string-upcase (okbc-string name))
			     (name-to-procedure-table kb))
		    procedure)
	      (when (not (procedure-name procedure))
		(setf (procedure-name procedure) name)))
       (if (and (procedure-name procedure)
		(or (symbolp (procedure-name procedure))
		    (quasi-symbol-p (procedure-name procedure))))
	   (setf (gethash (string-upcase
			   (okbc-string (procedure-name procedure)))
			  (name-to-procedure-table kb))
		 procedure)
	   (continuable-error "procedure ~S has no name."
				  procedure)))))

(defokbcop okbc:remove-class-superclass
    (class (superclass-to-remove :class) &key (kb (current-kb))
	   (kb-local-only-p nil))
  :returned-values :void
  :manual-category :class
  :doc-string
  "Removes \\karg{superclass-to-remove} from the superclasses of \\karg{class}.
   Returns no values."
  :compliance-classes :write
  :standard-default-body
  (put-class-superclasses-internal
   class
   (remove superclass-to-remove
	   (get-class-superclasses-internal class kb :direct :all
					    kb-local-only-p)
	   :test (decanonicalize-testfn :eql kb kb-local-only-p))
   kb kb-local-only-p)
  :tell&ask-default-body
  (untell-internal `(:subclass-of ,class ,superclass-to-remove)
		   kb class :known-true kb-local-only-p)
  :causes-side-effects-p t
  :monitor-body
  (progn 
    (record-reference class nil t nil kb)
    (record-reference superclass-to-remove nil t nil kb))
  :modification-body 
  (record-modification class kb :modify))

(defokbcop okbc:remove-facet-value (frame slot facet value
					  &key (kb (current-kb)) (test :equal)
					  (slot-type :own)
					  (value-selector :known-true)
					  (kb-local-only-p nil))
  :returned-values :void
  :manual-category :facet
  :doc-string
  "If \\karg{value} is currently a member of the set of direct values of
   the specified facet, then \\karg{value} is removed from the values of
   the facet.  Returns no values."
  :causes-side-effects-p t
  :standard-default-body
  (let ((values (get-facet-values-internal
		 frame slot facet kb :direct slot-type :all value-selector
		 kb-local-only-p))
	(testfn (decanonicalize-testfn test kb kb-local-only-p)))
    (when (member value values :test testfn)
      (put-facet-values-internal frame slot facet
				 (remove value values :test testfn)
				 kb slot-type value-selector kb-local-only-p)))
  :tell&ask-default-body
  ((declare (ignore test))
   (untell-internal (ecase slot-type
		      (:own `(,facet ,slot ,frame ,value))
		      (:template
		       `(:template-facet-value ,facet ,slot ,frame ,value)))
		    kb frame value-selector kb-local-only-p))
  :monitor-body
  (record-reference frame slot t nil kb)
  :modification-body
  (if frame
      (record-modification frame kb :modify slot)
    (record-modification slot kb :modify)))

(defokbcop okbc:remove-instance-type (frame (type-to-remove :class)
					    &key (kb (current-kb))
					    (kb-local-only-p nil))
  :returned-values :void
  :manual-category :instance
  :doc-string
  "Removes \\karg{type-to-remove} from the types of \\karg{frame} -- that is,
   makes \\karg{frame} no longer be an instance of \\karg{type-to-remove}.
   Returns no values."
  :compliance-classes :write
  :standard-default-body
  (put-instance-types-internal
   frame
   (remove type-to-remove
	   (get-instance-types-internal frame kb :direct :all kb-local-only-p)
	   :test (decanonicalize-testfn :eql kb kb-local-only-p))
   kb kb-local-only-p)
  :tell&ask-default-body
  (untell-internal `(:instance-of ,frame ,type-to-remove)
		   kb frame :known-true kb-local-only-p)
  :causes-side-effects-p t
  :monitor-body
  (progn (record-reference frame nil t nil kb)
	 (record-reference type-to-remove nil t nil kb))
  :modification-body 
  (record-modification frame kb :modify))


(defokbcop okbc:remove-local-facet-values (frame slot facet
						 &key (kb (current-kb))
						 (slot-type :own)
						 (value-selector :known-true)
						 (kb-local-only-p nil))
  :returned-values :void
  :manual-category :facet
  :doc-string
  "Removes all direct values of \\karg{facet} in \\karg{slot} of \\karg{frame}.
   Returns no values."
  :causes-side-effects-p t
  :standard-default-body
  (put-facet-values-internal frame slot facet nil kb slot-type value-selector
			     kb-local-only-p)
  :tell&ask-default-body
  (untell-internal (ecase slot-type
		      (:own `(,facet ,slot ,frame ?value))
		      (:template
		       `(:template-facet-value ,facet ,slot ,frame ?value)))
		    kb frame value-selector kb-local-only-p)
  :monitor-body
  (record-reference frame slot t nil kb)
  :modification-body
  (record-modification frame kb :modify :all))



(defokbcop okbc:remove-local-slot-values
    (frame slot
	   &key (kb (current-kb)) (slot-type :own)
	   (value-selector :known-true)
	   (kb-local-only-p nil))
  :returned-values :void
  :manual-category :slot
  :doc-string
  "Removes all direct values in \\karg{slot} of \\karg{frame}.
   Returns no values."
  :causes-side-effects-p t
  :standard-default-body
  (put-slot-values-internal frame slot nil kb slot-type value-selector
			    kb-local-only-p)
  :tell&ask-default-body
   (untell-internal (ecase slot-type
		      (:own `(,slot ,frame ?value))
		      (:template
		       `(:template-slot-value ,slot ,frame ?value)))
		    kb frame value-selector kb-local-only-p)
  :monitor-body
  (record-reference frame slot t nil kb)
  :modification-body
  (record-modification frame kb :modify :all))

(defokbcop okbc:remove-slot-value (frame slot value &key (kb (current-kb))
					 (test :equal)
					 (slot-type :own) (index :all)
					 (value-selector :known-true)
					 (kb-local-only-p nil))
  :returned-values :void
  :manual-category :slot
  :doc-string
  "If \\karg{value} is currently a member of the set of direct values of
   \\karg{slot}, then \\karg{value} is removed from the values of
   \\karg{slot}.  Only values matching the \\karg{test} are removed.
   If \\karg{index} is {\\tt :all}, then all occurrences of
   \\karg{value} will be removed.  Otherwise, \\karg{index} should be
   an integer index into the values list, and only the value at that
   position, if it matches \\karg{value}, will be removed (the first
   value of the slot has index 0).  The index argument is used only by slots
   whose {\\tt :collection-type} is {\\tt :list}.  Returns no values."
  :causes-side-effects-p t
  :standard-default-body
  (let ((values (get-slot-values-internal frame slot kb :direct slot-type :all
					  value-selector kb-local-only-p)))
    (let ((testfn (decanonicalize-testfn test kb kb-local-only-p)))
      (when (member value values :test testfn)
	(if (or (eq index :all)
		(eq (get-collection-type frame slot kb slot-type
					 kb-local-only-p)
		    :set))
	    (put-slot-values-internal
	     frame slot (remove value values :test testfn) kb slot-type
	     value-selector kb-local-only-p)
	    (when (funcall testfn value (nth index values))
	      (put-slot-values-internal
	       frame slot (remove value values :test testfn :start index
				  :count 1)
	       kb slot-type value-selector kb-local-only-p))))))
  :tell&ask-default-body
  ((declare (ignore index test))
   (untell-internal (ecase slot-type
		      (:own `(,slot ,frame ,value))
		      (:template
		       `(:template-slot-value ,slot ,frame ,value)))
		    kb frame value-selector kb-local-only-p))
  :monitor-body
  (record-reference frame slot t nil kb)
  :modification-body
  (record-modification frame kb :modify slot))

(defokbcop okbc:rename-facet (facet new-name &key (kb (current-kb))
				    (kb-local-only-p nil))
  :returned-values renamed-facet
  :manual-category :facet
  :compliance-classes :write
  :doc-string
  "Renames the facet for all frames containing that facet.
   \\bitem
   \\item If the facet identified by \\karg{facet} is represented as a frame,
          that frame is renamed.
   \\item If the facet identified by \\karg{facet} is not represented as
          a frame, \\kfn{facet-p} applied to \\karg{facet} will return
          \\false\\, and \\karg{facet} will not be returned by any of
          the facet-returning operations, such as \\kfn{get-kb-facets}.
          \\karg{New-name} will now identify the
          facet, and will be returned by operations such as
          \\kfn{get-kb-facets} and \\kfn{get-frame-facets}.
   \\eitem
   All the facet values and facet values associated with \\karg{facet} are
   preserved under the \\karg{new-name}.  For example, for any frame in
   the KB, the values returned by \\kfn{get-facet-values} for \\karg{facet}
   before the rename are identical to the values returned  for
   \\karg{new-name} after the rename.  In addition, the {\\em attached-to}
   relationship is preserved -- that is, if \\karg{facet} is attached to a
   frame before the rename, \\karg{new-name} is attached to that frame
   after the rename.  In some implementations, references to \\karg{facet}
   may still remain in the KB after \\karg{rename-facet}.  Returns the
   \\karg{renamed-facet}."
  :causes-side-effects-p t)


(defokbcop okbc:rename-slot (slot new-name &key (kb (current-kb))
				  (kb-local-only-p nil))
  :returned-values renamed-slot
  :manual-category :slot
  :compliance-classes :write
  :doc-string
  "Renames the slot for all frames containing that slot.
   \\bitem
   \\item If the slot identified by \\karg{slot} is represented as a frame,
          that frame is renamed.
   \\item If the slot identified by \\karg{slot} is not represented as
          a frame, \\kfn{slot-p} applied to \\karg{slot} will return \\false\\,
          and \\karg{slot} will not be returned by any of the slot-returning
          operations, such as \\kfn{get-kb-slots} and \\kfn{get-frame-slots}.
          \\karg{New-name} will now identify the slot, and will be returned by
          operations such as \\kfn{get-kb-slots} and \\kfn{get-frame-slots}.
   \\eitem
   All the slot values and facet values associated with \\karg{slot} are
   preserved under the \\karg{new-name}.  For example, for any frame in
   the KB, the values returned by \\kfn{get-slot-values} for \\karg{slot}
   before the rename are identical to the values returned  for
   \\karg{new-name} after the rename.  In addition, the {\\em attached-to}
   relationship is preserved -- that is, if \\karg{slot} is attached to a
   frame before the rename, \\karg{new-name} is attached to that frame
   after the rename.  In some implementations, references to \\karg{slot}
   may still remain in the KB after \\karg{rename-slot}.  Returns the
   \\karg{renamed-slot}."
  :causes-side-effects-p t)

(defokbcop okbc:replace-facet-value
    (frame slot facet (old-value :value) (new-value :value)
	   &key (kb (current-kb)) (test :equal)
	   (slot-type :own) (value-selector :known-true)
	   (kb-local-only-p nil))
  :returned-values :void
  :manual-category :facet
  :doc-string
  "If \\karg{old-value} is currently a member of the set of direct values of
   the specified facet, then \\karg{old-value} is replaced by 
   \\karg{new-value} in the facet.  Returns no values."
  :causes-side-effects-p t
  :standard-default-body
  ((remove-facet-value-internal frame slot facet old-value kb test slot-type
				value-selector kb-local-only-p)
   (add-facet-value-internal frame slot facet new-value kb test slot-type
			     value-selector kb-local-only-p))
  :tell&ask-default-body
  ((declare (ignore test))
   (untell-internal (ecase slot-type
		      (:own `(,facet ,slot ,frame ,old-value))
		      (:template
		       `(:template-facet-value
			 ,facet ,slot ,frame ,old-value)))
		    kb frame value-selector kb-local-only-p)
   (tell-internal (ecase slot-type
		    (:own `(,facet ,slot ,frame ,new-value))
		    (:template
		     `(:template-facet-value ,facet ,slot ,frame ,new-value)))
		  kb frame value-selector kb-local-only-p))
  :monitor-body
  (record-reference frame slot t nil kb)
  :modification-body
  (if frame
      (record-modification frame kb :modify slot)
      (record-modification slot kb :modify)))


(defokbcop okbc:replace-slot-value
    (frame slot (old-value :value) (new-value :value)
	   &key (kb (current-kb)) (test :equal)
	   (slot-type :own) (index :all)
	   (value-selector :known-true)
	   (kb-local-only-p nil))
  :returned-values :void
  :manual-category :slot
  :doc-string
  "If \\karg{old-value} is currently a member of the set of direct values of
   \\karg{slot}, then \\karg{old-value} is replaced by \\karg{new-value} in
   \\karg{slot}.  If \\karg{index} is {\\tt :all} then all occurrences of
   \\karg{old-value} will be replaced.  Otherwise, \\karg{index} should be
   an integer index into the values list, and only the value at that
   position, if it matches \\karg{old-value}, will be replaced (the first
   value of the slot has index 0).
   This operation may signal constraint violation conditions
   (see Section~\\ref{sec:errors}).  The \\karg{index} argument is used only
   by slots whose {\\tt :collection-type} is {\\tt :list}.
   Returns no values."
  :causes-side-effects-p t
  :standard-default-body
  (if (eq index :all)
      (let ((values (get-slot-values-internal frame slot kb :direct slot-type
					      :all value-selector
					      kb-local-only-p)))
	(let ((testfn (decanonicalize-testfn test kb kb-local-only-p)))
	  (if (member old-value values :test testfn)
	      (put-slot-values-internal frame slot
					(substitute new-value old-value values
						    :test testfn)
					kb slot-type value-selector
					kb-local-only-p)
	      :not-found)))
      (progn
	(remove-slot-value-internal frame slot old-value kb test slot-type
				    index value-selector kb-local-only-p)
	(add-slot-value-internal frame slot new-value kb test slot-type index
				 value-selector kb-local-only-p)))
  :tell&ask-default-body
  ((declare (ignore index test))
   (untell-internal (ecase slot-type
		      (:own `(,slot ,frame ,old-value))
		      (:template
		       `(:template-slot-value ,slot ,frame ,old-value)))
		    kb frame value-selector kb-local-only-p)
   (tell-internal (ecase slot-type
		    (:own `(,slot ,frame ,new-value))
		    (:template
		     `(:template-slot-value ,slot ,frame ,new-value)))
		  kb frame value-selector kb-local-only-p))
  :monitor-body
  (record-reference frame slot t nil kb)
  :modification-body
  (record-modification frame kb :modify slot))


(defokbcop okbc:revert-kb (&key (kb (current-kb)) (error-p t))
  :returned-values reverted-kb
  :manual-category :kb
  :doc-string
  "This operation is called when the user wishes to discard any changes
   made to a KB since it was last saved, and revert to the previously saved
   state.

   Equivalent to successive calls to \\kfn{close-kb} and then \\kfn{open-kb}.
   The \\karg{reverted-kb} returned has the same content as \\karg{kb} had at
   the time it was last saved (or empty, if the kb had never
   been saved).  No guarantee is made that the \\karg{reverted-kb}
   will have the same identity (==, EQLness) as \\karg{kb},
   but some implementations may choose to recycle the existing KB object.
   After a call to \\kfn{revert-kb}, portable applications must refer only
   to the \\karg{reverted-kb} object rather than \\karg{kb} in case it was
   not recycled.  References to the original \\karg{kb} may result in
   an \\kcond{object-freed} condition being signaled.
   If \\karg{error-p} is \\false, tries to catch errors that occur, and
   attempts to continue with reverting to the extent possible."
  :causes-side-effects-p t
  :default-body
  (let ((connection (connection kb))
	(kb-type (get-kb-type-internal kb (connection kb))))
    (let ((kb-locator (find-kb-locator-internal kb kb-type connection)))
      (close-kb-internal kb nil)
      (open-kb-internal kb-locator kb-type connection error-p))))

(defokbcop okbc:save-kb (&key (kb (current-kb)) (error-p t))
  :returned-values boolean
  :manual-category :kb
  :doc-string
  "Saves the contents of the KB to persistent storage.  No commitment is
   made as to the location of the KB in persistent storage, other than that
   it will be openable given the name, kb-type and connection first used
   to access it.  No commitment is made as to whether the save operation
   results in a complete dump of the KB, or whether it results only in a
   dump of the changes made since the KB was last saved.  If \\karg{error-p}
   is \\false, tries to catch errors that occur, and attempts to continue 
   with saving to the extent possible.
   Returns \\true\\ iff the KB was saved successfully, and \\false\\
   otherwise."
  :compliance-classes (:write :kb)
  :causes-side-effects-p t)


(defokbcop okbc:save-kb-as
    ((new-name-or-locator :value) &key (kb (current-kb)))
  :returned-values :void
  :manual-category :kb
  :doc-string
  "Saves the entire contents of the KB to persistent storage under the 
   \\karg{new-name-or-locator}.  \\karg{New-name-or-locator} is either a new
   name for the KB, or a new kb-locator.  The in-core KB is renamed so that
   \\kfn{find-kb-of-type} will return \\karg{kb} when passed the new name of
   the KB.  Returns no values."
  :compliance-classes :write
  :causes-side-effects-p t)

(defmethods save-kb-internal :around
  ((kb (kb structure-kb)) (error-p t))
  (let ((result (call-next-method)))
    (when result (setf (kb-has-been-modified-p kb) nil))
    result))

(defmethods save-kb-as-internal :after
  ((new-name-or-locator t) (kb (kb structure-kb)))
  (setf (kb-has-been-modified-p kb) nil))

(defokbcop okbc:slot-has-facet-p
    (frame slot facet &key (kb (current-kb))
	   (inference-level :taxonomic) (slot-type :own)
	   (kb-local-only-p nil))
  :returned-values boolean
  :manual-category :facet
  :doc-string
  "Returns \\true\\ iff \\karg{facet} is a valid facet for \\karg{slot} on
   \\karg{frame}, and \\false\\ otherwise.  What constitutes a valid facet is
   KB-specific, but a facet with a value locally asserted, or with a value
   that is accessible from a template slot will return \\true\\ for this
   operation."
  :standard-default-body
  (member facet (get-slot-facets-internal frame slot kb inference-level
					  slot-type kb-local-only-p))
  :tell&ask-default-body
  (first (ask-internal (ecase slot-type
			 (:own `(:facet-of ,facet ,slot ,frame))
			 (:template `(:template-facet-of ,facet ,slot ,frame)))
		       kb t
		       inference-level 1
		       t nil (timeout-for-tell&ask-defaults kb)
		       :known-true kb-local-only-p))
  :compliance-classes (:read :facets)
  :monitor-body
  (record-reference frame slot t nil kb))


(defokbcop okbc:slot-has-value-p
	  (frame slot &key (kb (current-kb)) (inference-level :taxonomic)
		 (slot-type :own) (value-selector :either)
		 (kb-local-only-p nil))
  :returned-values (boolean exact-p)
  :manual-category :slot
  :doc-string
  "Returns \\true\\ iff \\karg{slot} on \\karg{frame} has at least one
   value, otherwise returns \\false."
  :standard-default-body
  (multiple-value-bind (values exact-p)
      (get-slot-values-internal frame slot kb inference-level slot-type
				1 value-selector kb-local-only-p)
    (values (not (null values)) exact-p))
  :tell&ask-default-body
  (multiple-value-bind (res exact-p)
       (ask-internal
	(ecase slot-type
	  (:own `(,slot ,frame ?value))
	  (:template `(:template-slot-value ,slot ,frame ?value)))
	kb t inference-level 1
	t nil (timeout-for-tell&ask-defaults kb) value-selector kb-local-only-p)
     (values (not (null res)) exact-p))
  :monitor-body
  (record-reference frame slot t nil kb))


(defokbcop okbc:slot-p (thing &key (kb (current-kb)) (kb-local-only-p nil))
  :returned-values boolean
  :manual-category :slot
  :doc-string
  "Returns \\true\\ iff \\karg{thing} is a slot, and
   otherwise returns \\false."
  :tell&ask-default-body
  (first (ask-internal `(:slot ,thing) kb t
		       (inference-level-for-tell&ask-defaults kb) 1
		       t nil (timeout-for-tell&ask-defaults kb)
		       :known-true kb-local-only-p))
  :compliance-classes :read)

(defokbcop okbc:subclass-of-p
    ((subclass :class) (superclass :class)
     &key (kb (current-kb)) (inference-level :taxonomic)
     (kb-local-only-p nil))
  :returned-values (boolean exact-p)
  :manual-category :class
  :doc-string
  "Returns \\true\\ if class \\karg{subclass} is a subclass of class 
   \\karg{superclass}, and returns \\false\\ otherwise."
  :standard-default-body
  (multiple-value-bind (superclasses exact-p)
      (get-class-superclasses-internal
       subclass kb inference-level :all kb-local-only-p)
    (values (member-frame-list superclass superclasses kb kb-local-only-p)
	    exact-p))
  :tell&ask-default-body
  (multiple-value-bind (res exact-p)
      (ask-internal `(:subclass-of ,subclass ,superclass)
		    kb t
		    inference-level 1 t nil (timeout-for-tell&ask-defaults kb)
		    :known-true kb-local-only-p)
    (values (not (null res)) exact-p))
  :monitor-body
  (progn
    (record-reference subclass nil t nil kb)
    (record-reference superclass nil t nil kb)))

(defokbcop okbc:superclass-of-p
    ((superclass :class) (subclass :class)
     &key (kb (current-kb)) (inference-level :taxonomic)
     (kb-local-only-p nil))
  :returned-values (boolean exact-p)
  :manual-category :class
  :doc-string
  "Returns \\true\\ if class \\karg{subclass} is a subclass of class
   \\karg{superclass}, and returns \\false\\ otherwise."
  :standard-default-body
  (subclass-of-p-internal subclass superclass kb inference-level
			  kb-local-only-p)
  :tell&ask-default-body
  (multiple-value-bind (res exact-p)
      (ask-internal `(:subclass-of ,subclass ,superclass)
		    kb t
		    inference-level 1 t nil (timeout-for-tell&ask-defaults kb)
		    :known-true kb-local-only-p)
    (values (not (null res)) exact-p))
  :monitor-body
  (progn
    (record-reference subclass nil t nil kb)
    (record-reference super nil t nil kb)))

(defokbcop okbc:tell ((sentence :value) &key (kb (current-kb)) (frame nil)
		      (value-selector :known-true) (kb-local-only-p nil))
  :returned-values :void
  :manual-category :tell-ask
  :doc-string
  "The \\karg{tell} operation asserts the \\karg{sentence} to be true in
   the knowledge base \\karg{kb}.  Some KRSs may allow users to attach a
   sentence to a specific frame in the KB.  If that is possible and desired, 
   the \\karg{frame} argument may be supplied.  When \\karg{kb-local-only-p}
   is \\true, the \\karg{sentence} should be asserted in the \\karg{kb}, even
   if \\karg{kb} includes another KB containing the \\karg{sentence}.  When the
   \\karg{sentence} argument is syntactically invalid, \\karg{tell} signals
   a \\kcond{syntax-error} error.  A KRS may not accept all valid sentences
   of the OKBC Assertion Language, and for such cases, \\karg{tell} raises the
   condition \\kcond{cannot-handle}.  Returns no values."
  :compliance-classes :write
  :standard-default-body (default-tell
			     sentence kb frame value-selector kb-local-only-p))
  

(defokbcop okbc:tellable ((sentence :value) &key (kb (current-kb))
			  (value-selector :known-true) (kb-local-only-p nil))
  :returned-values boolean
  :manual-category :tell-ask
  :doc-string
  "The \\karg{tellable} operation returns \\false\\ if the KRS can
   determine that \\karg{tell}ing the \\karg{sentence} would result in a
   \\kcond{cannot-handle} error being signaled, and \\true\\ otherwise.
   It may raise a \\kcond{syntax-error} error as specified with the
   definition of \\karg{tell}.  Even if \\karg{tellable} returns
   \\true, \\karg{tell} may still not be able to handle the
   \\karg{sentence}. "
  :standard-default-body
  (default-tellable sentence kb value-selector kb-local-only-p)
  :compliance-classes :read)
  
(defokbcop okbc:type-of-p
    (class thing &key (kb (current-kb))
	   (inference-level :taxonomic) (kb-local-only-p nil))
  :returned-values (boolean exact-p)
  :manual-category :instance
  :doc-string
  "Returns \\true\\ if \\karg{thing} is an instance of \\karg{class}, otherwise
   returns \\false."
  :standard-default-body
  (instance-of-p-internal thing class kb inference-level kb-local-only-p)
  :tell&ask-default-body
  (multiple-value-bind (res exact-p)
      (ask-internal `(:instance-of ,thing ,class)
		    kb t
		    inference-level 1 t nil (timeout-for-tell&ask-defaults kb)
		    :known-true kb-local-only-p)
    (values (not (null res)) exact-p))
  :monitor-body
  (progn
    (record-reference class nil t nil kb)
    (record-reference thing nil t nil kb)))

(defokbcop okbc:unregister-procedure ((name :value) &key (kb (current-kb)))
  :returned-values :void
  :manual-category :funspec
  :causes-side-effects-p t
  :doc-string
  "Removes any procedure association for the \\karg{name} in \\karg{kb}.
   Returns no values."
  :default-body
  ((continuable-assert (symbolp name) ()
		       "Illegal argument ~S to unregister-procedure" name)
   (if name
       (remhash (string-upcase name)
		(name-to-procedure-table kb))
       (continuable-error
	"NIL cannot name a procedure."))))

(defokbcop okbc:untell ((sentence :value) &key (kb (current-kb)) (frame nil)
			(value-selector :known-true) (kb-local-only-p nil))
  :returned-values boolean
  :manual-category :tell-ask
  :doc-string
  "The \\karg{untell} operation can be used to remove assertions from the
   knowledge base.  Returns \\true\\ if the sentence was removed, and 
   \\false\\ otherwise.

   The effect of \\karg{untell}ing a sentence of the OKBC Assertion Language
   is equivalent to the effect of executing an equivalent OKBC operation.  
   The OKBC operations equivalent to \\karg{untell}ing a sentence in the
   Assertion Language are specified in Section~\\ref{sec:untell-semantics}.
   For example, the operation
   \\begin{verbatim}
   (Untell `(slot-name frame-name ,slot-value))
   \\end{verbatim}
   is equivalent to the OKBC operation {\\tt (remove-slot-value 'frame-name
   'slot-name slot-value :slot-type :own).}

   The effect of \\karg{untell}ing an arbitrary \\karg{tellable} sentence
   is not predictable across implementations.  For a given sentence {\\tt
   s}, executing {\\tt (untell s :kb kb)} after executing {\\tt (tell s :kb
   kb)} should remove the sentence {\\tt s} from the {\\tt kb}.  That is, a
   second call to \\karg{untell} should return {\\tt nil}.  This
   does not mean that {\\tt s} is no longer true, as it may be implied by
   other assertions in the KB.

   Some KRSs may allow users to attach an assertion to a frame in the KB.
   If the \\karg{sentence} was attached to a frame, the \\karg{frame}
   argument must be supplied.  The default value for \\karg{frame} is
   \\false.  When the \\karg{sentence} argument is syntactically invalid, it
   may signal the \\kfn{syntax-error} error."
  :compliance-classes :write
  :standard-default-body (default-untell
			     sentence kb frame value-selector kb-local-only-p))
  
;------------------------------------------------------------------------------

(defvar *location-list* :unbound
  "A list of frame location specifications generated during the printing of
   values by <code>value-as-string</code>,
   <code>print-value-to-stream</code>, <code>print-cons-to-stream</code>, and
   <code>print-frame-to-stream</code>.  Each element in the list is of the
   form <code>(&lt;&lt;start-index&gt;&gt; &lt;&lt;end-index&gt;&gt;
   &lt;&lt;frame&gt;&gt;)</code>, where &lt;&lt;start-index&gt;&gt; is the
   index in the output stream as measured by <code>*current-location*</code>
   of the start of the printed representation of the frame, and
   <code>&lt;&lt;end-index&gt;&gt;</code> is the index of the character
   following the printed representation of the frame.  A specification
   must be pushed onto this list for each frame reference printed.  The
   order of the list is important.  It is built up by pushing frame
   specifications on as they are encountered in the printing process.
   When printing is finished the list is reversed.")

(defvar *current-location* :unbound
  "A counter used in the implementation of <code>value-as-string</code>,
   <code>print-value-to-stream</code>, <code>print-cons-to-stream</code>, and
   <code>print-frame-to-stream</code>.  It is the responsibility of any method
   on any of these generic functions to increment this counter by the number
   of characters it prints to the stream.  See also
   <code>*location-list*</code>")

(defokbcop okbc:value-as-string (value &key (kb (current-kb))
				       (purpose :user-interface)
				       (pretty-p (eql purpose :user-interface))
				       (kb-local-only-p nil))
  :returned-values (string location-list)
  :manual-category :misc
  :doc-string
  "Given some \\karg{value}, returns two values, a string that is a printed
   representation of that value, and a list of three-tuples.
   In the second \\karg{location-list} value, one tuple is supplied for each
   frame reference encountered in \\karg{value} in the order they appear
   in the printed representation.  Each three-tuple is of the form
   {\\tt (index0 index1 frame)}, where {\\tt index0} is the zero-indexed
   start index of a printed representation of the
   {\\tt frame} in the printed representation and {\\tt index1} is the
   index one past the end.  For example, printing the list {\\tt (\\#<frame1>)}
   might deliver the values \"(Frame1)\" and {\\tt ((1 8 \\#<frame1>))}.

   This operation is useful for user interfaces that have no way in
   general to print the arbitrary data structures that might be returned by,
   for example, \\kfn{get-slot-values}.  The second value allows user
   interfaces to print the string with mouse-sensitive regions that point to
   frames.\\\\
   \\karg{Purpose}
          -- The \\karg{purpose} argument can be one of \\{{\\tt :file},
             {\\tt :user-interface}\\}.  When it is {\\tt :file}, it allows the
             KB to print data in a manner that will be readable again (e.g.,
             for dumping to files),
             preserving object identity where necessary.  The output will
             therefore typically fully escape strings, and will probably
             package qualify symbols.  When \\karg{purpose} is
             {\\tt :user-interface}, the string returned will be as pretty
             and readable as possible for a user interface, but such
             output will probably not be readable by OKBC.\\\\
   \\karg{Pretty-p}
           -- When \\true, OKBC will attempt to print everything in as pretty a
              manner as possible.  This includes printing frames by using their
              pretty-names, and by printing strings without escaping or
              quotes."
  :default-body
    (let ((*location-list* nil)
	  (*current-location* 0))
      (declare (special *current-location* *location-list*))
      (values
       (with-output-to-string (stream)
	 (implement-with-kb-io-syntax-internal
	  #'(lambda ()
	      (let ((*print-readably*
		     (ecase purpose (:file t) (:user-interface nil))))
		(if pretty-p
		    (let ((*print-escape* (not pretty-p)))
		      (print-value-to-stream value stream kb purpose pretty-p
					     nil kb-local-only-p 0))
		    (print-value-to-stream value stream kb purpose pretty-p
					   nil kb-local-only-p 0))))
	  kb purpose kb-local-only-p))
       (reverse *location-list*)))
  :monitor-body
  (record-reference frame nil t nil kb))

(defokbcgeneric print-value-to-stream
    (thing stream kb purpose pretty-p inside-quote-p kb-local-only-p indent)
  (:documentation
   "Internal back-end protocol used in the definition of
    <code>value-as-string</code>.  Arguments are the same as for
    <code>value-as-string</code>, except <code>indent</code> is the current
    indent in characters from the left margin, and <code>inside-quote-p</code>
    is true if we are inside a quote.  The latter is important because frame
    coercions are not performed inside quotes.<P>
    See also <code>print-cons-to-stream</code>,
    <code>print-frame-to-stream</code>, <code>*current-location*</code>, and
    <code>*location-list*</code>."))

(defmethods print-value-to-stream ((thing cons) (stream t)
				   (kb (kb structure-kb)) (purpose t)
				   (pretty-p t) (inside-quote-p t)
				   (kb-local-only-p t) (indent t))
  (let ((key (and (symbolp (first thing))
		  (find-symbol (symbol-name (first thing))
			       ok-back:*keyword-package*))))
    (print-cons-to-stream key (first thing) thing stream kb purpose pretty-p
			  inside-quote-p kb-local-only-p indent)))

(defokbcgeneric print-cons-to-stream
    (key car thing stream kb purpose pretty-p inside-quote-p kb-local-only-p
	 indent)
  (:documentation
   "Internal back-end protocol used in the definition of
    <code>value-as-string</code>, which is called when printing list structure.
    Arguments are the same as for <code>value-as-string</code>, except:<DL>
    <DT><code>key</code>
    <DD>is a keyword denoting the symbol in the car of the list if the car is
    a symbol, and if such a keyword exists.  For example, if we hit a quotation
    term, then this argument will be <code>:quote</code>.  This argument
    allows eql dispatch on a package canonicalized version of the car of
    the list.
    <DT><code>car</code>
    <DD>is the first element of the list.  For example, if we hit a quotation
    term, then this argument may be <code>lisp:quote</code>.  This argument
    allows eql dispatch on the car of the list.
    <DT><code>indent</code>
    <DD>is the current indent in characters from the left margin.
    <DT><code>inside-quote-p</code>
    <DD>is true if we are inside a quote.  This latter is important because
    frame coercions are not performed inside quotes.</DL>
    See also <code>print-value-to-stream</code>,
    <code>print-frame-to-stream</code>, <code>*current-location*</code>, and
    <code>*location-list*</code>."))

(defmethods print-cons-to-stream ((key (eql :quote)) (car t) (thing cons)
				  (stream t) (kb (kb structure-kb)) (purpose t)
				  (pretty-p t) (inside-quote-p t)
				  (kb-local-only-p t) (indent t))
  (declare (special *current-location*))
  (if (and (= (length thing) 2) (or (eq car 'quote) (not (eq purpose :file))))
      (progn (princ "'" stream)
	     (incf *current-location*)
	     (print-value-to-stream (second thing) stream kb purpose pretty-p
				    t kb-local-only-p (+ indent 1)))
      (call-next-method)))

(defmethods print-cons-to-stream ((key (eql :function)) (car t) (thing cons)
				  (stream t) (kb (kb structure-kb)) (purpose t)
				  (pretty-p t) (inside-quote-p t)
				  (kb-local-only-p t) (indent t))
  (declare (special *current-location*))
  (if (and (= (length thing) 2)
	   (or (eq car 'function) (and (not (eq purpose :file)))))
      (progn (princ "#'" stream)
	     (incf *current-location* 2)
	     (print-value-to-stream (second thing) stream kb purpose pretty-p
				    t kb-local-only-p (+ indent 1)))
      (call-next-method)))

(defmethods print-cons-to-stream ((key t) (car t) (thing cons) (stream t)
				  (kb (kb structure-kb)) (purpose t)
				  (pretty-p t) (inside-quote-p t)
				  (kb-local-only-p t) (indent t))
  ;; Define a trivial pretty printer.  If you want something better,
  ;; you can do a pp-stream hack.
  (declare (special *current-location*))
  (princ "(" stream)
  (incf *current-location*)
  (loop for element = (pop thing)
	for count from 0
	do (print-value-to-stream element stream kb purpose pretty-p
				  inside-quote-p kb-local-only-p
				  (if (zerop count)
				      (+ indent 1)
				      (+ indent 3)))
	(cond ((not thing) (return nil))
	      ((consp thing)
	       (if pretty-p
		   (progn (terpri stream)
			  (loop for i from 0 below (+ indent 3)
				do (princ " " stream))
			  (incf *current-location* (+ indent 4)))
		   (progn (princ " " stream)
			  (incf *current-location*))))
	      (t (if pretty-p
		     (progn (terpri stream)
			    (loop for i from 0 below (+ indent 3)
				  do (princ " " stream))
			    (princ ". " stream)
			    (incf *current-location* (+ indent 5)))
		     (progn (princ " . " stream)
			    (incf *current-location* 3)))
		 (print-value-to-stream
		  thing stream kb purpose pretty-p inside-quote-p
		  kb-local-only-p (+ indent 5))
		 (return nil))))
  (princ ")" stream)
  (incf *current-location*))

(defmethods print-cons-to-stream ((key (eql :define-okbc-frame)) (car t)
				  (thing cons) (stream t)
				  (kb (kb structure-kb)) (purpose t)
				  (pretty-p t) (inside-quote-p t)
				  (kb-local-only-p t) (indent t))
  ;; Define a trivial pretty printer for OKBC source forms.  If you want
  ;; something better, you can do a pp-stream hack.
  (declare (special *current-location*))
  (princ "(" stream)
  (incf *current-location*)
  (print-value-to-stream (pop thing) stream kb purpose pretty-p
			 inside-quote-p kb-local-only-p
			 (+ indent 1))
  (princ " " stream)
  (incf *current-location*)
  (print-value-to-stream (pop thing) stream kb purpose pretty-p
			 inside-quote-p kb-local-only-p
			 (+ indent 1))
  (when thing
    (loop for key = (pop thing)
	  for value = (pop thing)
	  for l = (length (prin1-to-string key))
	  do
	  (terpri stream)
	  (incf *current-location*)
	  (loop for i from 0 below (+ indent 2) do (princ " " stream))
	  (incf *current-location* (+ indent 2))
	  (primitive-print-value-to-stream key stream nil)
	  (princ " " stream)
	  (incf *current-location*)
	  (print-value-to-stream value stream kb purpose pretty-p
				 inside-quote-p kb-local-only-p
				 (+ indent l 2))
	  while thing))
  (princ ")" stream)
  (incf *current-location*))

(defun primitive-print-value-to-stream (thing stream pretty-p)
  (declare (special *current-location*))
  (if (and (null thing) (not pretty-p))
      (multiple-value-bind
	  (sym found-p) (find-symbol "NIL" *package*)
	  (if (or (and found-p (not (eq thing sym))) (not found-p))
	      (let ((string "()"))
		(princ string stream)
		(incf *current-location* (length string)))
	      (let ((string (prin1-to-string thing)))
		(princ string stream)
		(incf *current-location* (length string)))))
      (let ((string (if pretty-p
			(princ-to-string thing)
			(prin1-to-string thing))))
	(princ string stream)
	(incf *current-location* (length string)))))

(defmethods print-value-to-stream
    ((thing t) (stream t) (kb (kb structure-kb))
     (purpose t) (pretty-p t) (inside-quote-p t) (kb-local-only-p t) (indent t))
  (primitive-print-value-to-stream thing stream pretty-p))

(defmethods print-value-to-stream :around
  ((thing t) (stream t) (kb (kb structure-kb)) (purpose t) (pretty-p t)
   (inside-quote-p t) (kb-local-only-p t) (indent t))
  (if (stringp thing)
      ;; Even if a string is coercible-to-frame-p, we don't want to do
      ;; this coercion because it is a literal.
      (call-next-method)
      (multiple-value-bind (frame found-p)
	(coerce-to-frame-internal thing kb nil kb-local-only-p)
	(if (and found-p (or (not inside-quote-p) (eq thing frame)))
	    ;; No actual coercion allowed inside quotes.
	    (print-frame-to-stream
	     frame stream kb purpose pretty-p kb-local-only-p)
	    (call-next-method)))))

(defokbcgeneric print-frame-to-stream
    (frame stream kb purpose pretty-p kb-local-only-p)
  (:documentation
   "Internal back-end protocol used in the definition of
    <code>value-as-string</code>.  Called when the printer hits a frame
    reference.  Arguments are the same as for <code>value-as-string</code>.<P>
    See also <code>print-cons-to-stream</code>,
    <code>print-value-to-stream</code>, <code>*current-location*</code>, and
    <code>*location-list*</code>."))

(defmethods print-frame-to-stream
    ((frame t) (stream t) (kb (kb structure-kb))
     (purpose t) (pretty-p t) (kb-local-only-p t))
  (declare (special *current-location* *location-list*))
  (multiple-value-bind (thing-to-print? error-found-p)
    (ignore-errors (if (or pretty-p (eq :user-interface purpose))
		       (list (get-frame-pretty-name-internal
			      frame kb kb-local-only-p)
			     t)
		       (if (not (member nil (get-behavior-values-internal
					     :frame-names-required kb)))
			   (list (or (get-frame-name-internal
				      frame kb kb-local-only-p)
				     frame)
				 nil)
			   (list (get-frame-handle-internal
				  frame kb kb-local-only-p)
				 nil))))
    (let ((thing-to-print
	   (if error-found-p
	       (if pretty-p (princ-to-string frame) (prin1-to-string frame))
	       (destructuring-bind (thing-to-print already-string-p)
		   thing-to-print?
		 (if already-string-p
		     (princ-to-string thing-to-print)
		     (if pretty-p
			 (princ-to-string thing-to-print)
			 (prin1-to-string thing-to-print)))))))
      (princ thing-to-print stream)
      (push (list *current-location*
		  (+ *current-location* (length thing-to-print))
		  frame)
	    *location-list*)
      (incf *current-location* (length thing-to-print)))))

;------------------------------------------------------------------------------

