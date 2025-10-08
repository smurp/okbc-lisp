;;; -*- MODE :Lisp; Syntax:Common-Lisp; Package:OK-Kernel; Base:10  -*- 

(in-package :ok-kernel)

(defokbcop okbc:add-class-superclass (class (new-superclass :class)
					    &key (kb (current-kb))
					    (kb-local-only-p nil))
  :returned-values :void
  :manual-category :class
  :doc-string
  "Adds the \\karg{new-superclass} to the superclasses of \\karg{class}.
   Returns no values."
  :compliance-classes :write
  :standard-default-body
  (put-class-superclasses-internal
   class
   (adjoin new-superclass
	   (get-class-superclasses-internal class kb :direct :all
					    kb-local-only-p)
	   :test (decanonicalize-testfn :eql kb kb-local-only-p))
   kb kb-local-only-p)
  :tell&ask-default-body
  (tell-internal `(:subclass-of ,class ,new-superclass)
		 kb class :known-true kb-local-only-p)
  :causes-side-effects-p t
  :monitor-body
  (progn 
    (record-reference class nil t nil kb)
    (record-reference new-superclass nil t nil kb))
  :modification-body 
  (record-modification class kb :modify))

(defokbcop okbc:add-facet-value (frame slot facet value
				       &key (kb (current-kb)) (test :equal)
				       (slot-type :own) 
				       (value-selector :known-true)
				       (kb-local-only-p nil))
  :returned-values :void
  :manual-category :facet
  :doc-string
  "If the specified facet does not already contain \\karg{value}, 
   then \\karg{value} is added to the set of values of the facet.
   Returns no values."
  :causes-side-effects-p t
  :standard-default-body ;; SMP added 10/24/94
  (put-facet-values-internal 
   frame slot facet 
   (adjoin value
	   (get-facet-values-internal frame slot facet kb :direct slot-type
				      :all value-selector kb-local-only-p) 
	   :test (decanonicalize-testfn test kb kb-local-only-p))
   kb slot-type value-selector kb-local-only-p)
  :tell&ask-default-body
  ((declare (ignore test))
   (tell-internal (ecase slot-type
		    (:own `(,facet ,slot ,frame ,value))
		    (:template `(:template-facet-value
				 ,facet ,slot ,frame ,value)))
		  kb frame value-selector kb-local-only-p))
  :monitor-body
  (record-reference frame slot t nil kb)
  :modification-body
  (if frame
      (record-modification frame kb :modify slot)
    (record-modification slot kb :modify)))


(defokbcop okbc:add-instance-type
    (frame (new-type :class) &key (kb (current-kb)) (kb-local-only-p nil))
  :returned-values :void
  :manual-category :instance
  :doc-string
  "Adds the \\karg{new-type} to the types of \\karg{frame}.
   Returns no values."
  :compliance-classes :write
  :standard-default-body
  (put-instance-types-internal
   frame
   (adjoin new-type
	   (get-instance-types-internal frame kb :direct :all kb-local-only-p)
	   :test (decanonicalize-testfn :eql kb kb-local-only-p))
   kb kb-local-only-p)
  :tell&ask-default-body
  (tell-internal `(:instance-of ,frame ,new-type)
		 kb frame :known-true kb-local-only-p)
  :causes-side-effects-p t
  :monitor-body
  (progn (record-reference frame nil t nil kb)
	 (record-reference new-type nil t nil kb))
  :modification-body 
  (record-modification frame kb :modify))

(defokbcop okbc:add-slot-value (frame slot value &key
				      (kb (current-kb))
				      (test :equal)
				      (slot-type :own)
				      (add-before 0)
				      (value-selector :known-true)
				      (kb-local-only-p nil))
  :returned-values :void
  :manual-category :slot
  :doc-string
  "\\karg{Value} is added to the set of values of \\karg{slot}.  If the
   collection-type of \\karg{slot} is {\\tt :set}, then \\karg{value} is
   added only if \\karg{slot} does not already contain \\karg{value}.  
   \\karg{Add-before}, if supplied, should be \\false\\ or a nonnegative
   integer.  If the collection-type of
   \\karg{slot} is {\\tt :list}, \\karg{value} is added immediately before
   the value whose index is \\karg{add-before}.  For example, if
   \\karg{add-before} is 1, the new value will be added between the first
   and second old values.  If \\karg{add-before} is greater than or equal
   to the current number of slot values, or is \\false, and the
   collection-type of \\karg{slot} is {\\tt :list}, then \\karg{value} is
   added after all other values.  This operation may signal constraint
   violation conditions (see Section~\\ref{sec:errors}).  It is an error
   to provide a nonpositive integer as a value for \\karg{add-before}.
   Returns no values."
  :causes-side-effects-p t
  :standard-default-body
  (let ((values (get-slot-values-internal frame slot kb :all-inferable
					  slot-type :all value-selector
					  kb-local-only-p))
	(collection-type (get-collection-type frame slot kb slot-type
					      kb-local-only-p))
	)
    (if (eq collection-type :none)
	(put-slot-value-internal frame slot value kb slot-type value-selector
				 kb-local-only-p)
      (unless (and (eq collection-type :set)
		   (member value values
			   :test (decanonicalize-testfn
				  test kb kb-local-only-p)))
	;; Only put local values.  This prevents inherited values
	;; from being asserted locally as a result of a single add.
	(put-slot-values-internal frame slot
				  (nconc (subseq values 0 (or add-before 0))
					 (cons value
					       (nthcdr (or add-before 0)
						       values)))
				  kb slot-type value-selector
				  kb-local-only-p))))
  :tell&ask-default-body
  ((declare (ignore add-before test))
   (tell-internal (ecase slot-type
		    (:own `(,slot ,frame ,value))
		    (:template
		     `(:template-slot-value ,slot ,frame ,value)))
		  kb frame value-selector kb-local-only-p))
  :monitor-body
  (record-reference frame slot t nil kb)
  :modification-body
  (record-modification frame kb :modify slot))



(defparameter *existing-connections*
  (make-hash-table :test #'equal)
  "The hash table mapping connection specifications to all of the known
   connections.  This is used by <code>establish-connection</code> to make sure
   that an existing connection is returned if it is called with the same
   args on multiple occasions.")

(defokbcop okbc:all-connections ()
  :returned-values list-of-connections
  :manual-category :connection
  :enumerator t
  :doc-string "Returns a list of all of the known connections."
  :default-body
  (let ((connections nil))
    (maphash #'(lambda (key value)
		 (declare (ignore key))
		 (push value connections))
	     *existing-connections*)
    connections))

(defokbcop okbc:allocate-frame-handle
    ((frame-name :value) (frame-type :value)
     &key (kb (current-kb)) (frame-handle nil))
  :returned-values frame-handle
  :manual-category :frame
  :doc-string
  "Allocates a frame handle in \\karg{kb}.  It is not anticipated that this
   operation will be called by OKBC applications, but rather by OKBC back end
   implementations.  This operation can be used in two distinct ways:
   \\begin{enumerate}
   \\item Given a frame located in an arbitrary KB, typically different
   from \\karg{kb}, passing its \\karg{frame-name}, \\karg{frame-type}, and
   \\karg{frame-handle} will return a frame handle to represent that frame if
   such a frame were to be created in \\karg{kb}.  This is useful in OKBC
   operations such as \\kfn{copy-frame} and \\kfn{copy-kb} where it is often
   necessary to make forward references to frame objects.  
   \\item Providing just a \\karg{frame-name} and a \\karg{frame-type}
   will return a frame handle to represent that frame if such a frame were
   to be created in \\karg{kb}.  This is useful when an implementation wants
   to allocate a frame handle either during the frame creation process, or
   to create forward references to frames when faulting them in from a
   lazy persistent store.  \\karg{Frame-name} may be \\false.
   \\end{enumerate}
   \\karg{Frame-type} is the type of the frame as identified by the operation
   \\kfn{get-frame-type}; that is, it must be in the set \\{{\\tt :class},
   {\\tt :individual}, {\\tt :slot}, {\\tt :facet}\\}.

   The rationale for the arguments to this operation is as follows:
   \\bitem
   \\item \\karg{frame-name} -- In some KRSs, the name of a frame cannot be
          changed after the frame handle has been allocated.  OKBC therefore
          mandates that the name be supplied.  If the
          {\\tt :frame-names-required} behavior has the value \\false,
          this argument may be \\false.
   \\item \\karg{frame-type} -- In some KRSs, the type of data structure used
          to represent the frame handles of (say) classes is completely
          different from that of (say) individual frames.  OKBC therefore
          mandates that the frame type be specified.  Implementations that use
          the same representation for all frame handles will be able to ignore
          this argument, but it is not portable.
   \\item \\karg{frame-handle} -- Some KRSs may choose to use a frame handle
          provided as the value of the \\karg{frame-handle} argument as the
          new frame handle.  This allows implementations that do not have a
          special data structure for frame handles to save memory and to
          maximize the correspondence between the objects in different KBs.
   \\eitem
   The contract of \\kfn{allocate-frame-handle} does not require the callee to
   return the same frame handle if called multiple times with identical
   arguments.  Note that this is particularly important in case 2, above,
   with \\karg{frame-name} being \\false.  It is the responsibility of
   the caller to remember the
   correspondence between its frames and the frame handles allocated.  A frame
   handle allocated using \\kfn{allocate-frame-handle} can be used as the
   value of the \\karg{handle} argument to \\kfn{create-frame},
   \\kfn{create-class}, \\kfn{create-slot}, \\kfn{create-facet}, and
   \\kfn{create-individual}.  During the execution of these operations, it is
   the responsibility of the \\karg{kb} to preserve any necessary object
   identity so that, for example,
   \\begin{verbatim}
   new-handle = allocate-frame-handle(name, :class, kb, handle);
   new-frame = create-class(name, .... :handle new-handle);
   new-handle == get-frame-handle(new-frame) // this identity must hold!
   \\end{verbatim}"
  :compliance-classes (:write :network/copy)
  :causes-side-effects-p t)

(defokbcop okbc:ask
    ((query :value) &key (kb (current-kb)) (reply-pattern query)
     (inference-level :taxonomic) (number-of-values :all)
     (error-p t) (where nil) (timeout nil)
     (value-selector :either) (kb-local-only-p nil))
  :enumerator t
  :doc-string
  "Asks a \\karg{query} of the OKBC \\karg{kb}.  \\karg{Query} may be any
   sentence in the OKBC Assertion Language that is \\kfn{askable}.  A
   \\kcond{cannot-handle} error
   may be signaled if it is not \\karg{askable}. \\karg{Reply-pattern} is an
   expression mentioning KIF variables contained in \\karg{query}.

   \\karg{Reply-pattern} is any list structure mentioning the variables
   in the query, or just the name of a variable.  For example, consider
   a query that is a sentence of the form,
   \\begin{verbatim}
     (subclass-of ?x ?y)
   \\end{verbatim}
   that is, find me the things that are subclasses of other things.  If there
   is a match in the KB for {\\tt ?x = human} and {\\tt ?y = animal}.
   -- the class {\\tt human} is a subclass of the class {\\tt animal} -- then
   if the \\karg{reply-pattern} were to be
   \\begin{verbatim}
     (superclass-of ?y ?x)
   \\end{verbatim}
   we would be returned a list of sentences of which one
   would be {\\tt (superclass-of animal human)}.  The explicit use of a reply
   pattern in this manner allows the user to get either sentences
   that can be conveniently reasserted using \\kfn{tell}, or tuples of
   matches in a shape that is convenient to the application.

   When \\karg{error-p} is \\true, any errors resulting from the execution of
   the query are signaled.  When error-p is \\false, all possible attempts are
   made to continue with the query and deliver as many results as were
   requested.

   If the resources used by \\karg{ask} are a concern, the time (in
   seconds) allowed to answer a query will be limited, if possible, as
   specified by \\karg{timeout}.  If the value of \\karg{timeout} is
   \\false, an unlimited time is allowed for \\karg{ask} to complete.

   The \\karg{where} clause can be used to specify a list of bindings to
   be used for any variables appearing in the \\karg{query}.  During query
   evaluation, such variables are replaced by the values specified by
   \\karg{where}.  A valid value of \\karg{where} is a list of 2-tuples,
   with each tuple consisting of a variable and value pair.

   \\karg{Ask} returns three values.
   \\begin{enumerate}
   \\item \\karg{reply-pattern-list} -- In this list, each element is an
          instance of \\karg{reply-pattern}, with all variables mentioned in
          \\karg{query} substituted.
   \\item \\karg{exact-p} -- This has its normal interpretation.
   \\item \\karg{more-status} -- This has its normal interpretation, except
          that an additional option {\\tt :timeout} may be returned for the
          more-status value by \\karg{ask} if the call terminates because
          execution time exceeds the limit specified by the \\karg{timeout}
          argument.
   \\end{enumerate}
   When \\karg{ask} is given a syntactically invalid \\karg{query}, it
   signals the \\kcond{syntax-error} error.  When \\karg{ask} realizes that
   the \\karg{query} cannot be handled by the KRS, it signals a
   \\kcond{cannot-handle} error.

   The following query matches four channel oscilloscopes with a
   bandwidth greater than 80MHz.  It returns a list of pairs {\\tt
   (?osc ?bandwidth)} satisfying the query.
   \\begin{verbatim}
   (ask '(and (oscilloscope ?osc)
              (number-of-channels ?osc ?chans)
              (= ?chans 4)
              (bandwidth ?osc ?bandwidth)
              (> ?bandwidth (* 80 mega-hertz)))
         :reply-pattern '(?osc ?bandwidth)
         :number-of-values 10 :kb kb)
   \\end{verbatim}
   All KIF operators in the \\karg{query} are parsed in a
   package-insensitive manner.  For example, {\\tt (and A B)} and {\\tt
   (:and A B)} have the same effect.  Object, relation, and function constant
   references in \\karg{query} are taken as arguments to 
   \\kfn{get-frames-matching}.  Frame references in the query must uniquely 
   identify frames.  (See \\kfn{get-frames-matching}.)"
  :returned-values (reply-pattern-list exact-p more-status)
  :manual-category :tell-ask
  :standard-default-body
  (default-ask query reply-pattern kb inference-level
			     number-of-values error-p where timeout
			     value-selector kb-local-only-p))


(defokbcop okbc:askable ((sentence :value) &key (kb (current-kb))
			 (value-selector :either) (kb-local-only-p nil))
  :returned-values boolean
  :manual-category :tell-ask
  :doc-string
  "The \\karg{askable} operation returns \\false\\ if the KRS can
   determine that \\karg{ask}ing the \\karg{sentence} would result in a
   \\kcond{cannot-handle} error being signaled, and \\true\\ otherwise.
   It may also signal the \\kcond{syntax-error} condition.  Even if
   \\karg{askable} returns \\true,
   \\karg{ask} may still not be able to handle the \\karg{sentence}."
  :standard-default-body
  (default-askable sentence kb value-selector kb-local-only-p)
  :compliance-classes :read)


(defokbcop okbc:attach-facet (frame slot facet &key (kb (current-kb))
				    (slot-type :own) (kb-local-only-p nil))
  :returned-values :void
  :manual-category :facet
  :doc-string
  "Explicitly associates the \\karg{facet} with \\karg{slot} on \\karg{frame},
   in the sense of recording that values of the facet may be asserted with
   \\karg{frame} or with instances of \\karg{frame} if \\karg{slot-type} is
   {\\tt :template}.
   As a result, \\karg{facet} is returned by \\kfn{get-slot-facets} at the
   {\\tt :direct} inference level, and \\karg{slot-has-facet-p} will be
   \\true\\ for \\karg{facet} in \\karg{slot} on \\karg{frame}.  It is an
   error to attempt to attach a non-existent facet.  Doing so should signal
   a \\kcond{facet-not-found} error.  Returns no values."
  :causes-side-effects-p t
  :tell&ask-default-body
  (tell-internal `(,(ecase slot-type
			   (:own :facet-of)
			   (:template :template-facet-of))
		   ,facet ,slot ,frame)
		 kb frame :known-true kb-local-only-p)
  :compliance-classes :write
  :monitor-body
  (record-reference frame slot t nil kb)
  :modification-body
  (record-modification frame kb :modify slot))

(defokbcop okbc:attach-slot (frame slot &key (kb (current-kb)) (slot-type :own)
				   (kb-local-only-p nil))
  :returned-values :void
  :manual-category :slot
  :doc-string
  "Explicitly associates the \\karg{slot} with \\karg{frame}, in the sense
   of recording that values of slot may be asserted with \\karg{frame} or
   with instances of \\karg{frame} if \\karg{slot-type} is {\\tt :template}.
   As a result, \\karg{slot} is returned by \\kfn{get-frame-slots} at the
   {\\tt :direct} inference level, and \\karg{frame-has-slot-p} will be
   \\true\\ for \\karg{slot} on \\karg{frame}.  It is an error to attempt to
   attach a non-existent slot.  Doing so should signal a
   \\kcond{slot-not-found} error.  Returns no values."
  :causes-side-effects-p t
  :tell&ask-default-body
  (tell-internal `(,(ecase slot-type
			   (:own :slot-of)
			   (:template :template-slot-of))
		   ,slot ,frame)
		 kb frame :known-true kb-local-only-p)
  :compliance-classes :write
  :monitor-body
  (record-reference frame slot t nil kb)
  :modification-body
  (record-modification frame kb :modify slot))

(defokbcop okbc:call-procedure (procedure
				&key (kb (current-kb))
				(arguments nil))
  :returned-values value
  :manual-category :funspec
  :enumerator t
  :doc-string
  "Returns the \\karg{value} resulting from applying
   \\karg{procedure} to
   \\karg{arguments}.  See section~\\ref{ch:funspecs} for a definition of
   procedures."
  :default-body (apply procedure arguments))

(defokbcop okbc:class-p (thing &key (kb (current-kb)) (kb-local-only-p nil))
  :returned-values boolean
  :manual-category :class
  :doc-string
  "Returns \\true\\ if \\karg{thing} identifies a class."
  :compliance-classes :read
  :tell&ask-default-body
  (first (ask-internal `(:class ,thing) kb t
		       (inference-level-for-tell&ask-defaults kb) 1
		       t nil (timeout-for-tell&ask-defaults kb)
		       :known-true kb-local-only-p))
  :monitor-body
  (record-reference thing nil t nil kb))


(defokbcop okbc:close-connection (connection &key (force-p nil) (error-p t))
  :returned-values :void
  :manual-category :connection
  :doc-string
  "Closes the \\karg{connection}.  If \\karg{force-p} is \\true, the connection
   may be closed without waiting for any handshakes from the server.  A call
   to close-connection on the local connection
   is a no-op.  This allows the user to loop through \\kfn{all-connections},
   closing them all without fear of losing connectivity to KBs that share the
   same address space as the application.  Returns no values."
  :compliance-classes :read)

(defmethods close-connection-internal ((connection (kb structure-kb))
				       (force-p t) (error-p t))
  (close-connection-internal (connection connection) force-p error-p))

(defmethod close-connection-internal
    ((connection ok-back:connection) (force-p t) (error-p t))
  nil) ;; nothing to do in the base case.

(defmethod close-connection-internal :around
  ((connection ok-back:connection) (force-p t) (error-p t))
  (let ((matching-key nil))
    (maphash #'(lambda (key value)
		 (when (eq connection value) (setq matching-key key)))
	     *existing-connections*)
    (when (not matching-key)
      (cond ((and error-p (not force-p))
	     (continuable-error
	      "Internal error.  Cannot find key entry for connection ~S.  To ~
               close this connection you will have to use :force-p t"
	      connection))
	    (t (warn
		"Internal error.  Cannot find key entry for connection ~S.  To ~
                 close this connection you will have to use :force-p t"
		connection))))
    (unwind-protect
	 (if error-p
	     (call-next-method)
	     (ignore-errors (call-next-method)))
      (when (not (typep connection 'local-connection))
	(setf (open-p connection) nil)
	(when matching-key (remhash matching-key *existing-connections*))))))

(defokbcop okbc:close-kb (&key (kb (current-kb)) (save-p nil))
  :returned-values :void
  :manual-category :kb
  :doc-string
  "Deletes any in-core/accessible representation of \\karg{kb}, but does not
   remove it from any persistent store if the persistent version still
   constitutes a meaningful KB (i.e., temporary disk work files would be
   deleted).  It is an error ever to use \\karg{kb} again for any purpose.  If
   this occurs, an \\kcond{object-freed} error should be signaled.
   Implementations may free any storage allocated for KB.  If \\karg{save-p}
   is \\true, then any unsaved changes to \\karg{kb} will be saved
   before it is closed.  Note that the default value of \\karg{save-p}
   is \\false.  Returns no values."
  :compliance-classes (:write :kb)
  :causes-side-effects-p t)

(defokbcop okbc:coerce-to-class (thing &key (kb (current-kb)) (error-p t)
				       (kb-local-only-p nil))
  :returned-values (class class-found-p)
  :manual-category :class
  :doc-string
  "Coerces \\karg{thing} to a class.  This operation returns two values.
   \\bitem
   \\item \\karg{class} -- If \\karg{thing} identifies a class for \\karg{kb},
                           then this value is the class so identified, or
                           \\false otherwise.
   \\item \\karg{class-found-p} -- If the class is found then \\true,
                                   otherwise \\false.
   \\eitem
   If \\karg{error-p} is \\true and the class is not found, then a
   \\kcond{class-not-found} error is signaled.

   It is an error to call \\kfn{coerce-to-class} with \\karg{error-p} being
   \\true, and with a value of \\karg{thing} that does not uniquely identify
   a class.  If this happens, a \\kcond{not-unique-error} error should be
   signaled.

   Note that in some KRS, \\false\\ may be a valid class.  No portable
   program may assume that a returned value of \\false\\ for the first
   (\\karg{class}) returned value implies that \\karg{class-found-p}
   is \\false."
  :default-body
  (if (member :class (get-behavior-values-internal :are-frames kb))
      (multiple-value-bind (class found-p)
	  (coerce-to-frame-internal thing kb nil kb-local-only-p)
	(if (and found-p (class-p-internal class kb kb-local-only-p))
	    (values class found-p)
	    (if error-p
		(error 'class-not-found
		       :missing-class thing
		       :continuable t
		       :kb kb)
		(values nil nil))))
      (if (class-p-internal thing kb kb-local-only-p)
	  (values thing t)
	  (if error-p
	      (error 'class-not-found
		     :missing-class thing
		     :continuable t
		     :kb kb)
	      (values nil nil))))
  :compliance-classes :read
  :monitor-body
  (record-reference thing nil t nil kb))

(defokbcop okbc:coerce-to-facet (thing &key (kb (current-kb)) (error-p t)
				       (kb-local-only-p nil))
  :returned-values (facet facet-found-p)
  :manual-category :facet
  :doc-string
  "Coerces \\karg{thing} to a facet.  This operation returns two values.
   \\bitem
   \\item \\karg{facet} -- If \\karg{thing} identifies a facet for \\karg{kb},
                           then this value is the facet so identified, or
                           \\false otherwise.
   \\item \\karg{facet-found-p} -- If the facet is found then \\true,
                                   otherwise \\false.
   \\eitem
   If \\karg{error-p} is \\true and the facet is not found, then a
   \\kcond{slot-not-found} error is signaled.

   It is an error to call \\kfn{coerce-to-facet} with \\karg{error-p} being
   \\true, and with a value of \\karg{thing} that does not uniquely identify
   a facet.  If this happens, a \\kcond{not-unique-error} error should be
   signaled.

   Note that in some KRS, \\false\\ may be a valid facet.  No portable
   program may assume that a returned value of \\false\\ for the first
   (\\karg{facet}) returned value implies that \\karg{facet-found-p} is
   \\false."
  :default-body
  (if (member :facet (get-behavior-values-internal :are-frames kb))
      (multiple-value-bind (facet found-p)
	  (coerce-to-frame-internal thing kb nil kb-local-only-p)
	(if (and found-p
		 (facet-p-internal facet kb kb-local-only-p))
	    (values facet found-p)
	    (if error-p
		(error 'facet-not-found
		       :frame nil
		       :slot nil
		       :facet thing
		       :slot-type nil
		       :continuable t
		       :kb kb)
		(values nil nil))))
      (if (facet-p-internal thing kb kb-local-only-p)
	  (values thing t)
	  (if error-p
	      (error 'facet-not-found
		     :frame nil
		     :slot nil
		     :facet thing
		     :slot-type nil
		     :continuable t
		     :kb kb)
	      (values nil nil))))
  :compliance-classes :read
  :monitor-body
  (record-reference thing nil t nil kb))

(defokbcop okbc:coerce-to-frame (thing &key (kb (current-kb)) (error-p t)
				       (kb-local-only-p nil))
  :doc-string
  "Coerces \\karg{thing} to be a frame object, if such an object exists for
   the underlying KRS, or a frame handle otherwise.  \\karg{Thing} can be a
   frame object or a frame handle.  This operation may be
   less careful than \\kfn{get-frame-in-kb} about ensuring that the
   frame for \\karg{thing} is actually in \\karg{kb} when the supplied
   \\karg{thing} is a frame object.  \\kfn{Coerce-to-frame} verifies that
   \\karg{thing} is the
   appropriate {\\it type} of frame object for \\karg{kb}, but may not
   actually determine whether the frame resides in \\karg{kb}.  Therefore, this
   operation may be faster than \\kfn{get-frame-in-kb} for some KRSs.

   For user convenience, implementors are encouraged to support the coercion
   into a frame of any data-structure that uniquely identifies a frame in
   the KRS as well as frame handles and frame objects.  It is not
   portable to provide any value for \\karg{thing} other than a frame
   object or frame handle; \\kfn{get-frames-matching} should be used instead.

   If the {\\tt :frame-names-required} behavior has the value \\true\\ for
   \\karg{kb}, the names of frames are always coercible to frames.
   If the {\\tt :frame-names-required} behavior is \\false, frame names
   (if defined) are not guaranteed to be coercible to frames.

   This operation returns two values.
   \\bitem
   \\item \\karg{frame} -- If \\karg{thing} identifies a frame for \\karg{kb},
                           then this value is the frame so identified, or
                           \\false\\ otherwise.
   \\item \\karg{frame-found-p} -- If the frame is found then \\true,
                                   otherwise \\false.
   \\eitem
   If \\karg{error-p} is \\true\\ and the frame is not found, then a
   \\kcond{not-coercible-to-frame} error is signaled.

   It is an error to call \\kfn{coerce-to-frame} with \\karg{error-p} being
   \\true, and with a value of \\karg{thing} that does not uniquely identify
   a frame.  If this happens, a \\kcond{not-unique-error} error should be
   signaled.

   Note that in some KRS, \\false\\ may be a valid frame object.  No portable
   program may assume that a returned value of \\false\\ for the first
   (\\karg{frame}) returned value implies that \\karg{frame-found-p} is
   \\false."
  :compliance-classes :read
  :returned-values (frame frame-found-p)
  :manual-category :frame
  :monitor-body
  (record-reference thing nil t nil kb))

(defokbcop okbc:coerce-to-individual (thing &key (kb (current-kb)) (error-p t)
					    (kb-local-only-p nil))
  :returned-values (individual individual-found-p)
  :manual-category :individual
  :doc-string
  "Coerces \\karg{thing} to an individual.  This operation returns two values.
   \\bitem
   \\item \\karg{individual} -- If \\karg{thing} identifies an individual for
          \\karg{kb}, then this value is the individual so identified, or
          \\false otherwise.
   \\item \\karg{individual-found-p} -- If the individual is found then \\true,
                                   otherwise \\false.
   \\eitem
   If \\karg{error-p} is \\true and the individual is not found, then a
   \\kfn{individual-not-found} error is signaled.

   It is an error to call \\kfn{coerce-to-individual} with \\karg{error-p}
   being \\true, and with a value of \\karg{thing} that does not uniquely
   identify an individual.  If this happens, a \\kcond{not-unique-error} error
   should be signaled.

   Note that in most KRS, \\false\\ is a valid individual.  No portable
   program may assume that a returned value of \\false\\ for the first
   (\\karg{individual}) returned value implies that \\karg{individual-found-p}
   is \\false."
  :default-body
  (if (class-p-internal thing kb kb-local-only-p)
      (if error-p
	  (error 'individual-not-found
		 :missing-individual thing
		 :continuable t
		 :kb kb)
	  (values nil nil))
      (if (member :individual (get-behavior-values-internal :are-frames kb))
	  (multiple-value-bind (individual found-p)
	      (coerce-to-frame-internal thing kb nil kb-local-only-p)
	    (if found-p
		(values individual found-p)
		(if error-p
		    (error 'individual-not-found
			   :missing-individual thing
			   :continuable t
			   :kb kb)
		    (values nil nil))))
	  (values thing t)))
  :compliance-classes :read
  :monitor-body
  (record-reference thing nil t nil kb))


;==============================================================================

(defokbcop okbc:coerce-to-kb-value
    ((string-or-value :value) (target-context :value)
     &key (kb (current-kb)) (wildcards-allowed-p nil)
     (force-case-insensitive-p nil) (error-p t)
     (frame-action :error-if-not-unique) (kb-local-only-p nil))
  :returned-values (result-of-read success-p completions-alist)
  :manual-category :misc
  :doc-string
  "This operation is called by applications that receive input, often from a
   user in the form of typed input, or a value.  \\kfn{Coerce-to-kb-value}
   takes this input and delivers a value that is meaningful to the KRS.  This
   allows applications to interact with users and prompt for expressions
   containing frame references in a manner that will work predictably across
   implementation languages, and in networked implementations.
   \\kfn{Coerce-to-kb-value} implements OKBC's reading model just as
   \\kfn{value-as-string} implements OKBC's printing model.

   \\karg{string-or-value} may be one of the following.
   \\bitem
   \\item an arbitrary OKBC value entity -- If this is a list, then the
          coercion process applies recursively to the elements of the list.
          For example, if in the KB the symbol {\\tt fred} is coercible to the
          frame {\\tt \\#<frame FRED 763736>}, the value {\\tt (a fred 42)}
          would be coerced to the KB value
          {\\tt (a \\#<frame FRED 763736> 42)}.
   \\item a string -- This must be the printed representation of an OKBC entity,
          possibly containing wildcards.  For example, the string
          {\\tt \"(a fred 42)\"} would be coerced to the same KB value as in
          the example above.
   \\eitem

   Note that there is an asymmetry in the way that arguments are handled,
   in that a string as the value of \\karg{string-or-value} will \\em{always}
   be interpreted as a pattern from which to read a value, i.e. it will not
   be interpreted as an OKBC value entity.  This is useful in coercing strings
   into KB values.  However, this means that applications that use
   \\kfn{coerce-to-kb-value} as a way to read in values entered by the user
   must provide string quotes in order to get a string-valued result.  Thus,
   to get the string \"fred\" returned by \\kfn{coerce-to-kb-value} the
   value of the \\karg{string-or-value} argument would have to be
   \"\\\"fred\\\"\".  This problem arises if a user interface application
   is using a prompting model (such as the :string presentation type in CLIM)
   that elicits a string from the user, perhaps because it already knows that
   the value-type has to be a string.  If it does this, it will have to
   quote the string before it passes it to \\kfn{coerce-to-kb-value} or, of
   course, not pass it to \\kfn{coerce-to-kb-value} at all.

   Given a \\karg{string-or-value} and a \\karg{target-context}, returns three
   values.
  \\begin{enumerate}
  \\item \\karg{result-of-read} -- the result of reading from the string or
         value, interpreting objects in the \\karg{target-context} for the
         \\karg{kb}
  \\item \\karg{success-p} -- \\false\\ if an error occurred during the
         coercion, and \\true\\ otherwise
  \\item \\karg{completions-alist} -- an association list of possible
         completions
  \\end{enumerate}
  The first value returned (\\karg{result-of-read}) will be an entity such
  as a string, number, symbol, list (possibly containing other such values),
  or frame.

  \\karg{Target-context} is one of \\{{\\tt :frame}, {\\tt :class},
  {\\tt :slot}, {\\tt :individual}, {\\tt :facet}, {\\tt :value}\\} and
  identifies the way in which the value to be extracted from
  \\karg{string-or-value} is to be interpreted.
  \\bitem
  \\item {\\tt :frame} -- It is to be used as a \\karg{frame} argument to
  an OKBC operation.  It will be expected to resolve to a frame.
  \\item {\\tt :slot} -- It is to be used as a \\karg{slot} argument to
  an OKBC operation.  It will be expected to resolve to a slot name if slots
  are not represented as frames in \\karg{kb}, or to a slot frame if slots
  are represented as frames.
  \\item {\\tt :facet} -- It is to be used as a \\karg{facet} argument to
  an OKBC operation.  It will be expected to resolve to a facet name if facets
  are not represented as frames in \\karg{kb}, or to a facet frame if facets
  are represented as frames.
  \\item {\\tt :class} -- It is to be used as a \\karg{class} argument to
  an OKBC operation.  It will be expected to resolve to a class name if classes
  are not represented as frames in \\karg{kb}, or to a class frame if classes
  are represented as frames.
  \\item {\\tt :individual} -- It is to be used as an \\karg{individual}
  argument to an OKBC operation.  It will be expected to resolve to an
  individual, which may or may not be a frame.
  \\item {\\tt :value} -- it is to be used as a \\karg{value} argument to
  an OKBC operation, such as \\kfn{put-slot-value}.
  \\eitem
  The \\karg{frame-action} argument
  controls how the reading process interprets entities that can be interpreted
  as frames.  The \\karg{result-of-read} value is \\false\\ if an
  error occurs.  The third value returned (\\karg{completions-alist}) is
  \\false\\ if an error occurs, or otherwise is an association list of
  the form
  \\begin{verbatim}
  ((<<string1>> <<substring1>> <<frame1>> <<frame2>>... <<frameN>>)
   (<<string2>> ....) ...)
  \\end{verbatim}
  where {\\tt <<stringX>>} are strings found in \\karg{string-or-value}
  that match the frames {\\tt<<frame1>> ... <<frameN>>}
  (possibly by using any specified wildcards), and \\verb|<<substringX>>|
  are the corresponding
  longest matching initial substrings for each {\\tt<<stringX>>} (see the
  specification of \\kfn{get-frames-matching}).
  \\bitem
  \\item \\karg{Wildcards-allowed-p}
    --- has the same meaning as in \\kfn{get-frames-matching}.  Wildcards are
        interpreted piecewise for the components extracted from
        \\karg{string-or-value}.  Thus, {\\tt \"(fr* j*)\"} and
        {\\tt (\"fr*\" \"j*\")} both denote a list
        expression with two wildcarded components, and would match
        \\verb|(fred joe)|.
  \\item \\karg{Force-Case-Insensitive-P}
    --- when \\true\\ causes frame identification comparison to be
        case-insensitive, irrespective of the preferred case sensitivity of the
        \\karg{KB} itself.
  \\item \\karg{Error-p}
    --- when \\true\\ will signal a \\kcond{kb-value-read-error} error if a
        problem arises during the reading process, for example, due to
        mismatched parentheses.
  \\item\\karg{Frame-action}
    --- is a keyword from the following list:
        \\bitem
        \\item {\\tt :error-if-not-unique}
          --- If any substring is found that matches more than one frame then
            signal a \\kcond{not-unique-error} error.
        \\item {\\tt :do-not-coerce-to-frames}
          --- Substrings of \\karg{string-or-value} (if a string), or strings
              and symbols in \\karg{string-or-value} (if a nonstring) that
              match frames are not converted into frames, but may be mapped
              into strings or symbols.
        \\item {\\tt :must-name-frames}
          --- Any symbol or string value must be coercible to a frame.  If it
              is not, a \\kcond{not-coercible-to-frame} error is signaled.
        \\item {\\tt :options-if-not-unique}
          --- For each ambiguous frame reference in \\karg{string-or-value},
              give the possible matches in an entry in the
              \\karg{completions-alist} returned value.
        \\eitem
  \\eitem
  For example, if in a KB there are frames called {\\tt \"FRED\"},
  {\\tt \"FREDDY\"}, and {\\tt \"FRESH\"} and the call
  \\begin{verbatim}
  (coerce-to-kb-value \"fr*\" :frame-action :options-if-not-unique)
  \\end{verbatim}
  is made, the values returned would be
  \\begin{enumerate}
  \\item \\false  --- The coercion could not complete because of
  the ambiguity.
  \\item \\true --- The operation completed without error.
  \\item {\\tt ((\"FR*\" \"FRE\" FRED FREDDY FRESH))} --- Only one ambiguous
         reference was found, and for that the longest matching substring for
         the pattern {\\tt \"FR*\"} is {\\tt \"FRE\"}, and the matching frames
         are \\{FRED, FREDDY, FRESH\\}.
  \\end{enumerate}
  See also \\kfn{get-frames-matching}, which is called to identify frames."
  :default-body
  (default-coerce-to-kb-value
      string-or-value target-context kb wildcards-allowed-p
      force-case-insensitive-p error-p frame-action
      kb-local-only-p))

(defun whitespacep (x)
  #+Lucid (lucid::whitespacep x)
  #+MCL (ccl::whitespacep x)
  #+Allegro (excl::whitespace-char-p x)
  #+Harlequin-Common-Lisp (lispworks:whitespace-char-p x)
  #-(or Lucid MCL Allegro Harlequin-Common-Lisp) (error "Not yet implemented"))

(defun default-coerce-to-kb-value
    (string-or-value target-context kb wildcards-allowed-p
		     force-case-insensitive-p error-p frame-action
		     kb-local-only-p)
  (multiple-value-bind (form read-error-p)
      (if (stringp string-or-value)
          (handler-case
           (implement-with-kb-io-syntax-internal
	    #'(lambda ()
		(multiple-value-bind (sexpr end-index)
		  (safely-read-from-string string-or-value)
		  (when (loop for i from end-index
			      below (length string-or-value)
			      for char = (char string-or-value i)
			      thereis (not (whitespacep char)))
		    (error 'kb-value-read-error
			   :read-string string-or-value :kb kb
			   :continuable t
			   :error-message
			   (format nil "Junk found at end of string-or-value ~
                                  argument.  Value ~S was successfully read, ~
                                  but there was extra stuff: ~S left over.  ~
                                  The string should contain only one value."
			     sexpr (subseq string-or-value end-index))))
		  (values sexpr)))
	    kb :file kb-local-only-p)
	   (kb-value-read-error (condition) (error condition))
	   (error (condition)
		  (declare (ignore condition))
		  (values nil t)))
	  (values string-or-value nil))
    (continuable-assert
     (member target-context '(:frame :slot :facet :value :class :individual))
     () "Target-context must be one of {:frame :slot :facet :value :class ~
         :individual}")
    (cond (read-error-p
	   (if error-p
	       (error 'kb-value-read-error :read-string string-or-value :kb kb
		      :continuable t)
	       (values nil nil nil)))
	  ((and (not (atom form))
		(member target-context '(:frame :slot :class :facet)))
	   (error 'kb-value-read-error :read-string string-or-value :kb kb
		  :continuable t
		  :error-message
		  (format nil "Compound value ~S found for string-or-value ~
                                  argument, but this is not acceptable for ~
                                  :target-context = ~S"
			  string-or-value target-context)))
	  (t (flet ((doit ()
		      (ecase frame-action
			(:do-not-coerce-to-frames (values form t nil))
			((:error-if-not-unique
			  :must-name-frames
			  :options-if-not-unique)
			 (let ((*alist* nil))
			   (declare (special *alist*))
			   (multiple-value-bind (interned error-found-p)
			       (if error-p
				   (intern-frames-in form frame-action kb
						     wildcards-allowed-p
						     force-case-insensitive-p
						     kb-local-only-p
						     target-context)
				   (ignore-errors
				    (values (intern-frames-in
					     form frame-action kb
					     wildcards-allowed-p
					     force-case-insensitive-p
					     kb-local-only-p
					     target-context))))
			     (if error-found-p
				 (values nil nil nil)
				 (if *alist*
				     (values nil t *alist*)
				     (values interned t nil)))))))))
	       (if (and (not (stringp string-or-value))
			(eq frame-action :error-if-not-unique))
		   (case target-context
		     (:frame (coerce-to-frame-internal
			      form kb error-p kb-local-only-p))
		     (:slot  (coerce-to-slot-internal
			      form kb error-p kb-local-only-p))
		     (:facet (coerce-to-facet-internal
			      form kb error-p kb-local-only-p))
		     (:class (coerce-to-class-internal
			      form kb error-p kb-local-only-p))
		     (:individual (coerce-to-individual-internal
				   form kb error-p kb-local-only-p))
		     (otherwise (doit)))
		   (doit)))))))

#-MCL
(defun readtable-dispatch-tables (rt)
  ;; A list of th form ((#\# . <<table>>))
  #+TI (sys:dispatch-tables rt)
  #+Lucid (system:structure-ref rt 2 (type-of rt))
  #+EXCL (excl::readtable-dispatch-tables rt)
  #+Harlequin-Common-Lisp (system::readtable-dispatch-tables rt)
  #-(or Lucid EXCL TI Harlequin-Common-Lisp)
  (unimplemented "readtable-character-macro-table"))

(defun ok-utils:dispatch-macro-character-p
    (char &optional (readtable *readtable*)
	  #-MCL
	  (dispatch-tables
	   (readtable-dispatch-tables readtable)))
  "Is true if <code>char</code> is a dispatch macro character in
   <code>readtable</code>.  This is used by <code>read-safely-from-string</code>
   to make sure that we don't do anything like #."
  #-MCL
  (rest (assoc (the character char) (the cons dispatch-tables) :test #'char=))
  #+MCL
  (= 9 (aref (ccl::%svref readtable 1) (char-code char))))

(defvar *standard-cl-readtable*
  (locally #+Lucid (declare (special lucid::*standard-readtable*))
	   #+Lucid lucid::*standard-readtable*
	   #-Lucid *readtable*))

(defun innocuous-macro-reference-p (macro-char next-char)
  (let ((macro-table (dispatch-macro-character-p macro-char))
	(cl-table (dispatch-macro-character-p
		   #\# *standard-cl-readtable*)))
    (let ((function (aref macro-table (char-code next-char)))
	  (ichars '(#\( #\' #\* #\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9 #\=
		    #\\ #\| #\+ #\- #\A #\a #\C #\c #\B #\b #\O #\o #\R #\r
		    #\S #\s #\X #\x)))
      (loop for ichar in ichars
	    thereis (eq function (aref cl-table (char-code ichar)))))))

(defun safely-read-from-string
    (string &optional (eof-error-p t) (eof-value nil) &key (start 0) end)
  "Just like <code>read-from-string</code>, only it will not allow the reading
   to proceed if any potentially dangerous reader macro references are found
   in the <code>string</code>.  For example, <code>#.</code> macro references
   will signal an error, since they may be an attempt by a client to execute
   arbitrary Lisp code on the server."
  (loop for index from start below (or end (length string))
	for char = (aref string index)
	do (continuable-assert
	    (or (not (dispatch-macro-character-p char))
		(and (< index (- (or end (length string)) 2))
		     (innocuous-macro-reference-p
		      char (aref string (+ index 1)))))
	    syntax-error :erring-input string
	    :error-message
	    (format nil 
		    "Reader macro character ~S found in input.  ~
                     These are disallowed for security reasons."
		    char)))
  (read-from-string string eof-error-p eof-value
		    :start start :end end))

(defun add-to-*alist* (form substring matches)
  (declare (special *alist*))
  (push (cons form (cons substring matches)) *alist*))

(defun intern-frames-in
    (form frame-action kb wildcards-allowed-p force-case-insensitive-p
	  kb-local-only-p target-context)
  (declare (special *alist*))
  (typecase form
    (cons (cons (intern-frames-in (first form) frame-action kb
				  wildcards-allowed-p force-case-insensitive-p
				  kb-local-only-p target-context)
		(intern-frames-in (rest  form) frame-action kb
				  wildcards-allowed-p force-case-insensitive-p
				  kb-local-only-p target-context)))
    (null nil)
    ((or string symbol)
     (ecase frame-action
       (:must-name-frames
	(multiple-value-bind (matches substring)
	    (get-frames-matching-internal
	     form kb wildcards-allowed-p
	     (if (member target-context '(:value :frame)) :all target-context)
	     force-case-insensitive-p kb-local-only-p)
	  (declare (ignore substring))
	  (case (length matches)
	    (0 (error 'not-coercible-to-frame :frame form :kb kb
		      :continuable t))
	    (1 (first matches))
	    (otherwise (error 'not-unique-error
			      :pattern (string form)
			      :matches matches
			      :context target-context
			      :continuable t
			      :kb kb)))))
       ((:error-if-not-unique :options-if-not-unique)
	(let ((entry (assoc form *alist* :test #'equal)))
	  (cond ((variable? form) form)
		(entry (first entry))
		(t (multiple-value-bind (matches substring)
		     (get-frames-matching-internal
		      form kb wildcards-allowed-p
		      (if (member target-context '(:value :frame))
			  :all
			  target-context)
		      force-case-insensitive-p kb-local-only-p)
		     (case (length matches)
		       (0 form)
		       (1 (first matches))
		       (otherwise
			(when (eq :error-if-not-unique frame-action)
			  (error 'not-unique-error
				 :pattern (string form)
				 :matches matches
				 :context target-context
				 :continuable t
				 :kb kb))
			(add-to-*alist* form substring matches)
			nil)))))))))
    (otherwise form)))

;==============================================================================

(defokbcop okbc:coerce-to-slot (thing &key (kb (current-kb)) (error-p t)
				      (kb-local-only-p nil))
  :returned-values (slot slot-found-p)
  :manual-category :slot
  :doc-string
  "Coerces \\karg{thing} to a slot.  This operation returns two values.
   \\bitem
   \\item \\karg{slot} -- If \\karg{thing} identifies a slot for \\karg{kb},
                           then this value is the slot so identified, or
                           \\false otherwise.
   \\item \\karg{slot-found-p} -- If the slot is found then \\true,
                                   otherwise \\false.
   \\eitem
   If \\karg{error-p} is \\true and the slot is not found, then a
   \\kcond{slot-not-found} error is signaled.

   It is an error to call \\kfn{coerce-to-slot} with \\karg{error-p} being
   \\true, and with a value of \\karg{thing} that does not uniquely identify
   a slot.  If this happens, a \\kcond{not-unique-error} error should be
   signaled.

   Note that in some KRS, \\false\\ may be a valid slot.  No portable
   program may assume that a returned value of \\false\\ for the first
   (\\karg{slot}) returned value implies that \\karg{slot-found-p} is \\false."
  :default-body
  (if (member :slot (get-behavior-values-internal :are-frames kb))
      (multiple-value-bind (slot found-p)
	  (coerce-to-frame-internal thing kb nil kb-local-only-p)
	(if (and found-p (slot-p-internal slot kb kb-local-only-p))
	    (values slot found-p)
	    (if error-p
		(error 'slot-not-found
		       :frame nil
		       :slot thing
		       :slot-type nil
		       :continuable t
		       :kb kb)
		(values nil nil))))
      (if (slot-p-internal thing kb kb-local-only-p)
	  (values thing t)
	  (if error-p
	      (error 'slot-not-found
		     :frame nil
		     :slot thing
		     :slot-type nil
		     :continuable t
		     :kb kb)
	      (values nil nil))))
  :compliance-classes :read
  :monitor-body
  (record-reference thing nil t nil kb))

(defokbcop okbc:coercible-to-frame-p (thing &key (kb (current-kb))
					    (kb-local-only-p nil))
  :returned-values boolean
  :manual-category :frame
  :doc-string
  "Returns \\true\\ when \\karg{thing} can be coerced to a frame
   by using \\kfn{coerce-to-frame}, and otherwise returns \\false."
  :default-body
  (multiple-value-bind (a b)
		       (coerce-to-frame-internal thing kb nil kb-local-only-p)
		       (declare (ignore a))
    b)
  :monitor-body
  (record-reference thing nil t nil kb) )

;------------------------------------------------------------------------------

(defokbcop okbc:copy-frame (frame new-name &key (kb (current-kb))
				  (to-kb (current-kb)) (error-p t)
				  (missing-frame-action :stop)
				  (frame-handle-mapping-table nil)
				  (kb-local-only-p nil))
  :doc-string
  "Copies \\karg{frame} from \\karg{kb} to \\karg{to-kb}.  The name of the new
   frame in \\karg{to-kb} will be \\karg{new-name}.  \\karg{Kb} and
   \\karg{to-kb} may be the same KB.  If the {\\tt :frame-names-required}
   behavior has the value \\false\\ for \\karg{kb}, \\karg{new-name} may be
   \\false.
 
   If \\karg{error-p} is \\false, catches errors that occur, and 
   continues copying to the extent possible.

   The \\karg{frame} may contain references to other frames that do not
   reside in \\karg{to-kb} -- for example,
   its types, superclasses, or slot values.
   \\karg{Missing-frame-action} controls the behavior of \\kfn{copy-frame} 
   in this case.  It can take one of the following values:

   {\\tt :stop} -- Stop copying and signal a \\kfn{frames-missing} error,
                   depending on the value of \\karg{error-p}.

   {\\tt :abort} -- Abort copying \\karg{frame}, leaving the state of
                    \\karg{to-kb} unchanged.  Any side effects of
                    \\kfn{copy-frame} that have already been performed will
                    be undone.  Signals a \\kfn{frames-missing} error,
                    depending on the value of \\karg{error-p}.

   {\\tt :allocate} -- Allocate frame handles for any frame references that 
                       do not yet exist in \\karg{to-kb}.

   {\\tt :ignore} - Continue with the copying of the current frame, but
                    ignore and remove any references to missing frames.

   \\karg{Frame-handle-mapping-table}, if supplied, is a hash table that maps
   the frame handles in the \\karg{kb} to frame handles in \\karg{to-kb}, and
   is used during compound copy operations, such as \\kfn{copy-kb}.  If
   copy-frame fails to find a referenced frame in \\karg{to-kb}, it looks up
   the reference in the \\karg{Frame-handle-mapping-table} before allocating 
   a new frame handle.

   It returns two values.
   \\begin{enumerate}
   \\item \\karg{Copy-of-frame} -- Identifies the newly created frame in
      \\karg{to-kb}.  If \\karg{copy-frame} terminates because some frames were
      missing, and \\karg{missing-frame-action} was {\\tt :abort},
      \\false\\ is returned as a value of \\karg{copy-of-frame}.
   \\item \\karg{Allocated-frame-handle-alist} -- a list of 2-tuples\\\\ {\\tt
      (frame-handle-in-kb frame-handle-in-to-kb)} that maps frame handles in
      \\karg{kb} to frame handles in \\karg{to-kb} that were allocated during
      the copying process.  These mappings will also have been entered in
      \\karg{frame-handle-mapping-table} if it was supplied.
   \\end{enumerate} "
  :returned-values (copy-of-frame allocated-frame-handle-alist)
  :manual-category :frame
  :causes-side-effects-p to-kb
  :arguments-to-kb-specialize (kb to-kb)
  :monitor-body (progn
		  (record-reference frame nil t nil kb)
		  (record-reference new-name nil t nil kb))
  :modification-body
  (progn (when (coercible-to-frame-p-internal new-name to-kb kb-local-only-p)
	   (setq new-name (get-frame-name-internal new-name to-kb
						   kb-local-only-p)))
	 (record-modification new-name to-kb :create))
  :default-body
  (default-copy-frame frame new-name kb to-kb error-p missing-frame-action
    frame-handle-mapping-table kb-local-only-p))


;; Creates a list of slot specifications for Slots in Frame.
;; A slot spec is of the form:
;;    ((slot value*)*)

(defun get-slot-specification (frame slots slot-type kb inference-level
				     number-of-values kb-local-only-p)
  (let ((inexact-p nil))
    (values
     (loop with exact-p = nil
	   with vals = nil
	   with dvals = nil
	   for slot in slots
	   do (multiple-value-setq (vals exact-p)
		(get-slot-values-internal frame slot kb inference-level
					  slot-type number-of-values
					  :known-true kb-local-only-p))
	   when (not exact-p) do (setq inexact-p t)
	   do (multiple-value-setq (dvals exact-p)
		(get-slot-values-internal frame slot kb inference-level
					  slot-type number-of-values
					  :default-only kb-local-only-p))
	   when (not exact-p) do (setq inexact-p t)
	   collect
	   (multiple-value-bind (slot-frame found-p)
	     (coerce-to-slot-internal slot kb nil kb-local-only-p)
	     (cons (if found-p slot-frame slot)
		   (append (loop for d in dvals
				 collect (list :default (copy-tree d)))
			   (copy-tree vals)))))
     (not inexact-p))))

;; A facet-spec is of the form:
;;    ((slot (facet-name value*)*)*)

;; what happens when facet value is a frame?  don't 
;; we need to take get-frame-name of that?

(defun get-facet-specification (frame slots slot-type kb inference-level
				      number-of-values kb-local-only-p)
  (let ((inexact-p nil))
    (values
     (loop for slot in slots
	   for facet-spec =
	   (multiple-value-bind (facets exact-p)
	     (get-slot-facets-internal
	      frame slot kb inference-level slot-type kb-local-only-p)
	     (when (not exact-p) (setq inexact-p t))
	     (loop with exact-p = nil
		   with vals = nil
		   with dvals = nil
		   for facet in facets
		   do (multiple-value-setq (vals exact-p)
			(get-facet-values-internal
			 frame slot facet kb inference-level slot-type
			 number-of-values :known-true kb-local-only-p))
		   when (not exact-p) do (setq inexact-p t)
		   do (multiple-value-setq (dvals exact-p)
			(get-facet-values-internal
			 frame slot facet kb inference-level slot-type
			 number-of-values :default-only kb-local-only-p))
		   when (not exact-p) do (setq inexact-p t)
		   collect
		   (multiple-value-bind (facet-frame found-p)
		     (coerce-to-facet-internal facet kb nil kb-local-only-p)
		     (cons (if found-p facet-frame facet)
			   (append (loop for d in dvals
					 collect (list :default
						       (copy-tree d)))
				   (copy-tree vals))))))
	   when facet-spec
	   collect
	   (multiple-value-bind (slot-frame found-p)
	     (coerce-to-slot-internal slot kb nil kb-local-only-p)
	     (cons (if found-p slot-frame slot) facet-spec)))
     (not inexact-p))))


(defvar **missing-frame-tag** (make-symbol "**missing-frame-tag**"))
(defvar *untranslated-facet-frames*)

(defmethod allocate-any-necessary-frame-handles 
    (tree kb frame-handle-mapping-table kb-local-only-p to-kb
	  missing-frame-action error-p for-frame)
  (declare (special *allocated-frame-handle-alist*))
  (typecase tree
    (cons
     (let ((res nil)
	   (tail nil))
       (loop for car = (pop tree)
	     for car-result =
	     (allocate-any-necessary-frame-handles 
	      car kb frame-handle-mapping-table kb-local-only-p
	      to-kb missing-frame-action error-p for-frame)
	     when (not (eq car-result **missing-frame-tag**))
	     do (let ((new (list car-result)))
		  (if res
		      (progn (setf (rest tail) new)
			     (setq tail new))
		      (progn (setq res new)
			     (setq tail new))))
	     when (not tree) return nil
	     when (not (consp tree))
	     do (return (setf (rest tail)
			      (allocate-any-necessary-frame-handles 
			       tree kb frame-handle-mapping-table
			       kb-local-only-p to-kb missing-frame-action
			       error-p for-frame))))
       res)
     ;; The old way to do it was more recursive.
     #+ignore 
     (let ((car-result
	    (allocate-any-necessary-frame-handles 
	     (first tree) kb frame-handle-mapping-table kb-local-only-p
	     to-kb missing-frame-action error-p for-frame)))
       (if (eq car-result **missing-frame-tag**)
	   (allocate-any-necessary-frame-handles 
	    (rest tree) kb frame-handle-mapping-table kb-local-only-p
	    to-kb missing-frame-action error-p for-frame)
	   (cons car-result
		 (allocate-any-necessary-frame-handles 
		  (rest tree) kb frame-handle-mapping-table
		  kb-local-only-p to-kb missing-frame-action error-p
		  for-frame)))))
    ;; Symbolic frame references will name themselves
    ((or kb structure-kb symbol string number) tree)
    (otherwise 
     ;; The thing is a legal and allocated frame handle in the
     ;; target kb already.
     (cond ((gethash tree frame-handle-mapping-table)
	    (values tree :in-mapping-table))
	   ;; No need to look at the frame-handle table when we are in the
	   ;; same kb JFT 0698
	   ((eq kb to-kb) (values tree :copy-to-same-kb))
	   (t (let ((frame (if (typep tree 'ok-back:frame-handle)
			       tree
			       (multiple-value-bind (f found-p)
				 (coerce-to-frame-internal tree kb nil
							   kb-local-only-p)
				 (and found-p
				      (get-frame-handle-internal 
				       f kb kb-local-only-p))))))
		(cond
		  ((and frame (coercible-to-frame-p-internal
			       frame kb kb-local-only-p))
		   (let ((name (get-frame-name-internal
				frame kb kb-local-only-p))
			 (type (get-frame-type-internal
				frame kb kb-local-only-p)))
		     (ecase missing-frame-action
		       (:allocate
			(actually-allocate-if-necessary
			 name frame type to-kb frame-handle-mapping-table))
		       ((:stop :abort)
			(if error-p
			    (error 'missing-frames
				   :missing-frames (list frame) :kb kb
				   :frame for-frame)
			    (throw :stop
			      (values nil *allocated-frame-handle-alist*
				      missing-frame-action (list frame)))))
		       ((:continue :ignore) **missing-frame-tag**))))
		  (t (values tree :not-a-frame)))))))))

(defmethod default-allocate-name-in-new-kb (name (kb t))
 name)

(defvar *allocate-name-in-new-kb-hook* 'default-allocate-name-in-new-kb)

(defun actually-allocate-if-necessary
    (name frame type to-kb frame-handle-mapping-table
	  &optional (outside-handle nil supplied-p))
  (declare (special *allocated-frame-handle-alist*))
  (let ((key (list name frame type)))
    (or (gethash key frame-handle-mapping-table)
	(and (or (not supplied-p)
		 (not (symbolp outside-handle)))
	     (let ((name-in-new-kb (funcall *allocate-name-in-new-kb-hook*
					    name to-kb)))
	       (let ((new (allocate-frame-handle-internal
			   name-in-new-kb type to-kb frame)))
		 ;; store it both ways.
		 (setf (gethash key frame-handle-mapping-table) new)
		 (setf (gethash new frame-handle-mapping-table) key)
		 (when (not (equal name-in-new-kb name))
		   (let ((key (list name-in-new-kb frame type)))
		     (setf (gethash key frame-handle-mapping-table) new)
		     (setf (gethash new frame-handle-mapping-table) key)))
		 (push (list frame new) *allocated-frame-handle-alist*)
		 new))))))

(defun behavior-is-enabled-p (behavior kb)
  (let ((values (get-behavior-values-internal behavior kb)))
    (remove nil values)))

(defun slots-are-reified-p (kb)
  (member :slot (get-behavior-values-internal :are-frames kb)))

(defun facets-are-reified-p (kb)
  (member :facet (get-behavior-values-internal :are-frames kb)))

(defpackage gensym-slot-and-facets (:use))

(defun find-or-create-frame-handle-for-symbol
    (symbol frame-type frame-handle-mapping-table to-kb)
  (declare (special *allocated-frame-handle-alist*))
  (let ((key (list symbol nil frame-type)))
    (or (gethash key frame-handle-mapping-table)
	(and (let ((new (allocate-frame-handle-internal
			 symbol frame-type to-kb nil)))
	       (setf (gethash key frame-handle-mapping-table) new)
	       (setf (gethash new frame-handle-mapping-table) key)
	       (push (list symbol new) *allocated-frame-handle-alist*)
	       new)))))

(defun fix-up-internal
    (slot-specs from-kb to-kb frame-handle-mapping-table kb-local-only-p
		was-reified-p will-be-reified-p missing-frame-action error-p
		for-frame missing-name)
  (cond ((or (and was-reified-p will-be-reified-p)
	     (and (not was-reified-p) (not will-be-reified-p)))
	 ;; The same reification applies, but we still have to do the
	 ;; frame handle allocation.
	 (allocate-any-necessary-frame-handles
	  slot-specs from-kb frame-handle-mapping-table
	  kb-local-only-p to-kb
	  missing-frame-action error-p for-frame))
	((and was-reified-p (not will-be-reified-p))
	   ;;; then we need to dereify the slots.
	 (loop for (slot . spec) in slot-specs
	       for allocated-spec = (allocate-any-necessary-frame-handles
				     spec from-kb frame-handle-mapping-table
				     kb-local-only-p to-kb
				     missing-frame-action error-p for-frame)
	       for frame = (coerce-to-frame-internal slot from-kb nil
						     kb-local-only-p)
	       for allocated-frame
	       = (and frame (allocate-any-necessary-frame-handles
			     frame from-kb frame-handle-mapping-table
			     kb-local-only-p to-kb
			     missing-frame-action error-p for-frame))
	       for frame-to-use = (if (eq allocated-frame
					  **missing-frame-tag**)
				      missing-name
				      allocated-frame)
	       collect (cond (frame-to-use
			      (cons (get-frame-name-internal slot from-kb
							     kb-local-only-p)
				    allocated-spec))
			     ((symbolp slot)
			      (cons (get-frame-name-internal slot from-kb
							     kb-local-only-p)
				    allocated-spec))
			     (t (cons (intern (prin1-to-string slot)
					      :gensym-slot-and-facets)
				      allocated-spec)))))
	(t
	   ;;; then we need to reify the slots.
	 (loop for (slot . spec) in slot-specs
	       for frame = (coerce-to-frame-internal slot from-kb nil
						     kb-local-only-p)
	       for allocated-spec = (allocate-any-necessary-frame-handles
				     spec from-kb frame-handle-mapping-table
				     kb-local-only-p to-kb
				     missing-frame-action error-p for-frame)
	       for allocated-frame
	       = (and frame (allocate-any-necessary-frame-handles
			     frame from-kb frame-handle-mapping-table
			     kb-local-only-p to-kb
			     missing-frame-action error-p for-frame))
	       for frame-to-use = (if (eq allocated-frame
					  **missing-frame-tag**)
				      missing-name
				      allocated-frame)
	       collect
	       (cond (frame-to-use
		      (cons (if (not (eq frame-to-use missing-name))
				(get-frame-handle-internal
				 frame-to-use from-kb kb-local-only-p)
				frame-to-use)
			    allocated-spec))
		     ((symbolp slot)
		      (let ((handle
			     (find-or-create-frame-handle-for-symbol
			      slot :individual
			      frame-handle-mapping-table to-kb)))
			(cons handle allocated-spec)))
		     (t (let ((symbol (intern
				       (prin1-to-string slot)
				       :gensym-slot-and-facets)))
			  (let ((handle
				 (find-or-create-frame-handle-for-symbol
				  symbol :individual
				  frame-handle-mapping-table to-kb)))
			    (cons handle allocated-spec)))))))))

(defun fix-up-slot-specs
    (slot-specs from-kb to-kb frame-handle-mapping-table kb-local-only-p
		missing-frame-action error-p for-frame)
  (let ((was-reified-p (slots-are-reified-p from-kb))
	(will-be-reified-p (slots-are-reified-p to-kb)))
    (fix-up-internal
     slot-specs from-kb to-kb frame-handle-mapping-table kb-local-only-p
     was-reified-p will-be-reified-p missing-frame-action error-p
     for-frame :missing-slot)))

(defun fix-up-facet-specs
    (facet-specs from-kb to-kb frame-handle-mapping-table kb-local-only-p
		 missing-frame-action error-p for-frame)
  (let ((was-reified-p (facets-are-reified-p from-kb))
	(will-be-reified-p (facets-are-reified-p to-kb)))
    (fix-up-slot-specs
     (loop for (slot . specs) in facet-specs
	   collect (cons slot
			 (fix-up-internal
			  specs from-kb to-kb frame-handle-mapping-table
			  kb-local-only-p was-reified-p will-be-reified-p
			  missing-frame-action error-p for-frame
			  :missing-facet)))
      from-kb to-kb frame-handle-mapping-table kb-local-only-p
      missing-frame-action error-p for-frame)))

(defun default-copy-frame (frame new-name kb to-kb error-p
				 missing-frame-action
				 frame-handle-mapping-table kb-local-only-p)
  (let ((details (get-frame-details-internal frame kb :direct
					     :all kb-local-only-p))
	(frame-handle-mapping-table (or frame-handle-mapping-table
					(make-hash-table :test #'equal)))
	(just-copy-frame-p (not (boundp '*untranslated-facet-frames*))))
    (if details
	(let ((*untranslated-facet-frames*
	       (if just-copy-frame-p
		   (make-hash-table :test #'equal)
		   *untranslated-facet-frames*))
	      (*allocated-frame-handle-alist* nil))
	  (declare (special *allocated-frame-handle-alist*))
	  (multiple-value-bind (new-frame alist status)
	    (if error-p
		(default-copy-frame-inside-error-handler
		    frame new-name kb to-kb error-p missing-frame-action
		    frame-handle-mapping-table kb-local-only-p details)
		(handler-case
		 (default-copy-frame-inside-error-handler
		     frame new-name kb to-kb error-p missing-frame-action
		     frame-handle-mapping-table kb-local-only-p details)
		 (error (condition)
			(declare (ignore condition))
			(values nil *allocated-frame-handle-alist*
				:error-found))))
	    (when just-copy-frame-p
	      (warn-about-untranslated-facets to-kb))
	    (values new-frame alist status)))
	(if error-p
	    (error 'not-coercible-to-frame :frame frame :kb kb
		   :continuable t)
	    (values nil nil :no-details)))))


(defmethod default-compute-pretty-name-for-copy-frame
    (old-name new-name pretty-name handle kb)
 (declare (ignore old-name new-name handle kb))
 pretty-name)

(defvar *compute-pretty-name-for-copy-frame-hook*
  'default-compute-pretty-name-for-copy-frame)

(defun default-copy-frame-inside-error-handler
    (frame new-name kb to-kb error-p missing-frame-action
	   frame-handle-mapping-table kb-local-only-p details)
  (declare (special *allocated-frame-handle-alist*))
  (catch :stop
    (destructuring-bind (&key name pretty-name primitive-p frame-type types
			      superclasses handle own-slots own-facets
			      template-slots template-facets &allow-other-keys)
	details
      (if new-name
	  (format t "~%Copying ~A ~S [~A]"
	    (ecase frame-type
	      (:class "class")
	      (:facet "facet")
	      (:slot "slot")
	      (:individual "individual"))
	    new-name pretty-name)
	  (format t "~%Copying ~A [~A]"
	    (ecase frame-type
	      (:class "class")
	      (:facet "facet")
	      (:slot "slot")
	      (:individual "individual"))
	    pretty-name))
      (when (coercible-to-frame-p-internal new-name to-kb kb-local-only-p)
	(setq new-name (get-frame-name-internal new-name to-kb
						kb-local-only-p)))
      ;; If to-kb differs from kb, check that all parents of Frame
      ;; are also defined in to-kb.
      (let ((missing
	     (if (eq kb to-kb)
		 nil
		 (loop with all = (if (eq frame-type :class)
				      (append types superclasses)
				      types)
		       with converted =
		       (allocate-any-necessary-frame-handles 
			all kb frame-handle-mapping-table
			kb-local-only-p to-kb :allocate error-p frame)
		       for class in converted
		       ;; class is now a handle as specified in the
		       ;; to-kb
		       when (not (frame-in-kb-p-internal
				  class to-kb kb-local-only-p))
		       collect class))))
	(when missing
	  (ecase missing-frame-action
	    (:allocate
	     (if (member frame-type '(:individual :slot :facet))
		 (setq types (allocate-any-necessary-frame-handles 
			      types kb frame-handle-mapping-table
			      kb-local-only-p to-kb :allocate error-p frame))
		 (setq superclasses (allocate-any-necessary-frame-handles 
				     superclasses kb frame-handle-mapping-table
				     kb-local-only-p to-kb :allocate error-p
				     frame))))
	    (:stop
	     (if error-p
		 (error 'missing-frames
			:error-message
			(format nil
				"Not all parent frames of ~A in KB ~A exist ~
                                 in KB ~A.~%  Missing: ~{~S~^, ~}"
				handle (name kb) (name to-kb) missing)
			:missing-frames missing :kb kb :frame frame)
		 (return-from default-copy-frame-inside-error-handler
		   (values nil *allocated-frame-handle-alist* :stop
			   missing))))
	    (:abort
	     (format t "~%;;; Not all parent frames of ~A ~%~
                                ;;; in KB ~A exist in KB ~A - skipping copy."
		     handle (name kb) (name to-kb))
	     (if error-p
		 (error 'missing-frames
			:error-message
			(format nil
				"Not all parent frames of ~A in KB ~A exist ~
                                 in KB ~A.~%  Missing: ~{~S~^, ~}"
				handle (name kb) (name to-kb) missing)
			:missing-frames missing :kb kb :frame frame)
		 (return-from default-copy-frame-inside-error-handler
		   (values nil *allocated-frame-handle-alist*
			   :abort missing))))
	    ((:continue :ignore)
	     (format t "~%;;; Not all parent frames of ~A ~%~
                                ;;; in KB ~A exist in KB ~A.~%~
                                ;;; Missing frame~P to be ignored: ~
                            ~{~%;;;    ~S~^, ~}"
		     handle (name kb) (name to-kb)
		     (length missing) missing)
	     (if (member frame-type '(:individual :slot :facet))
		 (setq types  (set-difference types missing))
		 (progn (setq types (set-difference types missing))
			(setq superclasses
			      (set-difference superclasses missing)))))))
	(setq types (allocate-any-necessary-frame-handles 
		     types kb frame-handle-mapping-table
		     kb-local-only-p to-kb :allocate error-p frame))
	(setq superclasses (allocate-any-necessary-frame-handles 
			    superclasses kb frame-handle-mapping-table
			    kb-local-only-p to-kb :allocate error-p
			    frame))
	(let ((get-facets-p
	       (member :user-defined-facets
		       (get-behavior-values-internal :compliance to-kb))))
	  (when (and (not get-facets-p)
		     (not (gethash frame *untranslated-facet-frames*))) 
	    (setf (gethash frame *untranslated-facet-frames*) pretty-name)))
	(let ((new-handle
	       (actually-allocate-if-necessary
		new-name frame frame-type to-kb frame-handle-mapping-table
		handle)
		#+ignore ;; the old way
		(let ((key (list new-name handle frame-type)))
		 (or (gethash key frame-handle-mapping-table)
		     (and (not (symbolp handle))
			  (let ((new (allocate-frame-handle-internal
				      new-name frame-type to-kb handle)))
			    (setf (gethash key frame-handle-mapping-table) new)
			    (setf (gethash new frame-handle-mapping-table) key)
			    (push (list handle new)
				  *allocated-frame-handle-alist*)
			    new))))))
	  (let ((args (list new-name frame-type to-kb
			    types
			    (if (class-p-internal frame kb kb-local-only-p)
				superclasses
				nil)
			    nil;; documentation
			    (fix-up-slot-specs template-slots kb to-kb
					       frame-handle-mapping-table
					       kb-local-only-p
					       missing-frame-action error-p
					       frame)
			    (fix-up-facet-specs template-facets kb to-kb
						frame-handle-mapping-table
						kb-local-only-p
						missing-frame-action error-p
						frame)
			    (fix-up-slot-specs own-slots kb to-kb
					       frame-handle-mapping-table
					       kb-local-only-p
					       missing-frame-action error-p
					       frame)
			    (fix-up-facet-specs own-facets kb to-kb
						frame-handle-mapping-table
						kb-local-only-p
						missing-frame-action error-p
						frame)
			    primitive-p new-handle
			    (funcall *compute-pretty-name-for-copy-frame-hook*
				     name new-name pretty-name new-handle to-kb)
			    kb-local-only-p)))
	    (let ((new-frame
		   (apply 'create-frame-internal
			  (if (or (typep kb 'network-kb)
				  (typep to-kb 'network-kb)
				  (typep kb 'network-structure-kb)
				  (typep to-kb 'network-structure-kb)
				  (not (subtypep (type-of to-kb)
						 (type-of kb))))
			      (decontextualize-internal
			       args :value kb) ;;; !!!!
			      ;; We're in the same address space and using the
			      ;; same implementation
			      args))))
	      (values new-frame *allocated-frame-handle-alist*
		      :new-frame-created))))))))

;------------------------------------------------------------------------------

(defokbcop okbc:copy-kb ((from-kb :value) (to-kb :value)
			 &key (error-p t) (missing-frame-action :stop)
			 (kb-local-only-p nil))
  :returned-values :void
  :manual-category :kb
  :doc-string
  "Copies the frames in \\karg{from-kb} into \\karg{to-kb}.
   The interpretation of \\karg{Missing-frame-action} is the same as
   for \\kfn{copy-frame}.  If \\karg{error-p} is \\false, catches errors that
   occur, and attempts to continue with copying.  Returns no values.

   Note that the behavior {\\tt are-frames} might have different values for
   the two KBs.  Thus, if slots are represented as frames in
   \\karg{kb}, but are not represented as frames in \\karg{to-kb}, the frames
   representing slots in \\karg{kb} will not be copied."
  :causes-side-effects-p to-kb
  :arguments-to-kb-specialize (from-kb to-kb)
  :default-body
  (default-copy-kb from-kb to-kb error-p missing-frame-action
		   kb-local-only-p))

(defun warn-about-untranslated-facets (kb)
  (when (> (hash-table-count *untranslated-facet-frames*) 0)
    (let ((all nil))
      (maphash #'(lambda (k v) (declare (ignore k)) (push v all))
	       *untranslated-facet-frames*)
      (format t "~%;;; Warning -- Facets not copied because facets are not ~
                         supported by ~%;;; KB ~A for frame~P:~{~%    ~A~}"
	      (name kb) (length all) (sort all #'string<)))
    (clrhash *untranslated-facet-frames*)
    nil))
  
(defun default-copy-kb (from-kb to-kb error-p missing-frame-action
				kb-local-only-p &key
				(roots (get-kb-roots-internal
					from-kb :all kb-local-only-p)
				       supplied-p)
				(copy-slots-p t)
				(copy-facets-p t)
				(copy-individuals-p t)
				(copy-p-predicate nil))
  (declare (special *okbc-standard-names*))
  (let ((visited-table (make-hash-table))
	;; Maps (name source-handle) tuples to target-handles.
	(frame-handle-mapping-table (make-hash-table :test #'equal))
	(*untranslated-facet-frames* (make-hash-table :test #'equal))
	(classes-copied nil)
	(slots-copied nil)
	(slots-to-copy (make-hash-table :test #'eq))
	(facets-to-copy (make-hash-table :test #'eq)))
    (format t "~%Copying class graph.")
    (loop for class in roots
	  do (copy-subclasses class from-kb to-kb error-p missing-frame-action
			      visited-table frame-handle-mapping-table 
			      kb-local-only-p roots supplied-p
			      copy-p-predicate))
    (maphash #'(lambda (k v)
		 (declare (ignore v))
		 (push k classes-copied))
	     visited-table)
    (flet ((copy-for-individual (i)
	     (when (not (gethash i visited-table))
	       (let ((new-name (get-frame-name-internal i from-kb
							kb-local-only-p)))
		 (when (and (or (not (member new-name
					     *okbc-standard-names*))
				(not (coercible-to-frame-p-internal
				      new-name to-kb kb-local-only-p)))
			    (or (not copy-p-predicate)
				(funcall copy-p-predicate i from-kb to-kb
					 missing-frame-action kb-local-only-p 
					 roots)))
		   (copy-frame-internal i new-name from-kb to-kb error-p
					missing-frame-action
					frame-handle-mapping-table
					kb-local-only-p)))
	       (setf (gethash i visited-table) t))))
      (when (or (eq copy-slots-p :only-if-used)
		(eq copy-facets-p :only-if-used))
	(loop for class in classes-copied
	      for own-slots = (get-frame-slots-internal
			       class from-kb :direct :own kb-local-only-p)
	      for template-slots = (get-frame-slots-internal
				    class from-kb :direct :template
				    kb-local-only-p)
	      do (flet ((handle-slot (s slot-type)
			  (setf (gethash s slots-to-copy) t)
			  (let ((facets (get-slot-facets-internal
					 class s from-kb :direct slot-type
					 kb-local-only-p)))
			    (loop for facet in facets
				  do (setf (gethash facet facets-to-copy)
					   t)))))
		   (loop for s in template-slots do (handle-slot s :template))
		   (loop for s in own-slots do (handle-slot s :own)))))
      (when copy-slots-p
	(format t "~%Copying slots.")
	(loop for i in (get-kb-slots-internal from-kb :frames kb-local-only-p)
	      when (and (frame-in-kb-p-internal i from-kb kb-local-only-p)
			(case copy-slots-p
			  (:only-if-used (gethash i slots-to-copy))
			  (otherwise t)))
	      do (push i slots-copied)
	         (copy-for-individual i)))
      (when copy-facets-p
	(format t "~%Copying facets.")
	(loop for i in (get-kb-facets-internal
			from-kb :frames kb-local-only-p)
	      when (and (frame-in-kb-p-internal i from-kb kb-local-only-p)
			(case copy-facets-p
			  (:only-if-used (gethash i facets-to-copy))
			  (otherwise t)))
	      do (copy-for-individual i)))
      (when copy-individuals-p
	(format t "~%Copying individuals.")
	(loop for i in (get-kb-individuals-internal
			from-kb :frames kb-local-only-p)
	      when (and (frame-in-kb-p-internal i from-kb kb-local-only-p)
			(not (slot-p-internal i from-kb kb-local-only-p))
			(not (facet-p-internal i from-kb kb-local-only-p)))
	      do (copy-for-individual i))))
    ;;; Maybe at this point we should loop through the allocated frame handles
    ;;; and check against the visited frames, and try to copy the remainder.
    ;;; Not clear what the right thing to do is.
    ;;; Return this just for Lisp debugging reasons.
    (warn-about-untranslated-facets to-kb)
    (values frame-handle-mapping-table visited-table)))

(defun copy-subclasses (parent from-kb to-kb error-p missing-frame-action
			       visited-table frame-handle-mapping-table
			       kb-local-only-p roots just-this-subgraph-p
			       copy-p-predicate)
  (cond ((gethash parent visited-table) :already-visited)
	(t (setf (gethash parent visited-table) t)
	   (let ((testfn (decanonicalize-testfn :eql from-kb kb-local-only-p)))
	     (loop for super in (get-class-superclasses-internal
				 parent from-kb :direct :all kb-local-only-p)
		   when (and (frame-in-kb-p-internal
			      super from-kb kb-local-only-p)
			     ;; Don't move back up the class graph above the
			     ;; specified roots.  Also exclude any classes that
			     ;; we might have got to that are superclasses of
			     ;; the specified roots.
			     (not (member super roots :test testfn))
			     (not (loop for root in roots
					thereis (subclass-of-p-internal
						 root super from-kb :taxonomic
						 kb-local-only-p)))
			     ;; We must be in the selected subgraph!
			     (or (not just-this-subgraph-p)
				 (loop for root in roots
					thereis (subclass-of-p-internal
						 super root from-kb :taxonomic
						 kb-local-only-p))))
		   do (copy-subclasses super from-kb to-kb error-p
				       missing-frame-action visited-table
				       frame-handle-mapping-table
				       kb-local-only-p roots
				       just-this-subgraph-p copy-p-predicate)))
	   (let ((this-one
		  (if (and copy-p-predicate
			   (not (funcall copy-p-predicate parent from-kb to-kb
					 missing-frame-action kb-local-only-p 
					 roots)))
		      (list :filtered-out nil)
		      (multiple-value-bind (frame found-p)
			(get-frame-in-kb-internal parent to-kb nil
						  kb-local-only-p)
			(if (or (not found-p)
				(not (class-p-internal parent to-kb
						       kb-local-only-p)))
			    (copy-frame-internal
			     parent (get-frame-name-internal parent from-kb
							     kb-local-only-p)
			     from-kb to-kb error-p missing-frame-action
			     frame-handle-mapping-table kb-local-only-p)
			    (list :already-there frame))))))
	     (let ((subclasses (get-class-subclasses-internal
				parent from-kb :direct :all kb-local-only-p)))
	       ;; (format t "~%;; Subclasses of ~A are ~S" parent subclasses)
	       (values (list parent this-one)
		       (loop for sub in subclasses
			     when (frame-in-kb-p-internal sub from-kb
							  kb-local-only-p)
			     collect (list sub
					   (copy-subclasses
					    sub from-kb to-kb error-p
					    missing-frame-action visited-table
					    frame-handle-mapping-table
					    kb-local-only-p roots
					    just-this-subgraph-p
					    copy-p-predicate)))))))))

;------------------------------------------------------------------------------

(defokbcop okbc:create-class ((name :value) &key (kb (current-kb)) direct-types
			      direct-superclasses (primitive-p t) doc
			      template-slots template-facets own-slots
			      own-facets handle pretty-name
			      (kb-local-only-p nil))
  :returned-values new-class
  :manual-category :class
  :doc-string
  "Creates a class called \\karg{name} as a direct subclass
   of the list of classes (or class) \\karg{direct-superclasses}.  For KRSs
   that support the distinction between primitive and nonprimitive concepts,
   \\karg{primitive-p} specifies the primitiveness of the created class.
   The parameters \\karg{doc}, \\karg{template-slots},
   \\karg{template-facets}, \\karg{own-slots}, \\karg{own-facets}, 
   \\karg{direct-types}, \\karg{handle}, and \\karg{pretty-name} have the
   same meaning as for \\kfn{create-frame}.  For KRSs that support metaclasses,
   the \\karg{direct-types} argument specifies the type(s) of the class
   to be created (i.e., metaclasses).  Returns the \\karg{new-class}."
  :compliance-classes :write
  :tell&ask-default-body
  (create-frame-internal name :class kb direct-types
			 direct-superclasses doc
			 template-slots template-facets own-slots
			 own-facets primitive-p handle pretty-name
			 kb-local-only-p)
  :causes-side-effects-p t
  :monitor-body
  (record-reference name nil t nil kb)
  :modification-body
  (progn
    (record-modification name kb :create)
    (loop for class in (if (listp direct-superclasses)
			   direct-superclasses
			   (list direct-superclasses))
	  do (record-modification class kb :modify))))


(defokbcop okbc:create-facet
    ((name :value) &key (kb (current-kb)) (frame-or-nil nil)
     (slot-or-nil nil) (slot-type :own) (direct-types nil)
     (doc nil) (own-slots nil) (own-facets nil) (handle nil)
     (pretty-name nil) (kb-local-only-p nil))
  :returned-values new-facet
  :manual-category :facet
  :doc-string
  "Creates a facet called \\karg{name} on \\karg {slot-or-nil} that is
   associated with \\karg{frame-or-nil}.  If \\karg{frame-or-nil} is \\false,
   the facet's frame domain is unconstrained (i.e., the facet may apply to
   \\karg{slot-or-nil} in any frame).

   If \\karg{slot-or-nil} is \\false, the slot domain of the facet is
   unconstrained (i.e., the facet may apply to all slots in
   \\karg{frame-or-nil}, and if \\karg{frame-or-nil} is also \\false, may
   apply to all slots in all frames.)
   If {\\tt :facet} is a member of the behavior values for the
   {\\tt :are-frames} behavior, \\karg{direct-types},
   \\karg{doc}, \\karg{own-slots}, \\karg{own-facets}, \\karg{handle} and
   \\karg{pretty-name} have the same interpretation as for \\kfn{create-frame}.
   If either \\karg{frame-or-nil} or \\karg{slot-or-nil} is \\false,
   \\karg{slot-type} is ignored.  If either of the \\karg{frame-or-nil} or
   \\karg{slot-or-nil} arguments is
   \\false, and the KRS does not support facets with unconstrained domains,
   a \\kcond{domain-required} error will be signaled.
   If facets must be uniquely named and a facet named \\karg{name} already
   exists, a \\kcond{facet-already-exists} error will be signalled.
   Returns the \\karg{new-facet}."
  :tell&ask-default-body
  ((declare (ignore frame-or-nil slot-or-nil slot-type))
   (create-frame-internal name :facet kb direct-types
			  nil doc nil nil own-slots
			  own-facets t handle pretty-name
			  kb-local-only-p))
  :compliance-classes (:write :facets)
  :causes-side-effects-p t)

(defokbcgeneric create-frame-primitive-p-sentences (frame primitive-p kb)
  (:documentation
   "The sentences to assert during a create-frame operation that are a
    consequence of the setting of the primitive-p argument.  The sentences
    returned should be closed."))

(defmethod create-frame-primitive-p-sentences (frame primitive-p (kb t))
  (if primitive-p
      `((:primitive ,frame))
      nil))
  
(defokbcop okbc:create-frame ((name :value) (frame-type :value)
			      &key (kb (current-kb)) direct-types
			      direct-superclasses doc 
			      template-slots template-facets
			      own-slots own-facets (primitive-p t)
			      (handle nil) (pretty-name nil)
			      (kb-local-only-p nil))
  :returned-values new-frame
  :manual-category :frame
  :doc-string
  "Creates a new frame called \\karg{name} of type \\karg{frame-type}.
   \\karg{Frame-type} is one of \\{{\\tt :class}, {\\tt :slot}, {\\tt :facet},
   {\\tt :individual}\\}.  A call to \\karg{create-frame} is equivalent to
   a call to one of \\kfn{create-class}, \\kfn{create-individual},
   \\kfn{create-slot}, or \\kfn{create-facet} passing through the appropriate
   arguments, depending on the value of \\karg{frame-type}.  If
   \\karg{frame-type} is either {\\tt :slot} or {\\tt :facet}, the slot
   (or facet) created will have unconstrained domains.

   If the {\\tt :frame-names-required} behavior has the value \\false\\ for
   \\karg{kb}, \\karg{new-name} may be \\false.  If the
   {\\tt :frame-names-required} behavior is \\true\\ for \\karg{kb},
   \\karg{new-name} must uniquely name the new frame, and a
   \\kcond{frame-already-exists} error will be signaled if \\karg{new-name}
   is coercible to an existing frame.

   \\karg{Direct-types} is a list of classes (or class) of which this new
   frame is to be a direct instance.
   \\karg{Direct-superclasses} is a list of classes (or class) of which the
   new frame is to be a direct subclass.
   \\karg{Doc}, if specified, is a string documenting the new frame.
   \\karg{Pretty-name} is the pretty-name of the new frame.  Returns
   \\karg{new-frame}, which identifies the newly created frame.

   \\karg{Template-slots} and \\karg{own-slots} each take a list of slot 
   specifications.  A slot specification assigns a set of values to a
   slot.  The syntax of a slot specification is
   \\begin{verbatim}
        slot-spec ::= (slot slot-value-spec*)
        slot-value-spec ::= default-slot-value | slot-value
        default-slot-value ::= (:default slot-value)
   \\end{verbatim}
   where {\\tt slot} identifies a slot, or names a slot to be created.  If
   {\\tt slot} already exists, it is simply attached to the new frame, if
   it does not currently exist, it is created and attached to the new frame.
   Each {\\tt slot-value} is an entity suitable as a value of
   the specified slot.  Default slot values are identified by appearing in
   a list whose first element is {\\tt :default}.  Template slots are only
   allowed for class frames -- that is, when \\karg{frame-type} is
   {\\tt :class}.
   
   \\karg{Template-facets} and \\karg{own-facets} each take a list of facet 
   specifications, which can assign a set of facet values.  A facet
   specification has the form:
   \\begin{verbatim}
        facet-spec ::= (slot fspec*)
        fspec ::= (facet facet-value-spec*)
        facet-value-spec ::= default-facet-value | facet-value
        default-facet-value ::= (:default facet-value)
   \\end{verbatim}
   where {\\tt slot} identifies a slot, or names a slot to be created.  If
   {\\tt slot} already exists, it is simply attached to the new frame, if
   it does not currently exist, it is created and attached to the new frame.
   {\\tt Facet} identifies a facet, or names a facet to be created.  If
   {\\tt facet} already exists, it is simply attached to \\karg{slot} on
   the new frame, if it does not currently exist, it is created and attached
   to \\karg{slot} on the new frame.  Each {\\tt facet-value} is an object
   suitable as a value of the specified facet.  Default facet values are
   identified by appearing in a list whose first element is {\\tt :default}.  
   Template facets are allowed only for class frames -- that is, when
   \\karg{frame-type} is {\\tt :class}.

   All slot and facet names in slot and facet specs are defined in a unified
   namespace that operates across all of the {\\tt :own-slots},
   {\\tt :own-facets}, {\\tt :template-slots}, and {\\tt :template-facets}
   arguments.  Thus, in the following  example, all occurrences of the slot
   {\\tt s1} and the facet {\\tt f1} denote the same slot and facet
   respectively.

   The values specified in slot and facet specifications are interpreted
   conjunctively.  Thus, in the following example, the slot
   {\\tt s1} will have three values; 42, 100 and 2001, rather than just
   the value 2001.
   \\begin{verbatim}
      (create-frame 'foo :class
                    :own-slots '((s1 42 100)
                                 (s1 2001))
                    :own-facets '((s1 (:value-type :integer))
                                  (s1 (f1 \"Own hello\")))
                    :template-facets '((s1 (f1 \"Template hello\"))))
   \\end{verbatim}

   \\karg{Primitive-p} may be used only when creating a class.
   When \\karg{primitive-p} is \\false, the KRS will make
   the class nonprimitive, if possible.

   \\karg{Handle}, if supplied, is a previously allocated frame handle for the
   new frame to be created.  This is used by network applications, and
   operations such as \\kfn{copy-frame} and \\kfn{copy-kb}.  (See
   \\kfn{allocate-frame-handle}.)  It is an error to supply a value for the
   \\karg{handle} argument that is already coercible to a frame.  If this
   occurs, a \\kcond{frame-already-exists} error should be signaled.

   Note that if \\karg{frame-type} is either {\\tt :slot} or {\\tt :facet},
   then a {\\em frame} might not be created because slots (or facets) might not
   be represented as frames in \\karg{kb}.  If this is the case, and slots
   (or facets) with unconstrained domains are not supported, a
   \\kcond{domain-required} error will be signaled.

   It is an error to supply \\karg{own-slots}, \\karg{own-facets} if a frame
   will not be created, according to the {\\tt :are-frames} behavior, and a
   \\kcond{not-a-frame-type} error should be signaled."
  :causes-side-effects-p t
  :monitor-body
  (record-reference name nil t nil kb)
  :modification-body
  (progn
    (record-modification name kb :create)
    (loop for class in (append (if (listp direct-types)
				   direct-types
				   (list direct-types))
			       (if (listp direct-superclasses)
				   direct-superclasses
				   (list direct-superclasses)))
	  do
	  (record-modification class kb :modify)))
  :standard-default-body
  (progn
    ;; Note:  this restriction is arbitrary, but is made for
    ;;        stylistic/aesthetic reasons.
    (continuable-assert
     (or (stringp name) (symbolp name) (integerp name))
     () "Frame names can only be strings symbols or integers")
    (continuable-assert
     (or (not (or own-slots own-facets))
	 (member frame-type (get-behavior-values-internal :are-frames kb)))
     not-a-frame-type :frame-type frame-type :kb kb)
    (let ((frame
	   (ecase frame-type
	     (:class
	      (create-class-internal
	       name         kb      direct-types
	                    (list-if-not direct-superclasses)
			    primitive-p
			                          doc
						  template-slots
						  template-facets
						     own-slots own-facets
	      handle pretty-name kb-local-only-p))
	     (:individual
	      (create-individual-internal
	       name         kb       direct-types doc own-slots own-facets
	       handle pretty-name kb-local-only-p))
	     (:slot
	      (create-slot-internal
	       name     kb nil  :all direct-types doc own-slots own-facets
	       handle pretty-name kb-local-only-p))
	     (:facet
	      (create-facet-internal
	       name kb nil nil  :all direct-types doc own-slots own-facets
	       handle pretty-name kb-local-only-p)))))
      frame))
  :tell&ask-default-body
  (multiple-value-bind (frame sentence default-clauses)
    (build-assertion-for-tell-and-ask-create-frame
     name frame-type kb direct-types direct-superclasses doc
     template-slots template-facets own-slots own-facets
     primitive-p handle pretty-name kb-local-only-p)
    (tell-internal sentence kb frame :known-true kb-local-only-p)
    (when default-clauses
      (tell-internal `(:and ,@default-clauses) kb frame :known-true
		     kb-local-only-p))
    frame))

(defmethod build-assertion-for-tell-and-ask-create-frame
    (name frame-type kb direct-types direct-superclasses doc template-slots
	  template-facets own-slots own-facets primitive-p handle pretty-name
	  kb-local-only-p)
  (let ((frame (or handle
		   (allocate-frame-handle-internal name frame-type kb nil)))
	(default-clauses nil)
	(defined-slot-alist nil)
	(defined-facet-alist nil))
    (values
     frame
     `(:and
       (:frame ,frame)
       (:handle ,frame ,(or handle frame)) ;**:handle
       (,frame-type ,frame)
       ,@(if name `((:name ,frame ,name)) nil)
       ,@(if pretty-name `((:pretty-name ,frame ,pretty-name)) nil)
       ,@(if doc `((:documentation ,frame ,doc)) nil)
       ,@(loop for type in (list-if-not direct-types)
	       collect `(:instance-of ,frame ,type))
       ;; ** didn't check that we had a :class before asserting thing!
       ,@(loop for superclass in (or (list-if-not direct-superclasses)
				     (if (and (eql frame-type :class)
					      (not (eql name :thing)))
					 '(:thing) nil))
	       collect `(:subclass-of ,frame ,superclass))
       ,@(if (eq :class frame-type)
	     (create-frame-primitive-p-sentences frame primitive-p kb)
	     nil)
       ,@(loop for specs in (list own-slots template-slots)
	       for slot-type in '(:own :template)
	       for relation-spec = (ecase slot-type
				     (:template '(:template-slot-value))
				     (:own nil))
	       for slot-of-spec = (ecase slot-type
				    (:template :template-slot-of)
				    (:own :slot-of))
	       append
	       (loop for spec in specs
		     for slot-name = (first-if-list spec)
		     for values = (if (listp spec) (rest spec) nil)
		     for slot = (or (second (assoc slot-name
						   defined-slot-alist))
				    (let ((s (ensure-has-slot
					      slot-name slot-type kb
					      kb-local-only-p)))
				      (push (list slot-name s)
					    defined-slot-alist)
				      s))
		     append
		     (if values
			 (loop for value-spec in values
			       for value =
			       (if (and (consp value-spec)
					(eq :default (first value-spec)))
				   (second value-spec)
				   value-spec)
			       for default-p =
			       (and (consp value-spec)
				    (eq :default
					(first value-spec)))
			       for clause =
			       `(,@relation-spec ,slot ,frame ,value)
			       when default-p
			       do (push clause default-clauses)
			       when (not default-p)
			       collect clause)
			 `((,slot-of-spec ,slot ,frame)))))
       ,@(loop for specs in (list own-facets template-facets)
	       for slot-type in '(:own :template)
	       for relation-spec = (ecase slot-type
				     (:template '(:template-facet-value))
				     (:own nil))
	       for slot-of-spec = (ecase slot-type
				    (:template :template-slot-of)
				    (:own :slot-of))
	       for facet-of-spec = (ecase slot-type
				     (:template :template-facet-of)
				     (:own :facet-of))
	       append
	       (loop for spec in specs
		     for slot-name = (first-if-list spec)
		     for slot = (or (second (assoc slot-name
						   defined-slot-alist))
				    (let ((s (ensure-has-slot
					      slot-name slot-type kb
					      kb-local-only-p)))
				      (push (list slot-name s)
					    defined-slot-alist)
				      s))
		     for facet-specs =
		     (if (listp spec) (rest spec) nil)
		     append
		     (if facet-specs
			 (loop for spec in facet-specs
			       for facet-name = (first-if-list spec)
			       for values = (if (listp spec)
						(rest spec)
						nil)
			       for facet =
			       (or (second (assoc facet-name
						  defined-facet-alist))
				   (let ((fa (ensure-has-facet
					      facet-name slot slot-type
					      kb kb-local-only-p)))
				     (push (list facet-name fa)
					   defined-facet-alist)
				     fa))
			       append
			       (if values
				   (loop for value-spec in values
					 for value =
					 (if (and (consp value-spec)
						  (eq :default
						      (first
						       value-spec)))
					     (second value-spec)
					     value-spec)
					 for default-p =
					 (and (consp value-spec)
					      (eq :default
						  (first
						   value-spec)))
					 for clause =
					 `(,@relation-spec
					   ,facet ,slot ,frame ,value)
					 when default-p
					 do (push clause default-clauses)
					 when (not default-p)
					 collect clause)
				   `((,facet-of-spec
				      ,facet ,slot ,frame))))
			 `((,slot-of-spec ,slot ,frame))))))
     default-clauses)))

(defokbcgeneric ok-back:ensure-has-slot (slot slot-type kb kb-local-only-p)
  (:documentation "A generic function to ensure that the <code>kb</code>
   has a definition for the <code>slot</code> of the necessary
   <code>slot-type</code>.  This is called by the default implementation
   of <code>create-frame</code> for the <code>tell&ask-defaults-kb</code>
   defaults.  If you are using the tell&ask defaults middle end, and
   are not shadowing the default implementation of <code>create-frame</code>
   you will have to specialize this generic-function."))

(defmethod ok-back:ensure-has-slot ((slot t) (slot-type t) (kb t)
				    (kb-local-only-p t))
  (undefined-method 'ensure-has-slot kb))

(defokbcgeneric ok-back:ensure-has-facet
    (facet slot slot-type kb kb-local-only-p)
  (:documentation "A generic function to ensure that the <code>kb</code>
   has a definition for the <code>facet</code> on the <code>slot</code> of the
   necessary <code>slot-type</code>.  This is called by the default
   implementation of <code>create-frame</code> for the
   <code>tell&ask-defaults-kb</code> defaults.  If you are using the tell&ask
   defaults middle end, and are not shadowing the default implementation of
   <code>create-frame</code> you will have to specialize this generic
   function."))

(defmethod ok-back:ensure-has-facet
   ((facet t) (slot t) (slot-type t) (kb t) (kb-local-only-p t))
  (undefined-method 'ensure-has-facet kb))

(defokbcop okbc:create-individual (name &key (kb (current-kb)) direct-types
					doc own-slots own-facets
					handle pretty-name kb-local-only-p)
  :returned-values new-individual
  :manual-category :individual
  :doc-string
  "Creates an individual called \\karg{name}.  The one or more classes 
   that are the direct types of the instance are given by
   \\karg{direct-types}.  
   The parameters \\karg{doc}, \\karg{own-slots}, \\karg{own-facets},
   \\karg{handle}, and \\karg{pretty-name} all have the same meaning as for
   \\kfn{create-frame}.  Returns \\karg{new-individual}, which identifies the
   new frame."
  :compliance-classes :write
  :tell&ask-default-body
  (create-frame-internal name :individual kb direct-types
			 nil doc nil nil own-slots
			 own-facets t handle pretty-name
			 kb-local-only-p)
  :causes-side-effects-p t
  :monitor-body
  (record-reference name nil t nil kb)
  :modification-body
  (progn
    (record-modification name kb :create)
    (loop for class in (if (listp direct-types)
			   direct-types
			   (list direct-types))
	  do (record-modification class kb :modify))))


(defokbcop okbc:create-kb ((name :value) &key (kb-type nil)
			   (kb-locator nil) (initargs nil)
			   (connection (local-connection)))
  :returned-values new-kb
  :manual-category :kb
  :doc-string
  "Creates a new KB (see Section~\\ref{sec:kb}) called \\karg{name} whose
   implementation type is \\karg{kb-type}.  \\karg{Kb-type} identifies the
   underlying KRS that will be used to manipulate the KB.  Returns the
   \\karg{new-kb}.

   Note that this operation creates a new {\\em in-memory} KB; it does
   not necessarily create a persistent version of the knowledge base on
   external storage until \\kfn{save-kb} or \\kfn{save-kb-as} is called.

   The \\karg{name} of the KB is a symbol.

   \\karg{kb-locator}, if supplied, describes the new KB.  Kb-locators can be
   created using \\kfn{create-kb-locator}.
   If \\karg{kb-locator} is not supplied, a default kb-locator will be assigned
   by the KRS for \\karg{kb-type} and \\karg{connection}.

   \\karg{Initargs} is a list of initializations for the new KB as
   required by the \\karg{kb-type}.  The mechanism underlying the
   implementation of \\kfn{create-kb} is not specified and the user cannot,
   therefore, rely on any underlying native object system initialization
   protocol being invoked.  The format and content of the initialization
   arguments will be documented with the \\karg{kb-type}.  For example,
   if the KB being created allows the specification of parent (included) KBs,
   a set of initialization arguments might be as follows:
   \\begin{verbatim}
     (list :parent-kbs (list my-kb))
   \\end{verbatim}
   Any KB created with \\kfn{create-kb} can be found by using
   either \\kfn{find-kb} or \\kfn{find-kb-of-type}, and it is included in
   the values returned by \\kfn{get-kbs}.  A KB created with
   \\kfn{create-kb} is a frame object in the \\kfn{meta-kb}.

   Implementation note:  It is the responsibility of the implementations of
   \\kfn{create-kb} to register new KBs in the Meta KB (for example, by using
   \\kfn{put-instance-types} to tell the Meta KB that the new KB is an instance
   of \\karg{kb-type}."
  :causes-side-effects-p t
  :arguments-to-kb-specialize (kb-type)
  :default-body
  (internal-create-kb name kb-type kb-locator initargs connection))

(defmethod internal-create-kb (name  kb-type kb-locator initargs connection)
  (assert (typep name '(or symbol quasi-symbol)) ()
	  (error "Remote KB name ~S is not a symbol or quasi-symbol" name))
  (let ((new-kb
	 (if (typep kb-type 'structure-object)
	     (let ((type (type-of-name kb-type)))
	       (let ((creator (find-symbol
			       (concatenate 'string "MAKE-" (symbol-name type))
			       (symbol-package type))))
		 (continuable-assert
		  creator ()
		  "Cannot find creator function for kb type ~S"
		  type)
		 (apply creator :name name initargs)))
	     (apply #'make-instance (class-of kb-type)
		    :name name
		    :connection connection
		    initargs))))
    ;; Note: All the following code refers to the local connection.
    ;; This is intentional, since it is the responsibility of the guy
    ;; at the other end to fill in the locator.
    (put-instance-types-internal new-kb (list (class-of kb-type))
				 (meta-kb-internal (local-connection)) t)
    (when (not (slot-p-internal :locator (meta-kb-internal connection) t))
      (create-slot-internal :locator (meta-kb-internal (local-connection))
			    nil :own nil nil nil nil nil "Locator" nil))
    (put-slot-value-internal new-kb :locator
			     (or kb-locator (create-kb-locator-internal
					     new-kb kb-type
					     (local-connection)))
			     (meta-kb-internal (local-connection))
			     :own :known-true t)
    new-kb))

(defokbcop okbc:create-kb-locator (thing &key (kb-type nil)
					 (connection (local-connection)))
  :returned-values kb-locator
  :manual-category :kb
  :doc-string
  "Returns a new \\karg{kb-locator} associated with \\karg{thing} for a kb of
   type \\karg{kb-type}.  If \\karg{thing} is a KB, the kb-locator created is
   associated with that KB in the \\kfn{meta-kb}.  It is an error for
   \\karg{thing} to be an incomplete description of a kb-locator.

   \\karg{Thing} is a \\karg{kb-type} and \\karg{connection} specific
   specification of a KB location sufficient to create and fully
   initialize a KB locator.

   For example, \\karg{thing} may identify the pathname for a KB that
   resides in a disk file.  Each back-end implementation must provide
   documentation for all values of \\karg{thing} that the \\karg{kb-type}
   and \\karg{connection} will accept other than KBs, which are always
   accepted.

   Implementation note: Back end implementators may use any legal
   OKBC value entity for the \\karg{thing} argument as long as it
   consists only of the primitive data types: integer, float, string,
   symbol, true, false, or list.  Values of \\karg{thing} of these data
   types will always be transmitted by networked implementations without
   substitution of remote references.  For example, the following
   could be a legal value for for the \\karg{thing} argument for some
   \\karg{kb-type}
   \\begin{verbatim}
     (:db-file \"/projects/foo/my-database.data\" :db-type :oracle :name my-kb)
   \\end{verbatim}"
  :compliance-classes :write)

(defokbcop okbc:create-procedure
    (&key (kb (current-kb)) (arguments nil) (body nil) (environment nil))
  :returned-values procedure
  :manual-category :funspec
  :doc-string
  "Defines and returns a procedure in the OKBC procedure language.  The
   arguments are defined as follows:
   \\bitem
   \\item \\karg{arguments} -- the argument list for the procedure.  The
          argument list can be expressed in one of three forms.
          \\begin{enumerate}
          \\item A list of symbols
          \\item A string that is the printed representation of a list
                 of symbols
          \\item \\false -- the null argument list
          \\end{enumerate}
          For example, the argument lists {\\tt (a b c)}, and
          {\\tt \"(a b c)\"} are equivalent, as are {\\tt \"()\"} and \\false.
          The string representation is provided for language bindings in
          which it may be inconvenient to create lists of symbols.
   \\item \\karg{body} -- The body for the procedure expressed in the syntax
          defined in section~\\ref{ch:funspecs}.  The body can be
          provided in one of two forms:
          \\begin{enumerate}
          \\item A {\\tt body-form}
          \\item A list of {\\tt body-form}s
          \\item A string that is the printed representation of a sequence
                 of {\\tt body-form}s
          \\end{enumerate}
          For example, the following procedure bodies are equivalent:
          \\begin{verbatim}
          ((put-slot-values frame slot values :slot-type :own)
           (get-slot-value frame slot :slot-type :own))
          \\end{verbatim}
          and
          \\begin{verbatim}
          \"(put-slot-values frame slot values :slot-type :own)
           (get-slot-value frame slot :slot-type :own)\"
          \\end{verbatim}
          The string representation is provided for language bindings in
          which it may be inconvenient to create the complex list structure
          required in the procedure language.
   \\item \\karg{environment} -- A predefined set of bindings between variables
          mentioned in the procedure \\karg{body} and their associated values.
          The environment is a list of 2-tuples of the form
          \\begin{verbatim}
          ((var1 value1)
           (var2 value2)
           ....
           (varn valuen))
          \\end{verbatim}
          where {\\tt varN} are the variables mentioned in \\karg{body}, and
          {\\tt valueN} are the associated values for the variables.
   \\eitem
   A procedure is a legal argument to any OKBC operator in a position that
   expects a procedure.
   For example,
   \\begin{verbatim}
    (call-procedure
      #'(lambda (frame) (get-frame-pretty-name frame :kb kb))
      :kb kb :arguments (list my-frame))
   \\end{verbatim}
   and
   \\begin{verbatim}
    (call-procedure
      (create-procedure :arguments '(frame)
                        :body '(get-frame-pretty-name frame :kb kb))
      :kb my-kb :arguments (list my-frame))
   \\end{verbatim}
   are semantically identical.

   The main differences between
   procedures and lambda expressions in Lisp are as follows:
   \\benum
   \\item All bindings in procedures are dynamic, not lexical.
   \\item Only a restricted set of operations is available in procedures.
   \\item Lambda defines a {\\em lexical} closure over any free references.
     \\karg{procedure} defines a {\\em dynamic} closure over its free
     references.  The environment of the procedure is
     prefilled with bindings for the names of the arguments to
     the OKBC operator in which it is being executed.  In the above
     case, \\karg{call-procedure} takes arguments \\karg{KB},
     \\karg{Arguments}, and \\karg{Kb-local-only-p}
     which will take on the values \\code{my-kb}, \\code{(my-frame)}, and
     \\code{nil} (the default), respectively.
   \\item Lambda expressions are meaningful only within the Lisp system
     in which the OKBC system is running.  procedures are
     executable on any (possibly network-connected) OKBC KB.
   \\item procedures are package-insensitive in all respects
   other than quoted constants.
   \\eenum

   Note that persistent side effects to \\code{<<var1>>} and \\code{<<var2>>}
   cannot be made from within the procedure.  The arguments and variables
   mentioned in the procedure exist in a different space from the variables
   in a user program.  The only ways to establish associations between values
   in a user program and variables in a procedure are through the use of the
   \\karg{environment} argument to \\kfn{create-procedure}, or by the
   \\karg{arguments} argument to \\kfn{call-procedure}."
  :default-body (default-create-procedure
		    nil arguments
		  (if (stringp body) (list body) body)
		  environment kb))

(defokbcop okbc:create-slot ((name :value) &key (kb (current-kb))
			     (frame-or-nil nil)
			     (slot-type :all) (direct-types nil) (doc nil)
			     (own-slots nil) (own-facets nil) (handle nil)
			     (pretty-name nil) (kb-local-only-p nil))
  :returned-values new-slot
  :manual-category :slot
  :doc-string
  "Creates a slot called \\karg{name} in the frame specified by
   \\karg{frame-or-nil}.  Returns the \\karg{new-slot}.  If the slot to be
   created is to be represented as a frame ({\\tt :slot} is a member of the
   {\\tt :are-frames} behavior), \\karg{direct-types},
   \\karg{doc}, \\karg{own-slots}, \\karg{own-facets}, \\karg{handle}, and
   \\karg{pretty-name} have the same interpretation as for \\kfn{create-frame}.
   If \\karg{frame-or-nil} is \\false, \\karg{slot-type} is ignored, and the
   slot's domain is ignored.  If the
   \\karg{frame} argument is \\false, and the KRS does not support slots with
   unconstrained domains, a \\kcond{domain-required} error will be signaled.
   If slots must be uniquely named and a slot named \\karg{name} already
   exists, a \\kcond{slot-already-exists} error will be signalled."
  :compliance-classes :write
  :tell&ask-default-body
  ((declare (ignore frame-or-nil slot-type))
   (create-frame-internal name :slot kb direct-types
			  nil doc nil nil own-slots
			  own-facets t handle pretty-name
			  kb-local-only-p))
  :causes-side-effects-p t
  :modification-body
  (progn
    (record-modification name kb :create)
    (when frame-or-nil
      (if (listp frame-or-nil)
	  (loop for x in frame-or-nil do
		(record-modification x kb :modify))
	(record-modification frame-or-nil kb :modify)))))

(defokbcop okbc:decontextualize
    (value (from-context :value) &key (kb (current-kb)))
  :returned-values decontextualized-value
  :manual-category :misc
  :doc-string
  "Given a value from \\karg{kb}, returns a
   \\karg{decontextualized-value}, which contains no KB or KRS-specific
   data structures.  In particular,
   any references to frame objects will be replaced with KRS-independent frame
   handles (produced using \\karg{frs-independent-frame-handle}), and all
   values outside the standard set of OKBC data types that have
   no interpretation outside \\karg{kb} will be
   replaced with remote-value references.  Any frame references that are
   the result of an KRS-specific mapping of a canonically named frame will be
   replaced with the canonical name.  Thus, for example, a facet
   frame called {\\tt cardinality-of-slot} would be mapped back to a frame
   handle for the canonical facet-reference {\\tt :cardinality}.

   \\karg{From-context} is one of \\{{\\tt :frame}, {\\tt :slot},
   {\\tt :facet}, {\\tt :value}\\}.  It identifies the context of the argument
   to be decontextualized.  For example, if the
   decontextualization is to be applied to a slot value, then
   \\karg{from-context} should be {\\tt :value}.  If the
   decontextualization is to be applied to a slot (i.e., something that would
   be used as a \\karg{slot} argument to an operation such as
   \\kfn{get-slot-values}), then \\karg{from-context} should be {\\tt :slot}.

   It is not anticipated that this operation will be called by OKBC
   applications, but rather by OKBC back end implementations.  It is used to
   ensure correct operation in networked applications and during communication
   between KBs of different kb-types."
  :compliance-classes :read)

(defokbcop okbc:delete-facet
    (facet &key (kb (current-kb)) (kb-local-only-p nil))
  :returned-values :void
  :manual-category :facet
  :doc-string
  "Deletes the facet from all frames containing that facet, and the facet frame
   itself if the facet is represented as a frame. As a result of
   \\kfn{delete-facet}, \\karg{facet} will return \\false\\ for calls to
   \\kfn{facet-p}, and \\karg{facet} is not returned by any of the
   facet-returning operations, such as \\kfn{get-kb-facets} and
   \\kfn{get-slot-facets}.  It is no longer possible to access any values of
   \\karg{facet}.  Returns no values.

   Many implementations may, in fact, delete the values associated the
   facet in frames as well as making the facet no longer facet-p.  Other
   implementations will simply make these values inaccessible."
  :tell&ask-default-body
  ((let ((sentences (get-frame-sentences-internal
		     facet kb :all t :default-only kb-local-only-p)))
     (loop for sentence in sentences
	   do (untell-internal sentence kb facet :default-only
			       kb-local-only-p)))
   (let ((sentences (get-frame-sentences-internal
		     facet kb :all t :known-true kb-local-only-p)))
     (loop for sentence in sentences
	   do (untell-internal sentence kb facet :known-true
			       kb-local-only-p))))
  :compliance-classes :write
  :causes-side-effects-p t
  :modification-body
    (record-modification facet kb :delete))

(defokbcop okbc:delete-frame (frame &key (kb (current-kb))
				    (kb-local-only-p nil))
  :returned-values :void
  :manual-category :frame
  :doc-string
  "Deleting a frame from a KB is difficult to specify in a portable way.
   After calling \\kfn{delete-frame}, the \\karg{frame} argument
   will no longer be a valid frame reference (\\karg{frame-p} will return
   \\false).  As a consequence, the value of \\karg{frame} will
   not be a valid argument to any OKBC operation requiring a frame reference,
   such as \\kfn{get-frame-slots}.  It will no longer be possible to access
   any of the properties (e.g., slots, facets) of
   \\karg{frame}.  Implementations will delete at least the
   properties documented as being returned by \\kfn{get-frame-details}
   from the \\karg{kb}.

   Note that after a call to \\kfn{delete-frame}, references
   to \\karg{frame} may still remain in the KB.  Returns no values."
  :compliance-classes :write
  :tell&ask-default-body
  ((let ((sentences (get-frame-sentences-internal
		     frame kb :all t :default-only kb-local-only-p)))
     (loop for sentence in sentences
	   do (untell-internal sentence kb frame :default-only
			       kb-local-only-p)))
   (let ((sentences (get-frame-sentences-internal
		     frame kb :all t :known-true kb-local-only-p)))
     (loop for sentence in sentences
	   do (untell-internal sentence kb frame :known-true
			       kb-local-only-p))))
  :causes-side-effects-p t
  :monitor-body
  ;; The method itself records the deletion of frame because once the
  ;; frame is deleted, this after method has no way of determining what
  ;; KB the frame was in.  So there is no modification body.
  (record-reference frame nil t nil kb))


(defokbcop okbc:delete-slot (slot &key (kb (current-kb)) (kb-local-only-p nil))
  :returned-values :void
  :manual-category :slot
  :doc-string
  "Deletes the slot from all frames containing that slot, and the slot frame
   itself if the slot is represented as a frame. As a result of
   \\kfn{delete-slot}, \\karg{slot} will return \\false\\ for calls to
   \\kfn{slot-p}, and \\karg{slot} is not returned by any of the
   slot-returning operations, such as \\kfn{get-kb-slots} and
   \\kfn{get-frame-slots}.  It is no longer possible to access any values of
   \\karg{slot} or any facets or facet values on \\karg{slot}.
   Returns no values.

   Many implementations may, in fact, delete the values associated the
   slot in frames as well as making the slot no longer slot-p.  Other
   implementations will simply make these values inaccessible."
  :tell&ask-default-body
  ((let ((sentences (get-frame-sentences-internal
		     slot kb :all t :default-only kb-local-only-p)))
     (loop for sentence in sentences
	   do (untell-internal sentence kb slot :default-only
			       kb-local-only-p)))
   (let ((sentences (get-frame-sentences-internal
		     slot kb :all t :known-true kb-local-only-p)))
     (loop for sentence in sentences
	   do (untell-internal sentence kb slot :known-true
			       kb-local-only-p))))
  :compliance-classes :write
  :causes-side-effects-p t
  :modification-body
    (record-modification slot kb :delete))

(defokbcop okbc:detach-facet (frame slot facet &key (kb (current-kb))
				    (slot-type :own) (kb-local-only-p nil))
  :returned-values :void
  :manual-category :facet
  :doc-string
  "Removes any explicit association between the \\karg{facet} and
   \\karg{slot} on \\karg{frame}.  As a result, \\karg{facet} is not returned
   by \\kfn{get-slot-facets} at inference-level {\\tt :direct} unless there are
   facet values associated with \\karg{facet} in \\karg{slot} on
   \\karg{frame}."
  :causes-side-effects-p t
  :compliance-classes :write
  :tell&ask-default-body
  (untell-internal `(,(ecase slot-type
			   (:own :facet-of)
			   (:template :template-facet-of))
		     ,facet ,slot ,frame)
		   kb frame :known-true kb-local-only-p)
  :monitor-body
  (record-reference frame slot t nil kb)
  :modification-body
  (record-modification frame kb :modify slot))

(defokbcop okbc:detach-slot (frame slot &key (kb (current-kb)) (slot-type :own)
				   (kb-local-only-p nil))
  :returned-values :void
  :manual-category :slot
  :doc-string
  "Removes any explicit association between the \\karg{slot} and
   \\karg{frame}.  As a result, \\karg{slot} is not returned by
   \\kfn{get-frame-slots} at inference-level {\\tt :direct} unless there are
   slot or facet values associated with \\karg{slot} in \\karg{frame}."
  :causes-side-effects-p t
  :tell&ask-default-body
  (untell-internal `(,(ecase slot-type
			   (:own :slot-of)
			   (:template :template-slot-of))
		     ,slot ,frame)
		   kb frame :known-true kb-local-only-p)
  :compliance-classes :write
  :monitor-body
  (record-reference frame slot t nil kb)
  :modification-body
  (record-modification frame kb :modify slot))

(defokbcop okbc:enumerate-list ((list :value))
  :returned-values enumerator
  :doc-string
  "Returns an enumerator for the elements of the \\karg{list}."
  :manual-category :enumerator
  :default-body (list-to-enumerator list))

(defokbcop okbc:eql-in-kb ((arg0 :value) (arg1 :value) &key (kb (current-kb))
			   (kb-local-only-p nil))
  :manual-category :misc
  :returned-values boolean
  :doc-string
  "Returns \\true\\ iff \\karg{arg0} and \\karg{arg1}
   identify the same frame in \\karg{kb}, or are the same object (==, EQLness),
   and otherwise returns \\false.
   \\karg{Arg0} and \\karg{arg1} may be any combination of objects coercible
   to frames."
  :compliance-classes :read
  :default-body
  (or (eql arg0 arg1)
      (multiple-value-bind (arg0-frame arg0-found-p)
	  (coerce-to-frame-internal arg0 kb nil kb-local-only-p)
	(if arg0-found-p
	    (or (eql arg0-frame arg1)
		(multiple-value-bind (arg1-frame arg1-found-p)
		    (coerce-to-frame-internal arg1 kb nil kb-local-only-p)
		  (if arg1-found-p
		      (eql arg0-frame arg1-frame)
		      nil)))
	    nil)))
  :monitor-body
  (progn
    (record-reference frame-1 nil t nil kb)
    (record-reference frame-2 nil t nil kb)))

(defokbcop okbc:equal-in-kb ((arg0 :value) (arg1 :value) &key (kb (current-kb))
			     (kb-local-only-p nil))
  :returned-values boolean
  :manual-category :misc
  :doc-string
  "Returns \\true\\ iff \\karg{arg0} and \\karg{arg1}
   identify the same frame in \\karg{kb}, or are the same object (==, EQLness),
   or they are strings containing the same characters (case sensitively), or
   both are lists with the same structure, and each of the elements
   recursively is true according to \\kfn{equal-in-kb}.  Returns \\false\\
   otherwise."
  :default-body
  (if (stringp arg0)
      (equal arg0 arg1)
      (if (consp arg0)
	  (if (consp arg1)
	      (and (equal-in-kb-internal (first arg0) (first arg1)
					   kb kb-local-only-p)
		   (equal-in-kb-internal (rest  arg0) (rest  arg1)
					   kb kb-local-only-p))
	      nil)
	  (eql-in-kb-internal arg0 arg1 kb kb-local-only-p)))
  :compliance-classes :read
  :monitor-body
  (progn
    (record-reference frame-1 nil t nil kb)
    (record-reference frame-2 nil t nil kb)))

(defokbcop okbc:equalp-in-kb
    ((arg0 :value) (arg1 :value) &key (kb (current-kb)) (kb-local-only-p nil))
  :returned-values boolean
  :manual-category :misc
  :doc-string
  "Returns \\true\\ iff \\karg{arg0} and \\karg{arg1}
   identify the same frame in \\karg{kb}, or are the same object (==, EQLness),
   or they are strings containing the same characters (case-insensitively), or
   both are lists with the same structure, and each of the elements
   recursively is true according to \\kfn{equalp-in-kb}.  Returns
   \\false\\ otherwise."
  :default-body
  (if (stringp arg0)
      (equalp arg0 arg1)
      (if (consp arg0)
	  (if (consp arg1)
	      (and (equalp-in-kb-internal (first arg0) (first arg1)
					   kb kb-local-only-p)
		   (equalp-in-kb-internal (rest  arg0) (rest  arg1)
					   kb kb-local-only-p))
	      nil)
	  (eql-in-kb-internal arg0 arg1 kb kb-local-only-p)))
  :compliance-classes :read
  :monitor-body
  (progn
    (record-reference frame-1 nil t nil kb)
    (record-reference frame-2 nil t nil kb)))


;------------------------------------------------------------------------------


(defokbcop okbc:establish-connection ((connection-type :value) &key initargs)
  :returned-values connection
  :manual-category :connection
  :doc-string
  "Establishes and returns a connection of type \\karg{connection-type}.
   \\karg{Initargs} are initialization arguments for the connection if one
   is created, are used to initialize the connection in a manner
   specific to the connection type, and are documented with the definition
   of the connection type itself.  No guarantee is made that the connection
   will be newly created.  An existing, open connection with the same
   initializations may be returned.

   For example, to initialize some form of network connection, the value of
   \\karg{initargs} might be a property list of the form
   \\verb|(:host \"my-host\" :port 1234 :username \"joe\")|.

   Although the format of \\karg{initargs} is implementation-specific, OKBC
   nevertheless mandates a set of standard names for commonly used
   initializations.
   \\begin{itemize}
   \\item [{\\tt HOST}] -- A string naming the host on which the server is
                          to be found
   \\item [{\\tt PORT}] -- An integer indicating a TCP/IP port on which the
                          server is to be found
   \\item [{\\tt USERNAME}] -- A string for the login name of the user on
                              the OKBC server
   \\item [{\\tt PASSWORD}] -- The password of the user on the server
   \\end{itemize}

   Establishing a local connection requires no initialization arguments and
   can be done more conveniently using \\kfn{local-connection}."
  :compliance-classes :read)

(defmacro find-connection (key)
  "Given a key that describes a connection derived by calling
   <code>find-connection-key</code>, identifies the <code>connection</code>
   for that key."
  `(gethash ,key *existing-connections*))

(defmethod establish-connection-internal ((connection-type symbol) initargs)
  (let ((class (find-class connection-type)))
    (establish-connection-internal class initargs)))

(defmethod establish-connection-internal
    ((connection-type clos::standard-class) initargs)
  (let ((kb-type (class-prototype-safe connection-type)))
    (let ((key (apply 'find-connection-key kb-type initargs)))
      (or (find-connection key)
	  (let ((instance (apply 'make-instance connection-type initargs)))
	    (setf (find-connection key) instance)
	    instance)))))


;------------------------------------------------------------------------------


(defokbcop okbc:expunge-kb ((kb-locator :value) &key (kb-type nil)
			    (connection (local-connection)) (error-p t))
  :returned-values :void
  :manual-category :kb
  :doc-string
  "Given a \\karg{kb-locator}, removes the KB identified by that locator
   and any backup copies of it from permanent storage.  Returns no values.
   Any currently open KB identified by the locator will be unaffected,
   and may be saved to other locations using \\kfn{save-kb-as}.  If
   \\karg{error-p} is \\false, \\kfn{expunge-kb} catches errors that
   occur, and attempts to continue with the deletion process."
  :compliance-classes (:write :kb)
  :causes-side-effects-p t)


(defokbcop okbc:facet-has-value-p
    (frame slot facet &key (kb (current-kb))
	   (inference-level :taxonomic)
	   (slot-type :own) (value-selector :either)
	   (kb-local-only-p nil))
  :returned-values (boolean exact-p)
  :manual-category :facet
  :doc-string
  "Returns \\true\\ iff the specified facet has a value for the specified slot
   and frame, and otherwise returns \\false."
  :standard-default-body
  (multiple-value-bind (values exact-p)
      (get-facet-values-internal
       frame slot facet kb inference-level slot-type 1 value-selector
       kb-local-only-p)
    (values (not (null values)) exact-p))
  :tell&ask-default-body
  (multiple-value-bind (res exact-p)
	     (ask-internal
	      (ecase slot-type
		(:own `(,facet ,slot ,frame ?value))
		(:template `(:template-facet-value
			     ,facet ,slot ,frame ?value)))
	      kb t inference-level 1
	      t nil (timeout-for-tell&ask-defaults kb) value-selector
	      kb-local-only-p)
	   (values (not (null res)) exact-p))
  :monitor-body
  (record-reference frame slot t nil kb))


(defokbcop okbc:facet-p (thing &key (kb (current-kb)) (kb-local-only-p nil))
  :returned-values boolean
  :manual-category :facet
  :doc-string
  "Returns \\true\\ iff \\karg{thing} is a facet, and \\false\\ otherwise."
  :compliance-classes (:read :facets)
  :tell&ask-default-body
  (first (ask-internal `(:facet ,thing) kb t
		       (inference-level-for-tell&ask-defaults kb) 1
		       t nil (timeout-for-tell&ask-defaults kb)
		       :known-true kb-local-only-p))
  :monitor-body
  (record-reference frame slot t nil kb))

(defokbcop okbc:fetch (enumerator &key (number-of-values :all))
  :returned-values list-of-values
  :doc-string
  "Returns a \\karg{list-of-values} of at most
   \\karg{number-of-values} values remaining in the enumerator.  If the
   enumerator was exhausted before the call,
   an \\kcond{enumerator-exhausted} error will be signaled.  Note that unlike
   other operations taking a \\karg{number-of-values} argument, this operation
   does not return a \\karg{more-status} value."
  :manual-category :enumerator
  :default-body (enumerator-fetch enumerator number-of-values))


(defokbcop okbc:find-kb ((name-or-kb-or-kb-locator :value)
			 &key (connection (local-connection)))
  :returned-values kb-or-false
  :manual-category :kb
  :doc-string
  "Returns the first KB that can be found matching
   \\karg{name-or-kb-or-kb-locator}.
   If the argument is a KB, that KB is returned.  If no matching KB can be
   found, \\karg{kb-or-false} is \\false."
  :default-body
  (default-find-kb name-or-kb-or-kb-locator connection))

(defun default-find-kb
    (name-or-kb-or-kb-locator connection
			      &optional (inference-level :taxonomic))
  (typecase name-or-kb-or-kb-locator
    (kb name-or-kb-or-kb-locator)
    (structure-kb name-or-kb-or-kb-locator)
    (otherwise (or (and (eq '$meta-kb$ name-or-kb-or-kb-locator)
			;; Optimisation.  There is only
			;; ever one of these.
			(meta-kb-internal (local-connection)))
		   (and ;; bwm, hack to fix this temporarily.
			;; JPR: this is ok to keep.  Shouldn't do any harm.
			(not (eq name-or-kb-or-kb-locator :locator))
			(find name-or-kb-or-kb-locator
			 (get-kbs-internal connection)
			 :test #'eq :key #'name))
		   (and (instance-of-p-internal
			 name-or-kb-or-kb-locator :kb-locator
			 (meta-kb-internal (local-connection))
			 inference-level nil)
			(first (get-frames-with-slot-value-internal
				:locator name-or-kb-or-kb-locator
				(meta-kb-internal (local-connection))
				inference-level :own :known-true nil)))))))

(defokbcop okbc:find-kb-locator (thing &key (kb-type nil)
				       (connection (local-connection)))
  :returned-values kb-locator
  :manual-category :kb
  :doc-string
  "Returns the \\karg{kb-locator} associated with \\karg{thing} if such
   a kb-locator exists for a KB of type \\karg{kb-type}, and \\false\\
   otherwise.

   Always returns a kb-locator if \\karg{thing} is a KB.  Implementations
   are encouraged to accept other values for \\karg{thing} such as a pathname
   that identifies the location of the KB to the system.  Such usage is
   convenient, but is not portable.  It is not portable for an OKBC application
   to use anything other than a KB locator, or a KB for this argument."
  :compliance-classes :read)

(defokbcop okbc:find-kb-of-type
    ((name-or-kb :value) &key (kb-type nil) (connection (local-connection)))
  :returned-values kb-or-false
  :manual-category :kb
  :doc-string
  "If \\karg{name-or-kb} is the name of a KB of type \\karg{kb-type} (or a
   subtype of \\karg{kb-type}) that is
   currently known to the system through the \\karg{connection},
   \\kfn{find-kb-of-type} returns the KB.  If no such KB can be found,
   \\karg{kb-or-false} is \\false."
  :default-body
  (etypecase name-or-kb
    ((or kb structure-kb)
     (if (typep name-or-kb (type-of kb-type))
         name-or-kb
         (find-kb-of-type-internal
          (name name-or-kb) kb-type connection)))
    ((or symbol quasi-symbol)
     (or (find name-or-kb (get-kbs-of-type-internal kb-type connection)
	       :test #'eq :key #'name)
	 nil))
    (string
     (or (find name-or-kb (get-kbs-of-type-internal kb-type connection)
	       :test #'string= :key #'name)
	 nil)))
  :arguments-to-kb-specialize (kb-type))

(defokbcop okbc:follow-slot-chain (frame (slot-chain (:slot))
					 &key (kb (current-kb))
					 (union-multiple-values t)
					 (inference-level :taxonomic)
					 (value-selector :either)
					 (kb-local-only-p nil))
  :returned-values values
  :manual-category :slot
  :doc-string
  "Allows a program to traverse a chain of slot references,
   gathering own slot values.  For example, imagine that we wish to determine
   the sisters of the father of the mother of John.  The following two calls
   accomplish this goal:
   \\begin{verbatim}
   (follow-slot-chain 'john '(mother father sisters))
	
   (get-slot-values
      (get-slot-value
        (get-slot-value 'john 'mother)
        'father)
      'sisters)
   \\end{verbatim}
   This operation is complicated by the fact that slots can have multiple
   values.  For example, imagine that John has two mothers---adopted and
   biological.  If {\\tt union-multiple-values} is \\false\\ and a slot
   has more than one value, a \\kcond{cardinality-violation} error is signaled;
   if \\true, then the slot chain becomes a tree, and the union of
   all values found at the leaves of the tree is returned."
  :default-body
  (if (null slot-chain) 
      (if union-multiple-values (list frame) frame)
      (let ((slot-chain (if (and (symbolp (first slot-chain))
				 (string-equal (first slot-chain) "LISTOF"))
			    (rest slot-chain)
			    slot-chain)))
	(let ((values (get-slot-values-internal frame (car slot-chain) kb
						inference-level
						:own :all value-selector
						kb-local-only-p)))
	  (if (rest slot-chain)
	      (cond ((= (length values) 1)
		     (follow-slot-chain-internal (coerce-to-frame-internal 
						  (first values) kb t
						  kb-local-only-p)
						 (cdr slot-chain) 
						 kb union-multiple-values
						 inference-level value-selector
						 kb-local-only-p))
		    ((and (> (length values) 1) union-multiple-values)
		     (remove-duplicates
		      (loop for value in values
			    append
			    (follow-slot-chain-internal
			     (coerce-to-frame-internal
			      value kb t kb-local-only-p)
			     (cdr slot-chain) kb t
			     inference-level 
			     value-selector
			     kb-local-only-p))))
		    ((> (length values) 1)
		     (error
		      'cardinality-violation
		      :frame frame :slot (first slot-chain)
		      :kb kb
		      :error-message
		      (format nil "Frame ~A has too many values for slot ~A"
			frame (car slot-chain))))
		    (t (error 'cardinality-violation
			      :frame frame :slot (first slot-chain)
			      :kb kb
			      :error-message
			      (format nil "Frame ~A has no values for slot ~A"
				frame (car slot-chain)))))
	      (if union-multiple-values
		  values
		  (if (rest values)
		      (error 'cardinality-violation
			     :frame frame :slot (first slot-chain)
			     :kb kb
			     :error-message
			     (format
			      nil "Frame ~A has too many values for slot ~A"
			       frame (car slot-chain)))
		      (first values))))))))



(defokbcop okbc:frame-has-slot-p
    (frame slot &key (kb (current-kb))
	   (inference-level :taxonomic) (slot-type :own)
	   (kb-local-only-p nil))
  :returned-values boolean
  :manual-category :slot
  :doc-string
  "Returns \\true\\ iff \\karg{slot} is a slot in \\karg{frame},
   otherwise returns \\false."
  :standard-default-body
  (member slot (get-frame-slots-internal frame kb inference-level
					 slot-type kb-local-only-p))
  :tell&ask-default-body
  (first (ask-internal (ecase slot-type
			 (:own `(:slot-of ,slot ,frame))
			 (:template `(:template-slot-of ,slot ,frame)))
		       kb t
		       inference-level 1
		       t nil (timeout-for-tell&ask-defaults kb)
		       :known-true kb-local-only-p))
  :monitor-body (record-reference frame slot t nil kb))

(defokbcop okbc:frame-in-kb-p (thing
			       &key (kb (current-kb)) (kb-local-only-p nil))
  :returned-values boolean
  :manual-category :frame
  :doc-string
  "Returns \\true\\ when \\karg{thing} is both coercible to
   a frame, and that frame is known to be resident in \\karg{kb}, and otherwise
   returns \\false.  See \\kfn{get-frame-in-kb}."
  :default-body
  (multiple-value-bind (a b)
		       (get-frame-in-kb-internal thing kb nil kb-local-only-p)
		       (declare (ignore a))
    b)
  :monitor-body
  (record-reference thing nil t nil kb) )


(defokbcop okbc:free (enumerator)
  :returned-values :void
  :doc-string
  "Indicates that the \\karg{enumerator} will no longer be used.  The
   \\karg{enumerator} and any cache of unseen values may be thrown away.
   After calling \\kfn{free}, it is an error to provide \\karg{enumerator}
   as an argument to any operation, and if this is done, an
   \\kcond{object-freed} error should be signaled.  It is especially important
   to call \\kfn{free} in a network setting when a program has finished
   with the enumerator and its values have not been exhausted, so that
   the server can reclaim space allocated to the enumerator.
   Returns no values."
  :manual-category :enumerator
  :default-body (enumerator-free enumerator))

(defokbcop okbc:frs-independent-frame-handle
    (frame &key (kb (current-kb)) (kb-local-only-p nil))
  :returned-values frame-handle
  :manual-category :misc
  :doc-string
  "Given a frame, returns \\karg{frame-handle}, which is a KRS-independent
   OKBC frame handle object.  \\karg{Frame-handle} may now be used in network
   applications to refer to \\karg{frame} or in communication between KBs.
   The correspondence between \\karg{frame} and \\karg{frame-handle} is
   maintained, so that subsequent calls with the same frame will return the
   same frame-handle.

   It is not anticipated that this operation will ever be called by user
   applications, but must be used by back ends to implement
   \\kfn{decontextualize}.

   Note:  This operation is named \\kfn{frs-independent-frame-handle} for
   historical reasons.  Frame Representation Systems are now uniformly
   called Knowledge Representation Systems with the exception of in the names
   of this operator and \\kfn{frs-name}."
  :default-body
  (multiple-value-bind (real-frame found-p)
      (coerce-to-frame-internal frame kb nil kb-local-only-p)
    (let ((thing-for-handle
	   (if found-p
	       (get-frame-handle-internal real-frame kb kb-local-only-p)
	       frame)))
      (if (typep thing-for-handle 'ok-back:frame-handle)
	  thing-for-handle
	  (find-or-create-frame-handle
	   thing-for-handle thing-for-handle kb t))))
  :compliance-classes :read)

(defokbcop okbc:frs-name (&key (kb-type nil) (connection (local-connection)))
  :returned-values krs-name
  :manual-category :misc
  :doc-string
  "Returns the \\karg{krs-name} of the underlying KRS associated with the
   \\karg{kb-type}, which is accessed over \\karg{connection}.
   \\karg{Krs-name} is a string.  For example,
   given {\\tt loom-kb} as the kb-type, it might return the string
   {\\tt \"LOOM\"}.  This operation is used by user interfaces that need to
   display a printed representation of the underlying KRS for a particular
   kb-type.

   Note:  This operation is named \\kfn{frs-name} for
   historical reasons.  Frame Representation Systems are now uniformly
   called Knowledge Representation Systems with the exception of in the names
   of this operator and \\kfn{frs-independent-frame-handle}."
  :arguments-to-kb-specialize (kb-type)
  :default-body
  ((declare (ignore connection))
   (let ((string (string (type-of-name kb-type))))
     (if (and (> (length string) (length "-KB"))
	      (string-equal string "-KB" :start1
			    (- (length string) (length "-KB"))))
	 (subseq string 0 (- (length string) (length "-KB")))
	 string))))

