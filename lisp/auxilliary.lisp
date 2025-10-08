(in-package :OK-kernel)

;; This file contains add-on code for OKBC that isn't part of the
;; official spec, but that can still be quite valuable.

;; ================================================================

;; Returns T if the value-type of Slot in KB permits frames to be
;; values of that slot.


(defun frame-value-type? (slot kb &optional frame)
  (frame-value-type!
   (first (get-facet-values-internal frame slot :value-type kb
				     :all-inferable :own 1 :either nil)
	  ;;Slot :value-type is not inferred if inference-level is
	  ;;not :all-inferable.
	  )))

(defconstant +standard-okbc-datatypes+
    '(:integer :number :string :symbol :list :sexpr :sequence :boolean))

(defun frame-value-type! (value-type)
  (if (consp value-type)
      (case (first value-type)
	((:and :or)
	 (loop for type in (cdr value-type)
	     thereis
	       (frame-value-type! type)
		) )
	 (:one-of
	  nil
	  )
	 ;; If no keyword is given, assume a disjunction
	 (t
	  (loop for type in value-type
	      thereis
	       (frame-value-type! type)
		) )
	 )
    (and value-type
	 (not (find value-type +standard-okbc-datatypes+)) )
    )
  )

;; ================================================================

;; Compares the contents of two frames and determines if they are equal
;; or not.  Returns NIL if they are not.
;;
;; If Verbose? is set then *all* differences between the frames will
;; be printed; it does not stop at the first difference.

(defvar *last-frames* nil)



(defun frame-equal (f1 f2 &key
		    (kb1 (current-kb))
		    (kb2 (current-kb))
		    verbose?           ;; Print differences between the frames?
		    ignore-types?      ;; Ignore comparison of parents
		    ignore-facets?     ;; Ignore comparison of facet values
		    )

  (let (slots1 types1 types2 facets1 (equal? t)
	(name1 (get-frame-name-internal f1 kb1 nil))
	(name2 (get-frame-name-internal f2 kb2 nil))
	)
    (setq *last-frames* nil)
    
    (or (and (eq kb1 kb2)
	     (eql-in-kb-internal f1 f2 kb1 nil)
	     )
	(and (or ignore-types?
		 (if (equal-sets (setq types1 (get-instance-types-internal
					       f1 kb1 :direct :all nil))
				 (setq types2 (get-instance-types-internal
					       f2 kb2 :direct :all nil)))
		     t
		   (when verbose?
		     (print-difference name1 name2 types1 types2 :types? t)
		     (setq equal? nil)
		     t)
		     ) )

	     (let ()
	       (setq slots1 (union (get-frame-slots-internal
				    f1 kb1 :direct :all nil)
				   (get-frame-slots-internal
				    f2 kb2 :direct :all nil)))

	       (loop for slot in slots1
		     for v1 = (get-slot-values-internal
			       f1 slot kb1 :taxonomic :own :all :either nil)
		     for v2 = (get-slot-values-internal
			       f2 slot kb2 :taxonomic :own :all :either nil)
		     unless (compare-values v1 v2 slot kb1)
		     do
		     (setq equal? nil)
		     (when verbose?
		       (print-difference name1 name2 v1 v2 :slot slot)
		       )

		     until (and (not equal?) (not verbose?))
		     
		     unless ignore-facets?
		     do
		     (setq facets1 (union (get-slot-facets-internal
					   f1 slot kb1 :direct :own nil)
					  (get-slot-facets-internal
					   f2 slot kb2 :direct :own nil)))
		     (unless (diff-facets f1 f2 slot facets1 kb1 kb2 verbose?)
		       (setq equal? nil))

		     until (and (not equal?) (not verbose?)))
	       equal?)))))



(defun diff-facets (f1 f2 slot facets kb1 kb2 verbose?)
  (let ((match? t))
    (loop for facet in facets
	  for fv1 = (get-facet-values-internal
		     f1 slot facet kb1 :taxonomic :own :all :either nil)
	  for fv2 = (get-facet-values-internal
		     f2 slot facet kb2 :taxonomic :own :all :either nil)
	  unless (compare-values fv1 fv2 nil nil :set)
	  do
	  (setq match? nil)
	  (when verbose?
	    (print-difference f1 f2 fv1 fv2
			      :slot slot :facet facet))
	  when (and (not match?) (not verbose?))
	  return nil)
    match?))


(defun compare-values (v1 v2 slot kb &optional
		       (collection-type
			(or (get-slot-value-internal
			     slot :slot-collection-type kb :taxonomic :own
			     :either nil)
			    :set)))
  (case collection-type
    (:set (equal-sets v1 v2))
    (:list (equal v1 v2))
    (:multiset
     ;; Make sure the number of occurrences of each element in the
     ;; two multisets is the same in both multisets.
     (let ((set (union v1 v2 :test #'equal)))
       (loop for x in set
	     always
	     (eql (loop for y in v1 count (equal x y))
		  (loop for y in v2 count (equal x y))))))))


(defun equal-sets (x y)
  (let ((xlen (length x)))
    (and (eql xlen (length y))
	 (eql xlen (length (intersection x y :test #'equal))))))


(defun print-difference (frame1 frame2 data1 data2
			 &key
			 (kb (current-kb))
			 types? slot facet value label)
  (declare (ignore value label))
  (unless (and (eq frame1 (first *last-frames*))
	       (eq frame2 (second *last-frames*)) )
    (setq *last-frames* (list frame1 frame2))
    (format t "Difference for:  ~A // ~A~%~%" 
	    (get-frame-name-internal frame1 kb nil)
	    (get-frame-name-internal frame2 kb nil))
    )
  (when types?
    (format t "types~%") )
  (when slot
    (cond (facet
	   (format t "facet ~A of slot ~A~%" facet slot) )
	  (t
	   (format t "values of ~A~%" slot) )
	  ) )
  
  (format t "    ~A //~%    ~A~%" data1 data2)
  )


;; The following function is used to test the above code on the EcoCyc KB.

#|
(defun test-frame-equal (&optional verbose?)
  (let ((x 'ec:trypsyn)
	(y 'ec:trypsyn2) )
    (when (coercible-to-frame-p y)
      (delete-frame y) )

    (copy-frame x y)
    (unless (frame-equal x y :verbose? verbose?)
      (format t "Failure 1~%") )

    (put-slot-value y 'ec:pi 5)
    (when (frame-equal x y :verbose? verbose?)
      (format t "Failure 2~%") )
    (put-slot-values y 'pi nil)

    (put-facet-value y 'ec:catalyzes 'ec:comment "test facet")
    (when (frame-equal x y :verbose? verbose?)
      (format t "Failure 3~%") )
    (put-facet-values y 'ec:catalyzes 'ec:comment nil)

    (when (frame-equal x y :verbose? verbose?)
      (format t "Failure 4~%") )

    nil
    ) )
|#

;; ======================================================================


;; Copy the entire subtree of classes starting at Frame from KB
;; to New-KB.  Check for the case where some super of a class to
;; be copied does not yet exist in New-KB, in which case it is
;; copied also (as are its parents, recursively, if necessary).

(defun copy-all-subclasses (frame &key (kb (current-kb))
				 (to-kb kb) )
  (loop for sub in (get-class-subclasses-internal frame kb :direct :all nil)
      for sub-name = (get-frame-name-internal sub kb nil)
      unless (coercible-to-frame-p-internal sub-name to-kb nil)
      do
	(copy-class sub-name kb to-kb))

  (loop for sub in (get-class-subclasses-internal frame kb :direct :all nil)
      do
	(copy-all-subclasses sub :kb kb :to-kb to-kb)))


(defun copy-class (class-name kb to-kb)
  (loop for parent in (get-class-superclasses-internal
		       class-name kb :direct :all nil)
      for parent-name = (get-frame-name-internal parent kb nil)
      unless (coercible-to-frame-p-internal parent-name to-kb nil)
      do (copy-class parent-name kb to-kb))
  (copy-frame-internal class-name class-name kb to-kb t :stop nil nil))


;; ======================================================================

;; Merges selected slot values from f1 into f2, modifying f2.
;; This function does not transfer facets or annotations.
;; By default, f2 is deleted after the merge.

(defvar *sent-newline?*)


(defun merge-frames (f1 f2
		     &key
		     (kb (current-kb))
		     ;; A list of the slots that will be copied
		     (slots-to-copy (get-frame-slots-internal
				     f1 kb :direct :own nil))
		     ;; A subset of slots-to-copy that will NOT be copied
		     slots-to-ignore
		     (delete-f1? t)         ;; Delete f1 after the merge?
		     (print-changes? t)     ;; Print the changes we make?

		     ;; Controls how the values of F1.S and F2.S are
		     ;; combined.  Possible values are: :Union, :F1, :F2,
		     ;; meaning union the values, or prefer values
		     ;; from one frame or the other.  The default mode
		     ;; applies to all slots.  Example: If F2 is chosen,
		     ;; and if F1.S and F2.S both have values, then
		     ;; NO values are transferred from F1.S into F2.S.
		     (default-mode :f1)
		     ;; The following args provide finer control over
		     ;; combinations of values from specific slots by
		     ;; overriding the default mode, e.g., if the
		     ;; default mode is union, we can specify one or
		     ;; more slots in Priority-F2 for which the F2
		     ;; values are preferred rather than the union being
		     ;; taken.
		     priority-f1            ;; List of slots
		     priority-f2            ;; List of slots
		     union                  ;; List of slots
		     )
  (setq *sent-newline?* nil)
  (setq slots-to-copy (set-difference slots-to-copy slots-to-ignore))

  (loop for slot in slots-to-copy
	for v1 = (get-slot-values-internal
		  f1 slot kb :direct :own :all :either nil)
	for v2 = (get-slot-values-internal
		  f2 slot kb :direct :own :all :either nil)
	for mode = (cond ((find slot priority-f1) :f1)
			 ((find slot priority-f2) :f2)
			 ((find slot union) 'union)
			 (t default-mode) )
	do
	(ecase mode
	  (:f1
	   (when (not (ok-back:equal-in-kb-internal v1 v2  kb t))
	     (print-change print-changes? f2 slot v2 v1)
	     (put-slot-values-internal f2 slot v1 kb :own :known-true nil)
	     ) )

	  (:f2
	   (when (and v1 (not v2))
	     (print-change print-changes? f2 slot v2 v1)
	     (put-slot-values-internal f2 slot v1 kb :own :known-true nil)
	     )
	   (when (and v1 v2 (not (ok-back:equal-in-kb-internal v1 v2 kb t)) print-changes?)
	     (maybe-print-newline)
	     (format t "~A.~A: Keeping ~S (~A value is ~S)~%"
		     f2 slot
		     (if (eql 1 (length v2)) (first v2) v2)
		     f1
		     (if (eql 1 (length v1)) (first v1) v1)
		     ) )
	   )

	  (:union
	   (when v1
	     (print-change print-changes? f2 slot v2 v1 t)
	     (loop for v in v1
		   do
		   (add-slot-value-internal
		    f2 slot v kb :equal :own 
		    ;;kr96-7-17: added this keyword, to conservatively
		    ;; retain the ordering, because without it,
		    ;; the order is reversed.
		    (length (get-slot-values-internal
			     f2 slot kb :taxonomic :own :all :either nil))
		    :known-true nil))))))
  
  (when delete-f1?
    (delete-frame-internal f1 kb nil)))


(defun print-change (print-changes? f slot old new &optional add?)
  (when print-changes?
    (maybe-print-newline)

    (format t "~A.~A:  ~S  ~A  ~S~%"
	    f slot
	    (if (eql 1 (length old)) (first old) old)
	    (if add? "+" "-->")
	    (if (eql 1 (length new)) (first new) new)
	    )
    )
  )


(defun maybe-print-newline ()
    (unless *sent-newline?*
      (setq *sent-newline?* t)
      (terpri)
      )
    )

;; ===================================================================

;; This fn moves values from Old-Frame.Old-Slot to New-Frame.New-Slot .
;; New-Frame may be the same as Old-Frame, and ditto for New-Slot and
;; Old-Slot (although it would make no sense for both pairs to be
;; the same in one call).  Facets and annotations on the slot and
;; values, respectively, are also transfered.  If Delete-Old? is T
;; then the values, facets, and annotations are deleted from
;; Old-Frame.Old-Slot; else they are not altered.
;;
;; This code only works fully for Ocelot.

(defun xfer-slot-values (old-frame old-slot
			 &key
			 (new-frame old-frame)
			 (new-slot old-slot)
			 (delete-old? t)
			 (kb (current-kb)))

  (when (and (eq old-frame new-frame)
	     (eq old-slot new-slot) )
    (generic-error
     "xfer-slot-values: You probably do not want old-frame=new-frame ~
      and old-slot=new-slot"))

  (setq old-frame (coerce-to-frame-internal old-frame kb t nil)
	new-frame (coerce-to-frame-internal new-frame kb t nil)
	)

  (put-slot-values-internal
   new-frame new-slot
   (union (get-slot-values-internal new-frame new-slot kb
				    :taxonomic :own :all
				    :either nil)
	  (get-slot-values-internal old-frame old-slot kb
				    :taxonomic :own :all
				    :either nil))
   kb :own :known-true nil)

    (when delete-old?
    (put-slot-values-internal old-frame old-slot nil kb :own :known-true nil)))



;==============================================================================

(defun listener-unbound-variable-dwim-hook
    (symbol environment &optional (kb (current-kb)))
  (multiple-value-bind (frame found-p)
    (multiple-value-bind (frame found-p)
      (coerce-to-frame-internal symbol kb nil nil)
      (if found-p
	  (values frame t)
	  (let ((frames (get-frames-matching-internal
			 symbol kb nil :all nil nil)))
	    (if frames
		(if (rest frames)
		    (error 'not-unique-error
			   :pattern symbol
			   :matches frames
			   :context :all
			   :continuable t
			   :kb kb)
		    (let ((new (list symbol (first frames))))
		      (nconc environment (list new))
		      (values (first frames) t)))
		(continuable-error
		 "~S is unbound.  The known bindings are ~{~%     ~S~}"
		 symbol environment)))))
    (if found-p
	(let ((new (list symbol frame)))
	  (nconc environment (list new))
	  frame)
	(continuable-error
	 "~S is unbound.  The known bindings are ~{~%     ~S~}"
	 symbol environment))))

(defparameter *listener-trivial-eval-for-okbc-function*
  #'(lambda (form env)
      (trivial-eval-for-okbc (substitute-internals form) env)))


(defvar ok-utils:*okbc-listener-prompt* "OKBC> "
  "The prompt used by the OKBC listener.")

(defun ok-utils:okbc-listener
    (&key (kb (current-kb))
	  (purpose :user-interface)
	  (pretty-p nil)
	  (kb-local-only-p nil))
  "Runs a read-eval-print loop such that the expressions that are read in
   are in the OKBC procedure language.  The <code>purpose</code> and
   <code>pretty-p</code> arguments affect the way that the results are
   printed out.  Within the dynamic extent of the execution of the listener,
   a DWIM applies that will map unbound symbol references into any frame
   uniquely identified by that symbol.  If a match is found, the symbol
   will be bound to the symbol.  For exmaple, you will be able to say
   something like:<PRE>OKBC&gt; (get-slot-values fred age)</PRE>
   and if the symbol <code>FRED</code> is unbound then it may be bound to
   the frame <code>#&lt;Frame FRED 8387538&gt;</code>.<P>

   Unlike in normal procedure language expressions, top-level
   <code>SETQ</code>s can be performed to unbound variables, and the symbols
   <code>*</code>, <code>**</code>, <code>***</code>, and <code>****</code>
   have the normal meaning."
  (with-current-kb
      kb
    (catch :quit
      (loop with environment = (list (list 'kb kb)
				     (list '*    nil)
				     (list '**   nil)
				     (list '***  nil)
				     (list '**** nil))
	    with *allow-interpreted-global-assignments-p* = t
	    with fun = *listener-trivial-eval-for-okbc-function*
	    with *unbound-variable-eval-hook*
	    = 'listener-unbound-variable-dwim-hook
	    do
	    (catch :abort
	      (restart-case
	       (progn (format t "~&")
		      (loop for spec in (list-if-not *okbc-listener-prompt*)
			    do (case spec
				 (:kb (let ((*print-case* :capitalize))
					(format t "~A" (name (current-kb)))))
				 (otherwise (format t "~A" spec))))
		      (multiple-value-bind (form error-p)
			(ignore-errors
			  (let ((form
				 (if (typep kb 'ok-back:network-kb)
				     (read *standard-input* nil :eof)
				     (implement-with-kb-io-syntax-internal
				      #'(lambda ()
					  (read *standard-input* nil :eof))
				      kb :file nil))))
			    (if (or (equal nil form) (equal :eof form))
				(values "" t)
				(values (ok-back:coerce-to-kb-value-internal
					 (prin1-to-string form)
					 :value kb nil nil t
					 :do-not-coerce-to-frames nil)))))
			(cond (error-p
			       (if (equal "" form)
				   nil
				   (format t "~%** Read error **~%")))
			      (t (let ((results
					(multiple-value-list
					    (funcall fun form environment))))
				   (loop for result in results
					 do
					 (format t "~&~A"
					   (ok-back:value-as-string-internal
					    ;; Invoke part of the procedure
					    ;; language interpreter to
					    ;; interpret for the
					    ;; read-eval-print loop.
					    result kb purpose pretty-p
					    kb-local-only-p)))
				   (setf (second (assoc '**** environment))
					 (second (assoc '***  environment)))
				   (setf (second (assoc '***  environment))
					 (second (assoc '**   environment)))
				   (setf (second (assoc '**   environment))
					 (second (assoc '*    environment)))
				   (setf (second (assoc '*   environment))
					 (first results))
				   (setq kb (current-kb)))))))
	       (abort ()
		    :report "Abort to OKBC listener top level"
		    :interactive (lambda () (throw :abort :abort)))))))))

;==============================================================================
