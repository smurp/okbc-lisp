(in-package :OK-KERNEL)

(defmacro defdoc (sym (type) &body strings)
  "Defines a documentation method for the symbol <sym> on the documentation
   type <code>type</code>."
  (assert (not (eq type 'class)))
  #+ignore
  (let ((meth `(defmethod documentation
		((sym (eql ',sym)) &optional (type nil))
		(if (eq type ',type)
		    ,(first strings)
		    (call-next-method)))))
    meth)
  (let ((body `(progn (setf (documentation ',sym ',type) ,(first strings))
		',sym)))
    #+Harlequin-Common-Lisp `(eval-when (compile load eval) ,body)
    #-Harlequin-Common-Lisp body))

(defmacro %pathname-being-loaded ()
  "The symbol naming the pathname of the file currently being loaded. 
   This depends on Lisp-vendor-specific hooks."
  #+TI ''sys::fdefine-file-pathname
  #+LUCID ''lcl::*source-pathname*
  #+ALLEGRO ''excl::*source-pathname*
  #+MCL ''ccl::*loading-file-source-file*
  #-(or ti lucid allegro mcl)
  (error "Implementation needs source file recording hook."))

(defmacro defdocmethod (&rest args)
  "Defines a documentation method."
  (let ((meth `(defmethod ,@args)))
    meth))

#+Lucid
(eval-when (compile load eval)
  (when (loop for p in system:*patch-history*
	      thereis (equal "generic-function-documentation"
			     (lucid::patch-file p)))
    (pushnew :generic-function-doc-string-patch-loaded *features*)))

(defmacro ok-utils:defokbcgeneric (name (&rest args) &body options)
  "The way to define defgeneric forms in the OKBC implementation."
  #+(or (not Lucid)
	generic-function-doc-string-patch-loaded)
  `(defgeneric ,name (,@args) ,@options)
  ;; Code around a Lucid bug that blows away defgeneric doc strings in
  ;; compiled files.
  #+(and Lucid (not generic-function-doc-string-patch-loaded))
  (let ((doc nil)
	(filtered-opts nil))
    (loop for opt in options
	  do (if (or (not (consp opt))
		     (not (eq :documentation (first opt))))
		 (push opt filtered-opts)
		 (setq doc (second opt))))
    (if doc
	`(progn
	  (defgeneric ,name (,@args) ,@filtered-opts)
	  ,@(if doc `((defdoc ,name (function) ,doc)) nil)
	  #',name)
	;; Just a bit neater.
	`(defgeneric ,name (,@args) ,@options))))

#+(and Lucid (not lcl5.0))
(eval-when (compile load eval)
  (setf (macro-function 'define-compiler-macro)
	(macro-function 'def-compiler-macro)))

(defvar *advice* nil)
(defvar *all-files-defining-okbcops* nil)
(defvar *all-okbcops* nil)
;; Used in substitute-internals
(defvar *all-okbcops-ht* (make-hash-table :test #'equal))
(defun add-okbcop (op)
  (when (not (gethash (symbol-name op) *all-okbcops-ht*))
    (push op *all-okbcops*)
    (setf (gethash (symbol-name op) *all-okbcops-ht*) op)))

(defvar *acceptable-okbcops-for-call-procedure*
  (make-hash-table :test #'eq))
(defvar *all-okbc-classes-to-finalize* nil)
(defvar *ok-cache-package* (find-package :ok-cache)
  "A variable bound to the OK-CACHE package.")
(defvar ok-back:*okbc-package* (find-package :okbc)
  "A variable bound to the OKBC package.")
(defvar ok-back:*keyword-package* (find-package :keyword)
  "A variable bound to the keyword package.")
(defvar ok-back:*abstract-kb-class-names*
  '(ok-back:kb
    ok-back:standard-defaults-kb
    ok-back:tell&ask-defaults-kb
    ok-back:okbc-forwarding-mixin
    ok-back:okbc-side-effects-cause-error-mixin
    ok-back:handle-number-of-values-mixin
    ok-back:default-inheritance-mixin
    ok-back:caching-mixin
    ok-back:file-mixin
    ;; Defstruct kb classes
    ok-back:structure-kb
    ok-back:tell&ask-defaults-structure-kb
    ok-back:caching-structure-kb
    ok-back:default-inheritance-structure-kb
    ok-back:file-structure-kb
    ok-back:file-tell&ask-defaults-structure-kb)
  "A list of OKBC KB classes and mixins that are known to be abstract.  Nobody
   Should ever instantiate these.  This list is used by the get-kbs-of-type
   to make sure that the right KBs are found.")
;; Note:  No global binding.  We bind in cache wrappers
(defvar *ok-to-cache-p*)
(defvar ok-cache:*ephemeral-cache*)
(defparameter ok-cache:*allow-okbc-caching-p* t
  "A global flag that allows one to disable caching in caching-mixin
   for debugging purposes.")
(defvar *inside-network-coercion-p* nil)
(defvar *network-okbc-client-p* nil)
(defvar *inside-okbc-server-p* nil)
(defvar *current-connection* nil)

(defparameter *legal-literal-slot-values-alist*
  '((inference-level t :direct :taxonomic :all-inferable)
    (slot-type t :all :own :template)
    (missing-frame-action t :allocate :stop :abort :continue)
    (from-context t :frame :slot :facet :value)
    (target-context t :frame :slot :facet :class :individual :value)
    (kb-local-only-p t t nil)
    (number-of-values t :all (function test-for-positive-fixnum))
    (test t :eql :equal :equalp (function test-for-procedure))
    (selector (okbc:get-kb-classes
	       okbc:enumerate-kb-classes
	       okbc:get-kb-individuals
	       okbc:enumerate-kb-individuals
	       okbc:get-kb-slots
	       okbc:enumerate-kb-slots
	       okbc:get-kb-facets
	       okbc:enumerate-kb-facets)
     :all :frames :system-default)
    (selector (okbc:get-kb-roots
	       okbc:enumerate-kb-roots)
     :all :user)
    (selector (okbc:get-frames-matching
	       okbc:enumerate-frames-matching)
     :all :facet :slot :class :individual)
    (value-selector (okbc:put-slot-values 
		     okbc:put-slot-value
		     okbc:attach-slot
		     okbc:detach-slot
		     okbc:add-slot-value
		     okbc:remove-slot-value
		     okbc:replace-slot-value
		     okbc:put-facet-values 
		     okbc:put-facet-value
		     okbc:add-facet-value
		     okbc:remove-facet-value
		     okbc:replace-facet-value)
		    :known-true :default-only)
    (value-selector t :either :known-true :default-only)))

(defun test-for-positive-fixnum (arg-name arg-in-code)
  (declare (ignore arg-name))
  (and (#-Allegro fixnump #+allegro excl:fixnump arg-in-code)
       (>= arg-in-code 0)))

(defun test-for-procedure (arg-name arg-in-code)
  (declare (ignore arg-name))
  (if (and (consp arg-in-code) (eq (first arg-in-code) 'function))
      (values nil t)
      (values t nil)))

(defun pathname-in-temp-directory ()
  #+Lucid "/tmp/temp-okbc-lucid.tex"
  #+Allegro
  (progn #+microsoft-32 "c:/tmp/temp-okbc-allegro.tex"
	 #-microsoft-32 "/tmp/temp-okbc-allegro.tex")
  #+Harlequin-Common-Lisp "/tmp/temp-okbc-hcl.tex"
  #-(or Allegro Lucid Harlequin-Common-Lisp)
  "/tmp/temp-okbc-other.tex")
    
(eval-when (compile load eval)

  (defvar user::*detex-program* nil)

  (defun find-detex-in-which-response (stream)
    (loop for line = (read-line stream nil :eof)
	  when (eq line :eof) return nil
	  when (and (not (search "Command not found" line
				 :test #'char-equal))
		    (search "detex" line :test #'char-equal)
		    (not (search "no detex" line :test #'char-equal))
		    (not (search "which" line :test #'char-equal)))
	  return (setq user::*detex-program* line))
    user::*detex-program*)

  #+Lucid
  (ignore-errors
   (or (progn
	 (with-open-stream
	     (stream (ignore-errors
		      (run-program "which" :arguments (list "detex")
				   :output :stream :wait nil)))
	   (when stream (find-detex-in-which-response stream)))
	 user::*detex-program*)
       (warn "Cannot find detex program!")))

  #+Harlequin-Common-Lisp
  (progn #+Win32
	 (setq user::*detex-program* nil)
	 #-Win32
	 (ignore-errors
	  (or (progn
		(with-input-from-string
		    (stream (with-output-to-string (str)
			      (ignore-errors
			       (system::call-system-showing-output
				"which detex" :output-stream str))))
		  (when stream (find-detex-in-which-response stream)))
		user::*detex-program*)
	      (warn "Cannot find detex program!"))))

  ;; This is the version from David Gadbois hacked a bit by Rice.
  ;; Goldberg 1/99 Added conditional for windows to set detex to nil
  #+Allegro
  (progn #+microsoft-32
	 (setq user::*detex-program* nil)
	 #-microsoft-32
	 (let (stream error-output process-id)
	   (declare (ignore error-output))
	   (unwind-protect
		(progn
		  (multiple-value-setq (stream error-output process-id)
		    (excl:run-shell-command  "which detex" 
					     :output :stream :wait nil))
		  (find-detex-in-which-response stream))
	     (when (streamp stream) (close stream))
	     (when (numberp process-id) (sys:os-wait nil process-id)))
	   (when (not user::*detex-program*)
	     (warn "Cannot find detex program!"))
	   user::*detex-program*))


  #-(or Lucid Allegro Harlequin-Common-Lisp)
  (cerror
   "Go ahead, anyway"
   "!!!! Need to implement a way to find out whether detex exists or not.")

  (defun detex (string)
    (if user::*detex-program*
	#+(or Lucid Allegro Harlequin-Common-Lisp)
	;; Use different paths so that we can compile/load for different Lisp
	;; implementations at the same time.
	(let ((temp-path #+Lucid "/tmp/temp-okbc-lucid.tex"
			 #+Allegro
			 (progn #+microsoft-32 "c:/tmp/temp-okbc-allegro.tex"
				#-microsoft-32 "/tmp/temp-okbc-allegro.tex")
			 #+Harlequin-Common-Lisp "/tmp/temp-okbc-hcl.tex"
			 #-(or Allegro Lucid Harlequin-Common-Lisp)
			 "/tmp/temp-okbc-other.tex"))
	  (unwind-protect
	       ;; This clause from David Gadbois
	       (progn
		 (with-open-file (stream temp-path
				   :direction :output
				   :if-does-not-exist :create
				   :if-exists :new-version)
		   (format stream "\\begin{document}~%")
		   (with-input-from-string (str string)
		     (loop for line = (read-line str nil :eof)
			   until (eq line :eof)
			   do (princ (string-trim '(#\space #\tab) line)
				     stream)
			   (terpri stream)))
		   (format stream "~%\\end{document}"))
		 (flet ((get-output (str)
			  (let ((result ""))
			    (loop for line = (read-line str nil :eof)
				  until (eq line :eof)
				  do (setq result
					   (concatenate 'string result line
							(string #\newline))))
			    (string-trim '(#\space #\tab #\newline #\return)
					 result))))
		   (cond ((probe-file temp-path)
			  #+Allegro
			  (let (stream error-output process-id)
			    (declare (ignore error-output))
			    (unwind-protect
				 (progn
				   (multiple-value-setq
				       (stream error-output process-id)
				     (excl:run-shell-command 
				      ;; It doesn't work to use the vector
				      ;; trick.
				      (format nil
				       "~A ~A" user::*detex-program* temp-path)
				      :output :stream :wait nil))
				   (get-output stream))
			      (when (streamp stream)
				(close stream))
			      (when (numberp process-id)
				(sys:os-wait nil process-id))))		  
			  #+Lucid
			  (with-open-stream
			      (str #+Lucid
				   (run-program "detex"
						:arguments (list temp-path)
						:output :stream :wait nil))
			    (get-output str))
			  #+Harlequin-Common-Lisp
			  (with-input-from-string
			      (str (with-output-to-string (str)
				     (ignore-errors
				      (system::call-system-showing-output
				       (format nil "detex ~A" temp-path)
				       :output-stream str))))
			    (get-output str)))
			 (t (warn "Consistency error - cannot find ~A file."
				  temp-path)
			    string))))
	    ;; This is the old version that didn't for for Cycorp
		 #+ignore
	    (progn (with-open-file (stream temp-path :direction :output)
		     (format stream "\\begin{document}~%")
		     (with-input-from-string (str string)
		       (loop for line = (read-line str nil :eof)
			     until (eq line :eof)
			     do (princ (string-trim '(#\space #\tab) line)
				       stream)
			     (terpri stream)))
		     (format stream "~%\\end{document}"))
		   (with-open-stream
		       (str #+Lucid
			    (run-program "detex"
					 :arguments (list temp-path)
					 :output :stream :wait nil)
			    #+Allegro
			    (excl:run-shell-command "detex /tmp/temp.tex"
						    :output :stream :wait nil))
		     (let ((result ""))
		       (loop for line = (read-line str nil :eof)
			     until (eq line :eof)
			     do (setq result (concatenate 'string result line
							  (string #\newline))))
		       (string-trim '(#\space #\tab #\newline #\return)
				    result))))
	    (when (probe-file temp-path)
	      (or (ignore-errors (delete-file temp-path))
		  (warn "Cannot delete ~A file." temp-path)))))
	#-(or Lucid Allegro Harlequin-Common-Lisp)
	(progn (warn "!!!! Need to implement call to detex.") string)
	string))

  (defvar *all-okbcfuns* nil)
  (defvar *all-okbc-conditions* nil)

  (defun ok-utils:first-if-list (x)
    "If <code>x</code> is a list then it returns the first element of the list,
   otherwise it just returns <code>x</code>."
    (if (consp x) (first x) x))

  (defun ok-utils:list-if-not (x)
    "If <code>x</code> is a list then it just returns it, otherwise it wraps
   it in a list."
    (if (listp x) x (list x)))

  (defun record-okbc-fun (name args returned-values)
    (setq *all-okbcfuns*
	  (cons (list name args (if (eq returned-values :void)
				    nil
				    (list-if-not returned-values)))
		(remove (assoc name *all-okbcfuns*)
			*all-okbcfuns*))))

  (defun ensure-api-symbol-ok (name package)
    (when (not (and (eq (symbol-package name) (find-package package))
		    (multiple-value-bind (s type)
		      (find-symbol (symbol-name name) package)
		      (declare (ignore s))
		      (eq :external type))))
      (warn "~S Must be an external symbol homed in the ~A package!"
	    name package)))

  (defokbcgeneric ok-cache:register-side-effect (kb &optional arg)
    (:documentation "Notifies the <code>kb</code> that a side effect has been
   performed.  This might result in caches being flushed.  <code>Arg</code>
   is some key that might indicate the cause or nature of the side-effect.
   Certain back ends might use this argument to communicate the need for
   specific cache flushing behavior.<P>

   The most common use of this generic function is in kbs that are
   instances of <code>caching-mixin</code> or <code>caching-structure-kb</code>,
   and for which the <code>caching-policy</code> is <code>:agressive</code>."))

  (defokbcgeneric abstract-kb-class-name-from-kb (kb)
    (:documentation "Given a <code>kb</code> instance returns the abstract
   class name for it.  For each KB class that the back end author defines,
   an abstract KB class must be defined, named in the ok-back package, so that
   the network transport layer can communicate the right abstract notion of
   the KB to clients.  For a KB called <code>foo</code>, an abstract KB class
   called <code>ok-back::abstract-foo-kb</code> should be defined, and should
   be the left-most mixin to <code>foo</code>.  This generic function
   establishes the mapping between the KB and the abstract KB class.<P>

   Back end authors should be careful to define fill in this protocol, since
   a KB class can be made \"compliant\" by satisfying all of the required
   official OKBC API requirements, but without a suitable mapping between
   concrete and abstract KB classes, the KB will not show up as an available
   kb-type over network connections.  See also
   <code>concrete-kb-class-from-abstract-kb-class-name</code>."))

  (defokbcgeneric concrete-kb-class-from-abstract-kb-class-name (name)
    (:documentation "This is the inverse operation of
   <code>abstract-kb-class-name-from-kb</code> and maps an abstract KB name
   to a concrete KB class name, for example, <code>abstract-foo-kb</code>
   would be mapped to <code>foo</code>.<P>

   Back end authors should be careful to <code>EQL</code> specialize this
   generic function for their KB classes, otherwise the network layer will not
   hook up properly."))

  (defokbcgeneric ok-back:decontextualize-aux (value from-context kb)
    (:documentation "A useful generic function that implements most of the hard
   part of decontextualization for the back end author.  To use this
   function, the back end author should specialize
   <code>decontextualize-internal</code> as follows:<PRE>
   (defmethod decontextualize-internal
      ((value t) (from-context t) (kb foo-kb))
     (decontextualize-aux value from-context kb))</PRE>
   The back end author will then need to supply <code>decontextualize-aux</code>
   methods only for the specific objects that will need to be decontextualized.
   For example, if frames are implemented in the <code>foo-kb</code> class as
   instances of the class <code>frame</code>, decontextualization can be
   handled as follows:<PRE>
   (defmethod ok-back:decontextualize-aux
              ((value frame) (from-context t) (kb foo-kb))
     (ok-back:frs-independent-frame-handle-internal value kb nil))</PRE>
   Back end authors should also be careful to handle the correct
   decontextualizations for standard frames.  Thus, it may be necessary to
   write the above method as:<PRE>
   (defmethod ok-back:decontextualize-aux
              ((value frame) (from-context t) (kb foo-kb))
      (multiple-value-bind (frame? found-p)
	(coerce-to-frame-internal value kb nil nil)
	(if found-p
	    (let ((name (get-frame-name-internal frame? kb nil)))
	      (or (first (member name *okbc-standard-names*))
		  (ok-back:frs-independent-frame-handle-internal value kb nil)))
	    (ok-back:frs-independent-frame-handle-internal
              value kb nil))))</PRE>"))

  (defokbcgeneric ok-utils:kb-specializing-arguments (op)
    (:documentation "Given the front end API name for an OKBC
   operation, returns the list of argument names for that operation that
   specialize on KBs."))

  (defokbcgeneric ok-utils:causes-side-effects-p (op)
    (:documentation "A predicate on OKBC operator names that returns true if the
   operator causes side effects.  For example, this predicate is true for
   put-slot-values, and false for get-slot-values."))

  (defokbcgeneric ok-utils:internal-name-to-op-name (op)
    (:documentation "Given the back end API (-internal) name for an OKBC
   operation, returns the front end API name.  For example, given
   <code>ok-back:get-slot-values-internal</code> will return
   <code>okbc:get-slot-values</code>."))

  (defokbcgeneric ok-utils:op-name-to-internal-name (op)
    (:documentation "Given the front end API name for an OKBC
   operation, returns the back end API (-internal) name.  For example, given
   <code>okbc:get-slot-values</code> will return
   <code>ok-back:get-slot-values-internal</code>."))

  (defokbcgeneric ok-utils:okbcop-args (op)
    (:documentation "Given the front end API name for an OKBC
   operation, returns three values:
   <OL>
   <LI>the arguments to the operation,
   <LI>the values returned by the operation,
   <LI>the arguments to the back end API generic function for this operation.
   </OL>"))

  (defmacro ok-utils:defokbcfun
      (name (&rest args) (&key returned-values
			       (which-ends '(:back :front))
			       (causes-side-effects-p nil)
			       (manual-category nil))
	    doc-string
	    &body body)
    "Defines an OKBC operator as a simple function.  This is used for the
   very simple OKBC operators that cannot be specialized by back ends, such as
   <code>current-kb</code>.
   <DL>
   <DT>Returned-values<DD>names the value or values returned by the function.
   <DT>Which-ends<DD>is a list of the symbols <code>:back</code> and/or
   <code>:front</code>, which states whether this operation is to be part of the
   front end API, the back end API or both.
   <DT>Causes-side-effects-p<DD>is true is this operation causes side effects.
   <DT>Manual-category<DD>is a keyword specifying the category of operation
   as far as the manual is concerned.
   </DL>."
    (assert (stringp doc-string) () "OKBCfun ~S has no doc string!.")
    (assert (keywordp manual-category)
	    () "You must specify the manual-category")
    (ensure-api-symbol-ok name :okbc)
    `(progn (record-okbc-fun ',name ',args ',returned-values)
      (defmethod ok-utils:causes-side-effects-p ((op (eql ',name)))
       ,causes-side-effects-p)
      (setf (gethash ',name
	     *acceptable-okbcops-for-call-procedure*)
       ',name)
      (defmethod manual-category ((name (eql ',name)))
       ',manual-category)
      (defmethod raw-documentation ((name (eql ',name))) ,doc-string)
      (defmethod which-ends ((okbcop (eql ',name)))
       ',(list-if-not which-ends))
      (defun ,name (,@args) ,(detex doc-string) ,@body)))

  (defun current-source-file ()
    #+Lucid lcl::*source-pathname*
    #+ALLEGRO excl::*source-pathname*
    #+MCL ccl::*loading-file-source-file*
    #+Harlequin-Common-Lisp dspec:*source-pathname*
    #-(or Lucid Allegro MCL Harlequin-Common-Lisp)
    (generic-error "Implement me"))

  );; eval-when

(eval-when (compile load eval)
  (defun tex-doc-path ()
    (make-pathname :defaults #.(current-source-file)
		   :directory
		   '#.(append (butlast (pathname-directory
					(current-source-file)))
			      '("spec"))
		   :name "spec"
		   :type "tex")))

#+(and LUCID (not LCL4.1))
(defmacro print-unreadable-object 
	  ((object stream &key type identity) &body body)
  "Just like CLtL2 PRINT-UNREADABLE-OBJECT."
  (declare (ignore identity))
  (let ((stream-name (gensym)))
    `(let ((,stream-name ,stream))
       (format ,stream-name "#<")
       ,@(when type
	   `((format ,stream-name "~a " (symbol-name (type-of ,object)))))
       ,@body
       (format ,stream-name ">"))))

(defmacro ok-utils:okbc-assert
    (test &optional (condition-to-signal nil) &rest error-args)
  "A macro rather like the Common Lisp <code>assert</code> macro that
   performs a <code>test</code>, and will signal an OKBC error if the
   test fails.<p>

   The condition signalled is marked as being <i>non-continuable</i> in the OKBC
   sense.  A non-continuable OKBC error is an error that states that the KB
   may have been uncontinuably broken by whatever it was that caused the
   signalling of the error.</i><P>

   <code>Condition-to-signal</code> is the class of error signalled.  If this
   argument is NIL, a <code>generic-error</code> is signalled, and
   <code>error-args</code> are used as format control arguments to
   specify the error message.  If a condition name is supplied, the
   <code>error-args</code> are used to initialize the condition.
   For example,<PRE>
   (multiple-value-bind (frame found-p)
        (coerce-to-class-internal maybe-frame kb nil kb-local-only-p)
      (okbc-assert found-p not-coercible-to-frame
		   :frame frame :kb kb)
      ...)</PRE> or<PRE>   (okbc-assert (< value 42) nil
       \"The value ~S should have been less than 42\" value)</PRE>"
  (assert (or (not condition-to-signal) (symbolp condition-to-signal)))
  `(when (not ,test)
     (error ',(or condition-to-signal 'generic-error)
           ,@(if condition-to-signal
		 error-args
		 (if error-args
		     `(:error-message (format nil ,@error-args))
		     `(:error-message
		       (format nil "Assertion failed: ~S" ',test)))))))

(defmacro ok-utils:continuable-assert
    (test &optional (condition-to-signal nil) &rest error-args)
  "A macro rather like the Common Lisp <code>assert</code> macro that
   performs a <code>test</code>, and will signal an OKBC error if the
   test fails.<p>

   The condition signalled is marked as being <i>continuable</i> in the OKBC
   sense.  <i>Note: this is not the same thing as </i><code>cerror</code><i>,
   which signals a resumable Common Lisp error.  A continuable OKBC error is an
   error that guarantees that the KB has not been uncontinuably broken by 
   whatever it was that caused the signalling of the error.</i><P>

   <code>Condition-to-signal</code> is the class of error signalled.  If this
   argument is NIL, a <code>generic-error</code> is signalled, and
   <code>error-args</code> are used as format control arguments to
   specify the error message.  If a condition name is supplied, the
   <code>error-args</code> are used to initialize the condition.
   For example,<PRE>
   (multiple-value-bind (frame found-p)
        (coerce-to-class-internal maybe-frame kb nil kb-local-only-p)
      (continuable-assert found-p not-coercible-to-frame
			  :frame frame :kb kb)
      ...)</PRE>or<PRE>(continuable-assert (< value 42) nil
       \"The value ~S should have been less than 42\" value)</PRE>"
  (assert (or (not condition-to-signal) (symbolp condition-to-signal)) ()
	  "~S is not a legal condition to signal.  It must be either NIL, or ~
           the name of an OKBC condition."
	  condition-to-signal)
  `(when (not ,test)
     (error ',(or condition-to-signal 'generic-error)
             :continuable t
           ,@(if condition-to-signal
		 error-args
		 (if error-args
		     `(:error-message (format nil ,@error-args))
		     `(:error-message
		       (format nil "Assertion failed: ~S" ',test)))))))

(defun generic-error (format-string &rest args)
  "Signals a generic, non-continuable OKBC error with an error message
   specified by <code>format-string</code> and <code>args</code>."
  (error 'generic-error :error-message
	 (apply 'format nil format-string args)))

(defun continuable-error (format-string &rest args)
  "Signals a continuable <code>generic-error</code> with an error message
   constructed using the <code>format-string</code> and <code>args</code>.
   <i>Note: this is not the same thing as </i><code>cerror</code><i>,
   which signals a resumable Common Lisp error.  A continuable OKBC error is an
   error that guarantees that the KB has not been uncontinuably broken by 
   whatever it was that caused the signalling of the error.</i>"
  (error 'generic-error
	 :continuable t
	 :error-message (apply 'format nil format-string args)))

(defmacro ok-back:defokbcclass (name (&rest superclasses) (&rest slots)
				     &rest options)
  "A macro just like <code>defclass</code>, which should be used when defining
   any class that is part of the OKBC implementation.  This macro is used to
   make sure that all OKBC classes get finalized properly for implementations
   that are to be run in compilerless mode."
  #-Allegro
  `(progn (defclass ,name (,@superclasses) (,@slots)
		    ,@options)
    (pushnew ',name *all-okbc-classes-to-finalize*)
    ',name)
  ;; Code around a bug in the handling of defclass documentation.
  ;; Lucid has a similar bug in defgeneric.
  #+Allegro
  (let ((doc nil)
	(filtered-opts nil))
    (loop for opt in options
	  do (if (or (not (consp opt))
		     (not (eq :documentation (first opt))))
		 (push opt filtered-opts)
		 (setq doc (second opt))))
    (if doc
	`(progn (defclass ,name (,@superclasses) (,@slots)
			  ,@filtered-opts)
	  ,@(if doc `((defdoc ,name (type) ,doc)) nil)
	  (pushnew ',name *all-okbc-classes-to-finalize*)
	  ',name)
	;; Just a bit neater.
	`(progn (defclass ,name (,@superclasses) (,@slots)
			  ,@options)
	  (pushnew ',name *all-okbc-classes-to-finalize*)
	  ',name))))

;;; Define current-kb early in the build process because it gets inlined
;;; by the defokbcops defined in core*.lisp
;;; This obviates an eval-when.
(eval-when (compile load eval) (proclaim '(inline okbc:current-kb)))

(defvar *current-kb* nil
  "An internal variable whose value is the current KB.  This is set by
   <code>goto-kb</code>.  Back end implementors may have some reason to
   bind this, but should ideally use <code>current-kb</code> and
   <code>with-current-kb</code>.")
(defvar *current-kb-for-io-syntax* nil
  "A variable used to determine the current KB to use for the purpose of IO
   Syntax determination.  This is important because sometimes an implementation
   has a need to read, or print things with respect to a KB other than the
   <code>current-kb</code>.")
(defvar *current-purpose-for-io-syntax* nil
  "A special bound inside <code>with-kb-io-syntax</code> and similar forms
   to specify the user's selection of IO syntax purpose.  This is important
   because <code>print-object</code> methods need to be sensitive to the
   user's IO syntax purpose selection.")

(defokbcfun okbc:current-kb ()
  (:returned-values kb
   :manual-category :kb)
  "Returns the current KB.  The current KB is set using \\kfn{goto-kb}."
  *current-kb*)

(defparameter ok-back:*all-known-okbc-compliance-classes*
  '(:read
    :write
    :kb
    :network/copy
    (:facets (:facets t)))
  "A list of the different compliance classes.  Each element is either
   a keyword denoting the compliance class or a list of the form
   <code>(&lt;&lt;compliance-class-keyword&gt;&gt; &rest
   &lt;&lt;behavior-value-pairs&gt;&gt;)</code>
   where <code>&lt;&lt;behavior-value-pairs&gt;&gt;</code> are two-lists of
   behavior keywords,and the necessary values which must be present of an
   implementation for this compliance class to be meaningful.")

(defmacro ok-utils:without-scheduling (&body body)
  "An implementation-independent macro to run the <code>body</code> in an
   interrupts-deferred mode."
  #+Lucid `(with-scheduling-inhibited ,@body)
  #+EXCL  `(mp:without-scheduling ,@body)
  #+Harlequin-Common-Lisp `(mp::without-interrupts ,@body)
  #-(or EXCL Lucid Harlequin-Common-Lisp)
  (progn (cerror "Go ahead, anyway"
		 "Implement without-scheduling for this Lisp")
	 `(progn ,@body)))

(defmacro ok-utils:without-recursion-using-trie
    ((uid arg recursion-value) &body body)
  "Executes the <code>body</code> so that infinite recursions are detected
   and prevented.  <code>UID</code> is a unique identifier used to distinguish
   this without-recursion wrapper from others.  <code>Arg</code> is the
   argument used to check to see whether a cycle has been found.  If a
   cycle is found, <code>recursion-value</code> is returned.<P>

   In this formulation of without-recursion, instances of <code>arg</code> are
   kept in a <code>trie</code>, and <i>any</i> repeat call to the form will
   cause the <code>recursion-value</code> to be returned irrespective of the
   path taken to find the second occurrence of the <code>arg</code>."
  (let ((inside-sym
	 (intern (format nil "*INSIDE-WITHOUT-RECURSION-~A*" uid) 'ok-kernel))
	(visited-sym
	 (intern (format nil "*PLACES-VISITED-~A*" uid) 'ok-kernel))
	(ht-sym (gensym "HT-"))
	(key-sym (gensym "KEY-")))
    `(if (and (boundp ',inside-sym) (symbol-value ',inside-sym))
      (let ((,ht-sym (symbol-value ',visited-sym))
	    (,key-sym (ok-utils:fast-hash-key ,arg)))
	(multiple-value-bind (result found-p trie-node)
	    (get-hybrid-trie-returning-node ,key-sym ,ht-sym)
	  (if (and found-p result)
	      ,recursion-value
	      (progn
		(setf (hybrid-trie-value trie-node) t)
		,@body))))
      (let ((,inside-sym t)
	    (,visited-sym (new-root-hybrid-trie
			   :without-recursion :ephemeral)))
	(declare (special ,inside-sym ,visited-sym))
	,@body))))

(defmacro ok-utils:without-recursion-in-stack
    ((uid arg recursion-value &optional (test '#'eq)) &body body)
  "Executes the <code>body</code> so that infinite recursions are detected
   and prevented.  <code>UID</code> is a unique identifier used to distinguish
   this without-recursion wrapper from others.  <code>Arg</code> is the
   argument used to check to see whether a cycle has been found.  If a
   cycle is found, <code>recursion-value</code> is returned.  Comparison
   is performed according to <code>test</code>.<P>

   In this formulation of without-recursion, instances of <code>arg</code> are
   kept on a stack.  Repeat call to the form for a given value of
   <code>arg</code> will only be detected dynamically within a call to the
   form with the same value of <code>arg</code>."
  (let ((inside-sym
	 (intern (format nil "*INSIDE-WITHOUT-RECURSION-~A*" uid) 'ok-kernel))
	(visited-sym
	 (intern (format nil "*PLACES-VISITED-~A*" uid) 'ok-kernel)))
    `(if (and (boundp ',inside-sym) (symbol-value ',inside-sym))
         (if (member ,arg (symbol-value ',visited-sym) :test ,test)
	     ,recursion-value
	     (let ((,visited-sym (cons ,arg #-Harlequin-Common-Lisp ,visited-sym
                                       #+Harlequin-Common-Lisp (symbol-value ',visited-sym))))
	       (declare (special ,visited-sym))
	       ,@body))
         (let ((,inside-sym t)
	       (,visited-sym (list ,arg)))
	   (declare (special ,inside-sym ,visited-sym))
	   ,@body))))

;;; Test functions

(defokbcfun okbc:procedure-p (thing)
  (:returned-values boolean
   :manual-category :funspec)
  "Is \\true\\ if \\karg{thing} is a procedure, and \\false\\ otherwise."
  (okbc-procedure-p thing))

(defun ok-utils:decanonicalize-testfn (testfn kb kb-local-only-p)
  "In OKBC, the supported canonical test functions are represented by
   the keywords <code>:eql</code>, <code>:equall</code>, and
   <code>:equalp</code>.  This function takes either a canonical test function
   or an OKBC procedure and returns a Lisp function suitable for use
   as a <code>:test</code> argument to functions such as
   <code>member</code>.  For example,<PRE>
   (member frame list-of-frames
           :test (decanonicalize-testfn :eql kb kb-local-only-p))</PRE>"
  (decanonicalize-testfn-slow testfn kb kb-local-only-p))

(defun decanonicalize-testfn-slow (testfn kb kb-local-only-p)
  (case testfn
    (:eql #'(lambda (x y)
	      (or (eql x y)
		  (eql-in-kb-internal x y kb kb-local-only-p))))
    (:equal #'(lambda (x y)
		(or (equal x y)
		    (equal-in-kb-internal x y kb kb-local-only-p))))
    (:equalp #'(lambda (x y)
		 (or (equalp x y)
		     (equalp-in-kb-internal x y kb kb-local-only-p))))
    (otherwise
     (if (procedure-p testfn)
	 #'(lambda (x y) (call-procedure-internal testfn kb (list x y)))
	 (continuable-error "~S is not a legal test procedure." testfn)))))

(define-compiler-macro ok-utils:decanonicalize-testfn
    (&whole whole testfn kb kb-local-only-p)
  (case testfn
    (:eql    `#'(lambda (x y) (eql-in-kb-internal x y ,kb ,kb-local-only-p)))
    (:equal  `#'(lambda (x y) (equal-in-kb-internal x y ,kb ,kb-local-only-p)))
    (:equalp
     `#'(lambda (x y) (equalp-in-kb-internal x y ,kb ,kb-local-only-p)))
    (otherwise `(decanonicalize-testfn-slow ,@(rest whole)))))

(defmethod funcall-test ((testfn t) (x t) (y t) (kb t) (kb-local-only-p t))
  (continuable-error "~S is not a legal test procedure." testfn))

(defmethod funcall-test ((testfn (eql :eql)) x y kb kb-local-only-p)
  (eql-in-kb-internal x y kb kb-local-only-p))

(defmethod funcall-test ((testfn (eql :equal)) x y kb kb-local-only-p)
  (equal-in-kb-internal x y kb kb-local-only-p))

(defmethod funcall-test ((testfn (eql :equalp)) x y kb kb-local-only-p)
  (equalp-in-kb-internal x y kb kb-local-only-p))

(defun ok-utils:is-in-tree (x tree &key (test #'eql))
    "Is true if <code>x</code> is present in <code>tree</code> at least once
     according to the <code>test</code>."
    (is-in-tree-internal x tree test))

(defun is-in-tree-internal (x tree test)
  (or (funcall test x tree)
      (if (consp tree)
	  (or (is-in-tree-internal x (first tree) test)
	      (is-in-tree-internal x (rest tree) test))
	  nil)))

(define-compiler-macro ok-utils:is-in-tree
    (x tree &key (test #'eql))
  (cond ((or (equal test 'eq) (equal test ''eq)
	     (equal test #'eq) (equal test '#'eq))
	 `(is-in-tree-eq  ,x ,tree))
	((or (equal test 'eql) (equal test ''eql)
	     (equal test #'eql) (equal test '#'eql))
	 `(is-in-tree-eql ,x ,tree))
	((or (equal test 'equal) (equal test ''equal)
	     (equal test #'equal) (equal test '#'equal))
	 `(is-in-tree-equal ,x ,tree))
	(t `(is-in-tree-internal ,x ,tree ,test))))

(defmacro def-is-in-tree (name test)
  `(defun ,name (x tree)
    (or (,test x tree)
	(if (consp tree)
	    (loop for arg = (pop tree)
		  when (not tree) return (,name x arg)
		  when (,name x arg) return t
		  when (not tree) return nil
		  when (not (consp tree)) return (,name x tree))
	    nil))))

(def-is-in-tree is-in-tree-eq    eq)
(def-is-in-tree is-in-tree-eql   eql)
(def-is-in-tree is-in-tree-equal equal)

(defmethod class-prototype-safe ((class class))
  #+EXCL (when (not (clos::class-finalized-p class))
	   (clos:finalize-inheritance class))
  (#+(or TI Lucid EXCL Harlequin-Common-Lisp) clos:class-prototype
     #+MCL ccl::class-prototype
     #-(or mcl TI lucid excl Harlequin-Common-Lisp)
     (lambda (x)
       (declare (ignore x))
       (generic-error "Need to find the right ~
	               name for class-prototype in this implementation."))
     class))

(defmethod class-prototype-safe ((thing symbol))
  (let ((class (find-class thing nil)))
    (if class
	(class-prototype-safe class)
	nil)))

#+EXCL
(defvar *interned-structure-class-prototypes* (make-hash-table))

#+EXCL
(defmethod class-prototype-safe ((class structure-class))
  (multiple-value-bind (proto found-p)
      (gethash class *interned-structure-class-prototypes*)
    (if found-p
	proto
	(progn (when (not (clos::class-finalized-p class))
		 (clos::finalize-inheritance class))
	       (let ((proto (clos:class-prototype class)))
		 (setf (gethash class *interned-structure-class-prototypes*)
		       proto)
		 proto)))))

;-----------------------------------------------------------------
;                         defokbcop
;-----------------------------------------------------------------

(defun ok-utils:remove-keywords-and-defaults (args)
  "Given an arglist for a function possibly with lambda list keywords,
	   defaults and such returns just the list of names of args."
  (cond ((null args) nil)
	((member (first args) lambda-list-keywords)
	 (remove-keywords-and-defaults (rest args)))
	((consp (first args))
	 (cons (first (first args))
	       (remove-keywords-and-defaults (rest args))))
	(t (cons (first args) (remove-keywords-and-defaults (rest args))))))

(defun ok-utils:remove-coercion-specs (args)
  "Given an arglist for a function possibly with lambda list keywords,
   defaults and such returns the same arglist but with any coercion specs
    removed."
  (cond ((null args) nil)
	((member (first args) lambda-list-keywords) args)
	((consp (first args))
	 (cons (first (first args))
	       (remove-coercion-specs (rest args))))
	(t (cons (first args) (remove-coercion-specs (rest args))))))

(defparameter *known-coercion-types*
  '(:frame :slot :facet :value :class))

(defun get-coercion-specs (args &optional (in-keyword-portion-p nil))
  "Given an arglist with coercion specs, return the alist of arg -> coercion
	   for each non keyword arg."
  (cond ((null args) nil)
	((eq (first args) '&key) (get-coercion-specs (rest args) t))
	((member (first args) lambda-list-keywords) nil)
	((and in-keyword-portion-p (consp (first args)))
	 (get-coercion-specs (cons (first (first args)) (rest args))
			     in-keyword-portion-p))
	((consp (first args))
	 (assert (or (member (second (first args)) *known-coercion-types*)
		     (and (consp (second (first args)))
			  (member (first (second (first args)))
				  *known-coercion-types*)))
		 () "Illegal coercion type ~S" (second (first args)))
	 (cons (first args)
	       (get-coercion-specs (rest args) in-keyword-portion-p)))
	((let ((string (string (first args)))
	       (cookie "-OR-NIL"))
	   (and (> (length string) (length cookie))
		(string-equal cookie string
			      :start2 (- (length string) (length cookie)))
		(let ((res (first (get-coercion-specs
				   (list (intern (subseq string 0
							 (- (length string)
							    (length cookie)))
						 (symbol-package
						  (first args))))
				   in-keyword-portion-p))))
		  (if res
		      (cons (list (first args)
				  (intern (concatenate
					   'string (symbol-name (second res))
					   cookie)
					  :keyword))
			    (get-coercion-specs
			     (rest args) in-keyword-portion-p))
		      nil)))))
	(t (let ((match (cond ((string= (first args) :frame) :frame)
			      ((string= (first args) :slot) :slot)
			      ((string= (first args) :facet) :facet)
			      ((member (first args)
				       '(:thing :value :values :name :new-name
					 :enumerator :procedure :connection
					 :kb)
				       :test #'string=)
			       :value)
			      ((member (first args)
				       '(:class :subclass :subclasses
					 :superclass :superclasses)
				       :test #'string=)
			       :class))))
	     (assert (or in-keyword-portion-p match)
		     () "Cannot compute coercion type for ~S" (first args))
	     (cons (list (first args) (or match :value))
		   (get-coercion-specs (rest args) in-keyword-portion-p))))))

(defun supplied-p-ify (args)
  "Given an arglist returns a similar arglist only makes sure that any
	   optional (or keyword) arg also provides a supplied-p arg name."
  (cond ((null args) nil)
	((member (first args) lambda-list-keywords)
	 (cons (first args) (supplied-p-ify (rest args))))
	((consp (first args))
	 (let ((supplied-p (gensym "SUPPLIED-P-")))
	   (cons (ecase (length (first args))
		   (1 (list (first (first args)) nil supplied-p))
		   ;; PDK I added the quotation below
		   (2 (list (first (first args))
			    (LIST 'QUOTE (second (first args)))
			    supplied-p))
		   (3 (first args)))
		 (supplied-p-ify (rest args)))))
	(t (cons (first args) (supplied-p-ify (rest args))))))


(defmacro coerce-frame-arg (arg type kb kb-local-only-p)
  "Generates a list of statements to setq a list of variables
	   (args) to the result of coercing those variables to frames."
  (assert kb () "No KB supplied in argument coercion for ~S as a ~S.~%~
                 Maybe you are defining an extension OKBCop and have not ~
                 specified an :arguments-to-kb-specialize argument."
	  arg type)
  (flet ((coerce-arg-for-type (arg type)
	   (ecase type
	     (:value arg)
	     (:frame `(coerce-to-frame-internal ,arg ,kb t ,kb-local-only-p))
	     (:slot  `(coerce-to-slot-internal  ,arg ,kb t ,kb-local-only-p))
	     (:facet `(coerce-to-facet-internal ,arg ,kb t ,kb-local-only-p))
	     (:class `(coerce-to-class-internal ,arg ,kb t
		       ,kb-local-only-p)))))
    (typecase type
      (null arg)
      (cons (let ((temp (gensym)))
	      `(loop for ,temp in ,arg
		collect ,(coerce-arg-for-type temp (first type)))))
      (otherwise
       (let ((type-string (string type))
	     (cookie "-OR-NIL"))
	 (if (and (> (length type-string) (length cookie))
		  (string-equal cookie type-string
				:start2 (- (length type-string)
					   (length cookie))))
	     (let ((real-type
		    (intern (subseq type-string 0
				    (- (length type-string) (length cookie)))
			    :keyword)))
	       `(if (eq ,arg nil)
		    nil
		 ,(coerce-arg-for-type arg real-type)))
	     (coerce-arg-for-type arg type)))))))

(defun coerce-frame-args (args kb types &optional (gensym-p t))
  "Generates a list of statements to setq a list of variables
	   (args) to the result of coercing those variables to frames."
  (flet (#+ignore
	 (coerce-arg-for-type (arg type)
	   (ecase type
	     (:frame `(coerce-to-frame-internal
		       ,arg ,kb t kb-local-only-p))
	     (:value arg)
	     (:slot `(coerce-to-slot-internal
		      ,arg ,kb t kb-local-only-p))
	     (:facet `(coerce-to-facet-internal
		       ,arg ,kb t kb-local-only-p))
	     (:class `(coerce-to-class-internal
		       ,arg ,kb t kb-local-only-p)))))
    (loop for arg in args
	  for type in types
	  for coerced =
	  (if (consp type)
	      (let ((temp (if gensym-p (gensym) (gentemp "L" :ok-kernel))))
		`(loop for ,temp in ,arg
		  collect (coerce-frame-arg ,temp ,(first type) ,kb
			   kb-local-only-p)))
	      `(coerce-frame-arg ,arg ,type ,kb kb-local-only-p))
	  when (not (eq arg coerced))
	  collect (list 'setq arg coerced))))

(defvar *trace-okbc-compiler-macro-expansions-p* nil)

(defun generate-compiler-macro-inner-form (internal-name supplied-p-spec
							 args-with-coercions
							 allow-coercions-p)
  (let ((all-args (remove-if
		   #'(lambda (x) (member x lambda-list-keywords :test #'eq))
		   supplied-p-spec)))
    (let ((arg-gensyms
	   (loop for arg in all-args
		 collect
		 (cons (first-if-list arg)
		       (gensym (format nil "ARG-~A-"
				       (if (consp arg) (first arg) arg))))))
	  (args-for-expander
	     (loop for arg in all-args
		   append (if (consp arg)
			      (list (first arg) (third arg))
			      (list arg)))))
      (let ((args (loop for index from 0
			for args-already-bound =
			(firstn index (mapcar #'rest arg-gensyms))
			for arg in all-args
			collect (if (consp arg)
				    (list 'if
					  (third arg)
					  (first arg)
					  (sublis
					   (loop for a in args-already-bound
						 for b in all-args
						 collect (cons (if (consp b)
								   (first b)
								   b)
							       a))
					   (second arg)))
				    arg))))
	(values `(list 'let*
		  ,(cons 'list
			 (loop for spec in arg-gensyms
			       for arg = (rest spec)
			       for expr in args
			       collect
			       (list 'list
				     (list 'quote
					   arg)
				     expr)))
		  ,@(if allow-coercions-p
			(loop with kb-gensym = (rest (assoc 'kb arg-gensyms))
			      with kb-local-only-p-gensym
			      = (rest (assoc 'kb-local-only-p arg-gensyms))
			      for (arg type) in args-with-coercions
			      for gensym = (rest (assoc arg arg-gensyms))
			      when (and (member :OKBC-Frame-Coercion *features*
						:test #'string=)
					(not (member type '(:value (:value))
						     :test #'equal)))
			      collect
			      `(list 'setq ',gensym
				(list 'coerce-frame-arg ',gensym ',type
				 ',kb-gensym ',kb-local-only-p-gensym)))
			nil)
		  (list ',internal-name
		   ,@(loop for a in (mapcar #'rest arg-gensyms)
			   collect (list 'quote a))))
		args-for-expander)))))

(defun build-body-expander
    (name internal-name args supplied-p-spec args-with-coercions)
  (declare (ignore args))
  (let ((expander-name (intern (concatenate 'string
					    (string name)
					    "-BODY-EXPANDER")
			       (symbol-package name))))
    (multiple-value-bind (inner-form args-for-expander)
	(generate-compiler-macro-inner-form
	 internal-name supplied-p-spec args-with-coercions
	 nil)
      (declare (ignore args-for-expander))
      `(defun ,expander-name (form)
	 (destructuring-bind (,@supplied-p-spec) (rest form)
	   ,inner-form)))))

(defmacro ok-utils:defmethods (gf-name &rest stuff)
  "Define the power set of methods for different specializers.  For example,
	   (defmethods foo :before
       ((a (symbol number)) b (c (c1 (eql s1))) d &rest args)
       :baz)
	   will define the four methods:
	   (defmethod foo :before
       ((a symbol) b (c c1) d &rest args)
       :baz)
	   (defmethod foo :before
       ((a number) b (c c1) d &rest args)
       :baz)
	   (defmethod foo :before
       ((a symbol) b (c (eql s1)) d &rest args)
       :baz)
	   (defmethod foo :before
       ((a number) b (c (eql s1)) d &rest args)
       :baz)"
  (multiple-value-bind (qualifiers rest)
      (loop for x in stuff
	    for remainder on stuff
	    until (listp x)
	    collect x into quals
	    finally (return (values quals remainder)))
    (let ((args (first rest))
	  (body (rest rest)))
      (let ((specializers
	     (loop for arg in args
		   for index from 0
		   until (member arg lambda-list-keywords)
		   when (and (consp arg) (consp (second arg))
			     (not (eq 'eql (first (second arg)))))
		   collect (list index (first arg) (second arg)))))
	(if specializers
	    (cons 'progn
		  (loop for (index arg-name specs) in specializers
			for count from 0 below 1 ;; recursion will do the rest
			append
			(loop for spec in specs
			      collect `(defmethods ,gf-name ,@qualifiers
					(,@(loop for arg in args
						 for i from 0
						 collect
						 (if (= index i)
						     (list arg-name spec)
						     arg)))
					,@body))))
	    `(defmethod ,gf-name ,@stuff))))))

(defun test-arg-for-legal-literal 
    (arg-name arg-in-code function whole &optional (real-function function)
	      (error-p t))
  (let ((entry (loop for (arg spec . entry)
		     in *legal-literal-slot-values-alist*
		     when (and (eq arg-name arg)
			       (or (eq t spec)
				   (member function spec)))
		     return entry)))
    (loop for legal in entry
	  when (eq legal arg-in-code) return nil
	  when (and (symbolp arg-in-code) (boundp arg-in-code)
		    (eq legal (symbol-value arg-in-code)))
	  return nil
	  when (and (consp legal) (eq (first legal) 'function)
		    (funcall (second legal) arg-name arg-in-code))
	  return nil
	  when (and (consp legal) (eq (first legal) 'function)
		    (symbolp arg-in-code) (boundp arg-in-code)
		    (funcall (second legal) arg-name
			     (symbol-value arg-in-code)))
	  return nil
	  finally (when (or (and (symbolp arg-in-code) (boundp arg-in-code)
				 ;; The symbol must be interned to be a bogus
				 ;; literal.
				 (symbol-package arg-in-code))
			    (and (consp legal) (eq (first legal) 'function)
				 (or (multiple-value-bind (ok-p known-bogus-p)
					 (funcall (second legal) arg-name
						  arg-in-code)
				       (declare (ignore ok-p))
				       known-bogus-p)
				     (and (boundp arg-in-code)
					  (multiple-value-bind
						(ok-p known-bogus-p)
					      (funcall (second legal) arg-name
						       (symbol-value
							arg-in-code))
					    (declare (ignore ok-p))
					    known-bogus-p)))))
		    (if whole
			(apply (if error-p 'error 'warn)
			       "In call to ~S, illegal value for argument ~
                                ~S: ~S~%  Erring form: ~S"
			       real-function arg-name
			       arg-in-code whole)
			(apply (if error-p 'error 'warn)
			       "In call to ~S, illegal value for argument ~
                                ~S: ~S" real-function arg-name
				arg-in-code))))))

(defun coercion-code-for-compiler-macro
    (ctmps arguments-to-kb-specialize args-with-coercions)
  (if args-with-coercions
      `(,@(coerce-frame-args
	   ctmps (first arguments-to-kb-specialize)
	   (mapcar #'second args-with-coercions))
	,@(loop for arg in args-with-coercions
		for tmp in ctmps
		for type in (mapcar #'second args-with-coercions)
		when (not (eq :value type))
		collect (list 'setq (first arg) (list 'quote tmp))))
      nil))

(defun define-defokbcop-compiler-macro
    (name internal-name doc-string supplied-p-spec monitor-body advice-body
	  args-with-coercions arg-names returns-multiple-values-p
	  arguments-to-kb-specialize)
  (declare (ignore arguments-to-kb-specialize doc-string))
  #-OKBC-Record-Modifications (declare (ignore advice-body))
  #-Monitor-OKBC (declare (ignore monitor-body
				 #-OKBC-Record-Modifications arg-names))
  (let ((expand-name (intern (format nil "COMPILER-EXPAND-~A" name)
			     (symbol-package name))))
    (multiple-value-bind (inner-form args-for-expander)
	(generate-compiler-macro-inner-form
	 internal-name supplied-p-spec args-with-coercions t)
      `(progn
	(defun ,expand-name (whole ,@args-for-expander)
	  ,(format nil "Compiler macro expander function for ~S." name)
	  ,@(loop with found-p = nil
		  for arg in args-for-expander
		  for entry = (assoc arg *legal-literal-slot-values-alist*)
		  when entry do (setq found-p t)
		  when entry
		  collect
		  `(test-arg-for-legal-literal ',arg ,arg ',name whole)
		  finally (when (not found-p) 
				(return '((declare (ignore whole))))))
	  (let ((form
		  (list ',(if returns-multiple-values-p
			      'multiple-value-prog1 'prog1)
			(list 'let '(#+OKBC-Record-Modifications
				     (*advice* *advice*))
			      ;; Insert a call to the advice code
			      #+OKBC-Record-Modifications
			      (let ((advice-code (quote ,advice-body)))
				(loop for arg-name in (quote ,arg-names)
				      for arg in ,(cons 'list arg-names)
				      do (setq advice-code
					       (subst arg arg-name
						      advice-code)))
				advice-code)
			      ;; Call the internal-name method
			      ,inner-form
			      ;; Insert a call to the monitoring code
			      #+Monitor-OKBC
			      (let ((monitor-code (quote ,monitor-body)))
				(loop for arg-name in (quote ,arg-names)
				      for arg in ,(cons 'list arg-names)
				      do (setq monitor-code
					       (subst arg arg-name
						      monitor-code)))
				monitor-code)))))
	    (when *trace-okbc-compiler-macro-expansions-p*
	      (let ((*print-pretty* t))
		(format *trace-output* "~%Expanded call to ~S into ~%~S"
			',name form)))
	    form))
	(define-compiler-macro ,name (&whole whole ,@supplied-p-spec)
	  (,expand-name whole ,@args-for-expander))))))


(defun firstn (n l)
  (loop for index from 0 below n
        for element in l collect element))


(defun define-okbcop-top-level-function
  (name internal-name args arg-names args-with-coercions
        monitor-body advice-body doc-string
	returns-multiple-values-p arguments-to-kb-specialize
	allow-coercion-p)
  #-Monitor-OKBC (declare (ignore monitor-body))
  #-OKBC-Record-Modifications (declare (ignore advice-body))
  `(defun ,name (,@args)
     ,doc-string
     ,@(if allow-coercion-p
	   (coerce-frame-args arg-names (first arguments-to-kb-specialize)
			      (mapcar #'second args-with-coercions))
	   nil)
     ,@(loop for arg in arg-names
	     for entry = (assoc arg *legal-literal-slot-values-alist*)
	     when entry
	     collect `(test-arg-for-legal-literal ',arg ,arg ',name nil))
     (,(if returns-multiple-values-p 'multiple-value-prog1 'prog1)
      (#+Lucid let-globally #-Lucid let
	       (#+OKBC-Record-Modifications (*advice* *advice*))
	       #+OKBC-Record-Modifications ,advice-body
	       (,internal-name ,@arg-names))
      #+Monitor-OKBC
      ,monitor-body)))

(defmethod ok-utils:internal-name-to-op-name ((symbol symbol)) nil)

(defun var-is-in-tree (thing tree)
  (or (eq thing tree)
      (and (consp tree)
	   ;;; Just look at args to this function.
	   (loop for arg in (rest tree) thereis (var-is-in-tree thing arg)))))

(defun intern-okbcop-name (name)
  (intern (concatenate 'string (string name) "-INTERNAL")
	  :ok-back))

(defun internal-method-definition-style-checker (form)
  (when (and (consp form)
	     (member (first form) '(defmethod defmethods)))
    (let ((op (internal-name-to-op-name (second form))))
      (when op
	(let ((arg-names (remove-keywords-and-defaults
			  (ok-utils:okbcop-args op)))
	      (arglist (if (listp (third form))
			   (third form)
			   (fourth form))))
	  (let ((clashes
		 (loop for arg-name in arg-names
		       for arg-spec in arglist
		       for arg = (first-if-list arg-spec)
		       when (not (string-equal arg arg-name))
		       collect (list arg-name arg)))
		(*print-case* :downcase))
	    (when clashes
	      (format *error-output* "~&;;; Style warning:")
	   (format *error-output*
		   "~%;;; In the definition of:~%;;; (~{~S ~}...),"
		   (if (listp (third form))
		       (firstn 3 form)
		       (firstn 4 form)))
	   (loop for (arg-name arg) in clashes
		 do (format *error-output* "~%;;;     the expected ~
                                                 argument ~A is called ~A"
			    arg-name arg)))))))))

(defvar *all-okbc-compile-time-style-checkers*
  '(internal-method-definition-style-checker))

;;; If you're in Franz and using the runtime image then you don't want to
;;; do any style checking.  There's no compiler anyway.

#+EXCL
(when (and (member :excl *features*) (not (member :allegro-runtime *features*)))
  (excl::advise comp::compile-process-form :around
		:check-style-for-arg-compatibility ()
		(loop for ch in *all-okbc-compile-time-style-checkers*
		      do (funcall ch (first user::arglist)))
		:do-it))


#+lucid
(lcl::defadvice (lucid::compile-form :check-style-for-arg-compatibility)
	(&rest args)
  (loop for ch in *all-okbc-compile-time-style-checkers*
	do (funcall ch (first args)))
  (lcl::apply-advice-continue args))

#+Harlequin-Common-Lisp
(cl-user::defadvice
    (compiler::process-form :check-style-for-arg-compatibility :around)
	(&rest args)
  (loop for ch in *all-okbc-compile-time-style-checkers*
	do (funcall ch (first args)))
  :do-it)

#+excl
(excl::advise comp::compile-process-form :around
	      :check-style-for-arg-compatibility ()
  (loop for ch in *all-okbc-compile-time-style-checkers*
	do (funcall ch (first user::arglist)))
  :do-it)

#-(or lucid excl Harlequin-Common-Lisp)
(cerror "Go ahead, anyway" "Please implement the style checker hook.")

(defun default-method-def (classes internal-name arg-names
				   arguments-to-kb-specialize default-body)
  `(defmethods ,internal-name
    ,(loop for arg in arg-names
	   collect (if (member arg arguments-to-kb-specialize)
		       (list arg classes)
		       arg))
    ,@(if (and (consp default-body)
	       (consp (first default-body))
	       (not (eq (first (first default-body)) 'lambda)))
	  default-body
	  (if default-body
	      (list default-body)
	      (list
	       `(declare
		 (ignore
		  ,@(loop for arg in arg-names
			  when
			  (not (member
				arg arguments-to-kb-specialize))
			  collect arg)))
	       default-body)))))

(defun side-effect-has-no-ontological-effect-p (name)
  (member name '(register-procedure)))

(defun check-and-abort-for-sfc ()
  #+Lucid
  (when lucid:*use-sfc*
    (cerror "Abort and switch to PQC"
	    "Sorry, you can't use the SFC because of a compile ~
                            bug.")
    (proclaim '(optimize (speed 3) (safety 0)
		(compilation-speed 0)))
    (abort)))

(defun build-defokbcop-defgeneric-form
    (name internal-name arg-names doc-string causes-side-effects-p
	  arguments-to-kb-specialize
	  default-body default-body-supplied-p
	  standard-default-body standard-default-body-supplied-p
	  tell&ask-default-body tell&ask-default-body-supplied-p)
  (let ((kb-args (loop for arg in arg-names
		       when (member arg arguments-to-kb-specialize)
		       collect arg))
	(arg-check-form
	 (if (and #+lucid (not lucid:*use-sfc*)
		  (loop for arg-name in arg-names
			thereis (assoc arg-name
				       *legal-literal-slot-values-alist*)))
	     `((define-compiler-macro ,internal-name (&whole whole ,@arg-names)
		 (declare (ignore 
			   ,@(loop for arg-name in arg-names
				   for entry =
				   (assoc arg-name
					  *legal-literal-slot-values-alist*)
			 when (not entry)
			 collect arg-name)))
		 (check-and-abort-for-sfc)
		 ,@(loop for arg-name in arg-names
			 for entry = (assoc arg-name
					    *legal-literal-slot-values-alist*)
			 when entry
			 collect `(test-arg-for-legal-literal
				   ',arg-name ,arg-name ',name whole 
				   ',internal-name))
		 whole))
	   nil)))
    `((defokbcgeneric ,internal-name (,@arg-names)
	(:documentation
	 ,(if doc-string
	      (concatenate 'string
			   (format nil "Implementation generic function ~
                               for ~S, whose documentation is:~%"
			     name)
			   doc-string)
	      (format nil "Implementation generic function for ~S." name)))
	,@(loop for kb-arg in kb-args
		collect
		`(:Method
		  ,(loop for arg in arg-names
			 collect (if (eq arg kb-arg)
				     (list arg 'okbc-forwarding-mixin)
				     arg))
		  (when (slot-boundp ,kb-arg 'target-kb)
		    (,internal-name
		     ,@(loop for arg in arg-names
			     collect (if (eq arg kb-arg)
					 (list 'target-kb arg)
					 arg))))))
	,@(if (and causes-side-effects-p
		   (not (side-effect-has-no-ontological-effect-p name)))
	      (loop for kb-arg in kb-args
		    when (and (not (string-equal (first-if-list kb-arg)
						 :kb-type))
			      (not (member name '(okbc:goto-kb))))
		    collect
		    `(:Method
		      ,(loop for arg in arg-names
			     collect
			     (if (eq arg kb-arg)
				 (list arg
				       'okbc-side-effects-cause-error-mixin)
				 (list arg t)))
		      (error 'read-only-violation
		       :error-message
		       (format nil
			,(format nil "OKBC operator ~A not permitted in KB ~
                                         ~~S because side-effects are not ~
                                         allowed."
				 name)
			,kb-arg))))
	      nil))
      ,@arg-check-form
      ,@(if default-body-supplied-p
	    (list (if (and default-body-supplied-p kb-args)
		      (default-method-def
			  '(kb structure-kb)
			  internal-name arg-names
			  arguments-to-kb-specialize default-body)
		      (default-method-def 'kb
			  internal-name arg-names
			  arguments-to-kb-specialize default-body)))
	    nil)
      ,@(if standard-default-body-supplied-p
	    (list (if (and standard-default-body-supplied-p kb-args)
		      (default-method-def
			  '(standard-defaults-kb structure-kb)
			  internal-name arg-names
			  arguments-to-kb-specialize standard-default-body)
		      (default-method-def 'standard-defaults-kb
			  internal-name arg-names
			  arguments-to-kb-specialize standard-default-body)))
	    nil)
      ,@(if tell&ask-default-body-supplied-p
	    (list (default-method-def
		      '(tell&ask-defaults-kb tell&ask-defaults-structure-kb)
		      internal-name arg-names
		      arguments-to-kb-specialize tell&ask-default-body))
	    nil))))

(defun merge-strings (strings)
  (if strings
      (let ((output (make-string (+ (- (length strings) 1)
				    (loop for x in strings sum (length x))))))
	(loop with index = 0
	      for s in strings
	      for first-p = t then nil
	      when (not first-p)
	      do (setf (schar output index) #\newline)
	      (incf index)
	      do (loop for i from 0 below (length s)
		       do (setf (schar output index) (schar s i))
		       (incf index)))
	(string-trim '(#\space #\newline #\return) output))
      nil))

(defun extract-doc-for-okbcop-from-tex-file (okbcop path)
  (when (probe-file path)
    (with-open-file (stream path :direction :input)
      (loop with *package* = (find-package :okbc)
	    with start-cookie = (format nil "\\begin{okbcop}{~A}" okbcop)
	    with end-cookie = (format nil "\\end{okbcop}")
	    for line = (read-line stream nil)
	    for index = (search start-cookie line :test #'char-equal)
	    when (not line) return nil
	    when index 
	    do (let ((strings
		      (cons (concatenate
			     'string
			     (string okbcop) " "
			     (subseq line (length start-cookie)))
			    (loop for line = (read-line stream nil)
				  when (not line)
				  do (warn "!!! Documentation for ~S is not ~
                                              terminated."
					   okbcop)
				  until (or (not line)
					    (search end-cookie line
						    :test #'char-equal))
				  collect line))))
		 (return (merge-strings strings)))))))

(defun compute-enumerator-name (name)
  (intern (concatenate
	   'string
	   "ENUMERATE-"
	   (if (and (> (length (string name)) 4)
		    (string= "GET-" (string name)
			     :end2 (length "GET-")))
	       (subseq (string name) 4)
	       (string name)))
	  :okbc))

(defun generate-enumerator-defokbcop (name internal-name arguments
					  arguments-to-kb-specialize
					  potentially-functional-arguments)
  (let ((enumerator-name (compute-enumerator-name name))
	(arg-names (remove-keywords-and-defaults
		    (remove-coercion-specs arguments))))
    `(defokbcop ,enumerator-name (,@arguments)
      :returned-values enumerator
      :doc-string
      ,(format nil "Returns an enumerator for the elements returned by ~%~
                  \\kfn{~A}."
	       (string-downcase name))
      :default-body
      ,(if arguments-to-kb-specialize
	   `(let ((*current-kb* ,(first arguments-to-kb-specialize)))
	      (enumerate-list-internal (,internal-name ,@arg-names)))
	   `(enumerate-list-internal (,internal-name ,@arg-names)))
      :compliance-classes :read
      :arguments-to-kb-specialize ,arguments-to-kb-specialize
      :manual-category :enumerator
      :potentially-functional-arguments ,potentially-functional-arguments)))

(defmacro ok-utils:with-defokbcop-bindings ((form) &body body)
  "Takes a <code>form</code>, which is the body of a call to the
   <code>ok-back:defokbcop</code> macro and executes <code>body</code> binding
   locals of the appropriate names to all of the arguments of the call to
   <code>ok-back:defokbcop</code>, defaulting where appropriate.<P>

   This macro is useful in code that reads OKBC operator defining source
   files and generates new code, such as the C and Java client code generators."
  (let ((arg-spec '(name arguments
		    &key doc-string
		    (default-body nil default-body-supplied-p)
		    (standard-default-body
		     nil standard-default-body-supplied-p)
		    (tell&ask-default-body
		     nil tell&ask-default-body-supplied-p)
		    monitor-body modification-body
		    advice-body
		    (arguments-to-kb-specialize '(kb kb-type))
		    (returned-values nil)
		    (potentially-functional-arguments nil)
		    (causes-side-effects-p nil)
		    (compliance-classes nil)
		    (enumerator nil)
		    (which-ends '(:back :front))
		    (manual-category nil))))
    (let ((alist
	   (loop for x in arg-spec
		 append (cond ((member x lambda-list-keywords) nil)
			      ((symbolp x)
			       (list (cons x (intern (symbol-name x)
						     *package*))))
			      ((consp x)
			       (let ((argx
				      (list (cons (first x)
						  (intern (symbol-name
							   (first x))
							  *package*)))))
				 (if (third x)
				     (cons (cons (third x)
						 (intern (symbol-name
							  (third x))
							 *package*))
					   argx)
				     argx)))))))
      `(destructuring-bind ,(sublis alist arg-spec)
	,form
	,@body))))

(defmacro ok-back:defokbcop
    (&whole whole
	    name (&rest arguments)
	    &key doc-string
	    (default-body nil default-body-supplied-p)
	    (standard-default-body
	     nil standard-default-body-supplied-p)
	    (tell&ask-default-body
	     nil tell&ask-default-body-supplied-p)
	    monitor-body modification-body
	    advice-body
	    (arguments-to-kb-specialize '(kb kb-type))
	    (returned-values nil)
	    (potentially-functional-arguments nil)
	    (causes-side-effects-p nil)
	    (compliance-classes nil)
	    (enumerator nil)
	    (which-ends '(:back :front))
	    (manual-category nil))
  "Defines a macro for defining those OKBC operations that are
   implemented as generic functions.<P>

   For an operation called <code>okbc:name</code>, a function is generated and a
   compiler macro called <code>okbc:name</code>, along with a
   <code>defgeneric</code> form called <code>ok-back:name-INTERNAL</code>,
   and in some cases, methods on that generic function.  Numerous other methods
   on <code>ok-back:name-INTERNAL</code>, functions and compiler macros are
   also generated for such purposes as cache wrapping and style checking.<P>
   <DL>
   <DT>name  <DD>- the name for the user-level OKBC function,
   <DT>arguments <DD>- the arglist to the top-level function.  Arguments to
                the left of the &key must have a known type.
   <DT>doc-string <DD>- documentation for the top-level function
   <DT>default-body <DD>- if supplied this is used as the body for the
                  default method for this top-level function.  If this is not
                  provided then no default (<code>T</code> specialized) method
                  is provided and an error will be signaled if this function
                  is invoked on an unknown KB type.
   <DT>standard-default-body <DD>- the same as <code>default-body</code>, only
                           this default applies
                           only to the <code>standard-defaults-kb</code> middle
                           end.
   <DT>tell&ask-default-body <DD>- the same as <code>default-body</code>, only
                           this default applies
                           only to the <code>tell&ask-defaults-kb</code> middle
                           end.
   <DT>monitor-body <DD>- if supplied, is code that we insert into the generated
                  function and compiler macro.
   <DT>modification-body <DD>- if supplied, is code that we insert into an after
                       method on <code>ok-back:name-INTERNAL</code>.
   <DT>arguments-to-kb-specialize <DD>- is the list of the names of the
                               arguments to
                               the default method which should be specialized
                               on <code>kb</code>
   <DT>returned-values <DD>- the value or list of values returned.  Mandatory.
   <DT>potentially-functional-arguments <DD>- a list of the names of arguments
                               that might take on functional values, such as
                               <code>:test</code>.
   <DT>causes-side-effects-p <DD>- when true asserts that the okbcop causes
                      side effects when called.  This is important for proxy
                      OKBC implementations so that they know when to flush
                      caches.
   <DT>compliance-classes <DD>- a keyword or list of keywords naming the
                      compliance classes of which this op is a member.
                      Mandatory OKBC ops must be in at least one compliance
                      class.
   <DT>enumerator <DD>- when true, generates an enumerator OKBCOP as well.
   <DT>which-ends <DD>- the <code>:back</code> or <code>:front</code> end
                        applicability for this op.
   <DT>manual-category <DD>- a keyword naming the operator category in the
                             manual.
   </DL>
  "
  #-OKBC-RECORD-MODIFICATIONS
  (declare (ignore modification-body))
  (let ((body (nthcdr 3 whole)))
    (loop for key in body by #'cddr
	  for rest on (rest (rest body)) by #'cddr
	  when (getf rest key)
	  do (warn "Multiple instances of keyword arg ~S in okbcop ~S"
		    key name)))
  (assert (keywordp manual-category)
	  () "You must specify the manual-category")
  (assert (not (and default-body
		    (or standard-default-body tell&ask-default-body)))
	  () "Cannot have a :default-body and either a :standard-default-body ~
              or a :tell&ask-default-body")
  (assert (or default-body-supplied-p
	      standard-default-body-supplied-p
	      compliance-classes) ()
	  "Mandatory OKBC op ~S (has neither no default body) has no ~
           compliance classes."
	  name)
  (assert returned-values () "No returned values supplied for OKBC op ~S."
	  name)
  (assert (listp which-ends))
  (setq returned-values
	(if (eq :void returned-values) nil (list-if-not returned-values)))
  (loop for c in (list-if-not compliance-classes)
	do (assert (member c ok-back:*all-known-okbc-compliance-classes*
			   :key 'first-if-list)
		   () "~S is not a known compliance class." c))
;  (setq doc-string
;        (or doc-string (extract-doc-for-okbcop-from-tex-file
;                        name (tex-doc-path))))
;  (when (not doc-string)
;    (warn "OKBC operator ~S has neither a doc string nor a manual entry."
;          name))
  (when (not doc-string) (warn "OKBC operator ~S has no doc string." name))
  (let ((supplied-p (supplied-p-ify (remove-coercion-specs arguments)))
	(internal-name (intern-okbcop-name name))
	(args (remove-coercion-specs arguments))
	(arg-names (remove-keywords-and-defaults
		    (remove-coercion-specs arguments)))
	(args-with-coercions (get-coercion-specs arguments))
	(returns-multiple-values-p (not (null (rest returned-values))))
	(detexed-doc-string (detex doc-string)))
    (setq arguments-to-kb-specialize
	  ;; Make sure we preserve order.  Intersection is not guaranteed to.
	  (loop for x in arguments-to-kb-specialize
		when (member x arg-names) collect x))

    (setq potentially-functional-arguments
	  (list-if-not potentially-functional-arguments))
    (loop for arg in potentially-functional-arguments
	  do (assert (member arg arg-names) ()
		     "Potentially functional arg ~S is not specified in the ~
                      arglist of ~S"
		     arg name))
    ;; Get the compiler to tell us what it's compiling
    ;; when errors occur.
    #+Lucid
    (setq sys:*compiler-message-string* (string name))
    (let ((top-level-function
	   (define-okbcop-top-level-function
	     name internal-name args arg-names args-with-coercions
	     monitor-body advice-body detexed-doc-string
	     returns-multiple-values-p
	     arguments-to-kb-specialize
	     (and arguments-to-kb-specialize
		  (member :OKBC-Frame-Coercion *features*))))
	  (compiler-macro
	   (define-defokbcop-compiler-macro
	     name internal-name detexed-doc-string supplied-p monitor-body
	     advice-body args-with-coercions arg-names
	     returns-multiple-values-p arguments-to-kb-specialize))
	  (compiler-macro-body
	   (let ((exp (build-body-expander name internal-name args
					   supplied-p args-with-coercions)))
	     `(,exp
	       (defmethod body-expander-function
		   ((okbcop (eql ',name)))
		 ',(second exp)))))
	  (side-effect-form
	   `((defmethod ok-utils:causes-side-effects-p
		 ((okbcop (eql ',name)))
	       ,(not (null causes-side-effects-p)))
	     (defmethod ok-utils:causes-side-effects-p
		 ((okbcop (eql ',internal-name)))
	       ,(not (null causes-side-effects-p)))))
	  (raw-documentation-method
	   `(defmethod raw-documentation ((okbcop (eql ',name)))
	      ,doc-string))
	  (multiple-values-form
	   `(defmethod returns-multiple-values-p ((okbcop (eql ',name)))
	      ,returns-multiple-values-p))
	  (args-form `(defmethod ok-utils:okbcop-args
		       ((okbcop (eql ',name)))
		       (values ',args ',returned-values ',arg-names)))
	  (which-ends-method
	   `(defmethod which-ends ((okbcop (eql ',name)))
	     ',which-ends))
	  (potentially-functional-arguments-form
	   `(defmethod potentially-functional-arguments ((okbcop (eql ',name)))
	      (values ',potentially-functional-arguments
		      ',(loop for arg in potentially-functional-arguments
			      collect
			      (position arg args :key 'first-if-list)))))
	  (internal-name-to-op-name-form
	   `(defmethod internal-name-to-op-name
	      ((okbcop (eql ',internal-name)))
	      ',name))
	  (op-name-to-internal-name-form
	   `(defmethod op-name-to-internal-name
	      ((okbcop (eql ',name)))
	      ',internal-name))
	  (compliance-classes-method
	   `(defmethod compliance-classes
	     ((okbcop (eql ',internal-name)))
	     ',(list-if-not compliance-classes)))
	  (has-enumerator-p-method
	   `(defmethod has-enumerator-p
	          ((okbcop (eql ',internal-name)))
	     ,(not (null enumerator))))
	  (kb-specialization-argument-form
	   `(defmethod ok-utils:kb-specializing-arguments
	      ((okbcop (eql ',name)))
	      (values ',(loop for arg in arguments-to-kb-specialize
			      when (member arg arg-names)
			      collect arg)
		      ',(loop for arg in arguments-to-kb-specialize
			      for pos = (position arg arg-names)
			      when pos
			      collect pos))))
	  (cache-method-forms
	   (define-cache-methods
	       name args arguments-to-kb-specialize
	       returns-multiple-values-p (length returned-values)
	       causes-side-effects-p))
	  (number-of-values-forms
	   (define-number-of-values-method
	       internal-name args arg-names arguments-to-kb-specialize
	       returned-values))
	  (defgeneric-forms
	      (build-defokbcop-defgeneric-form
	       name internal-name arg-names detexed-doc-string
	       causes-side-effects-p arguments-to-kb-specialize
	       default-body default-body-supplied-p
	       standard-default-body standard-default-body-supplied-p
	       tell&ask-default-body tell&ask-default-body-supplied-p))
	  (funarg-forms
	   (define-procedure-handlers
	       internal-name args arguments-to-kb-specialize
	       potentially-functional-arguments))
	  (network-forms
	   (network-okbc-method
	    name args arguments-to-kb-specialize
	    potentially-functional-arguments))
	  (network-coercion-forms
	   (define-network-coercion-forms
	       internal-name arg-names arguments-to-kb-specialize
	       args-with-coercions)))
      ;;; Load the *-internal GF now so that it is defined at compile-time
      ;;; so that we don't get a barf out of compiling the top-level-function
      ;;; in the absense of any delayed undefined-function reporting mechanism
      ;;; that you get for free from the average defsystem.
					;      (eval defgeneric-form)   ;; AVOID DOUBLE EVAL (KLM 8-26-94)
      ;;; For Lucid we load the function definition.  This gets around
      ;;; a noisy warning about the compiler-macro apparently being redefined
      ;;; by the function
					;      #+Lucid
					;      (eval top-level-function)  ;; AVOID DOUBLE EVAL (KLM 8-26-94)
    ;;; Evaluate the compiler macro to make sure that it is defined in the
    ;;; compilation environment.  This is a little dirty, but it makes it
    ;;; possible to reference okbcops in the same file in which they are
    ;;; defined and still get the right compiler behavior.
					;      (eval compiler-macro)  ;; AVOID DOUBLE EVAL  (KLM 8-26-94)
      (ensure-api-symbol-ok
       name (if (member :front which-ends) :okbc :ok-back))
      (ensure-api-symbol-ok internal-name :ok-back)
      `(progn
	 ,top-level-function
	 ,args-form
	 ,compiler-macro
	 ,raw-documentation-method
	 ,@defgeneric-forms
	 ,@number-of-values-forms
	 ,@compiler-macro-body
	 ,@side-effect-form
	 ,@cache-method-forms
	 ,@funarg-forms
	 ,@network-forms
	 ,@network-coercion-forms
	 ,multiple-values-form
	 ,has-enumerator-p-method
	 ,compliance-classes-method
	 ,potentially-functional-arguments-form
	 ,kb-specialization-argument-form
	 ,internal-name-to-op-name-form
	 ,op-name-to-internal-name-form
	 (defmethod manual-category ((name (eql ',name)))
	   ',manual-category)
	 ,which-ends-method
	 ,@(if enumerator
	       (list (generate-enumerator-defokbcop
		      name internal-name arguments
		      arguments-to-kb-specialize
		      potentially-functional-arguments))
	       nil)
	 (add-okbcop ',name)
	 (setf (gethash ',internal-name
		*acceptable-okbcops-for-call-procedure*)
	  t)
	 (let ((source-path ',(current-source-file)))
	   (when source-path
	     (let ((true (namestring (or (ignore-errors
					  (truename source-path))
					 source-path))))
	       (when (not (member true *all-files-defining-okbcops*
				  :test #'string=))
		 (push true *all-files-defining-okbcops*)))))
	 ;; Create an after method that calls the modification-body,
	 ;; if supplied.
	 #+OKBC-Record-Modifications
	 ,(when modification-body
	    `(defmethod ,internal-name
	       :after (,@(substitute
			  (list (first arguments-to-kb-specialize)
				'ok-back::frame-logging-mixin)
			  (first arguments-to-kb-specialize)
			  arg-names))
	       (declare
		(ignore ,@(loop for arg in arg-names
				unless (or (eq arg
					       (first
						arguments-to-kb-specialize))
					   (var-is-in-tree
					    arg modification-body))
				collect arg)))
	       ,modification-body))
	 ',name))))

(defmethod ok-utils:causes-side-effects-p ((thing t))
  (continuable-error "~S is not an OKBC operator" thing))

(defmacro ok-back:defblock-of-okbc-methods
    (class (&key modifier condition) &body body)
  "This macro is used to generate a set of methods on a particular KB class
   for some subset of the OKBC operations.  It is particularly useful is
   a back end implementor wants to implement a set of daemon or wrapper
   methods to do operations like notification or caching.  <code>modifier</code>
   is a defmethod modifier, and <code>condition</code> is a predicate or one
   argument called with the name of an OKBC operation used to
   determine whether a method should be defined.  <code>Body</code> can be
   either a set of forms to put in the body of the method, or a function
   name to call at macroexpansion to compute the code for the method body.
   Within the body of the method, the arguments for the method will have
   the appropriate names specified in the specification.  These can be computed
   using <code>ok-utils:okbcop-args</code>.
   For example,<PRE>
   (ok-back::defblock-of-okbc-methods my-kb
      (:modifier :after :condition ok-utils:causes-side-effects-p)
      (format t \"~%Some side effect just happened.\"))</PRE>
   will define one <code>:after</code> daemon method on the class
   <code>my-kb</code> for every side-effecting
   OKBC operation that prints out a message after the side-effect has happened.
   In the following example, a tailored trace message is printed out for
   all non-side-effect causing operations.<PRE>
   (defun doesnt-cause-side-effects-p (x)
     (not (ok-utils:causes-side-effects-p x)))

   (defun trace-message-body (op-name)
     (format t \"~%Entering ~S\" op-name)
     (let ((results (multiple-value-list (call-next-method))))
       (format t \"~%Exiting ~S with results ~{~S~^, ~}\" op-name results)
       (values-list results)))

   (ok-back::defblock-of-okbc-methods my-kb
      (:modifier :around :condition doesnt-cause-side-effects-p)
      trace-message-body)</PRE>"
  (cons 'progn
	(loop for op in *all-okbcops*
	      when (and (ok-utils:kb-specializing-arguments op)
			(or (not condition) (funcall condition op)))
	      append (loop for spec in (ok-utils:kb-specializing-arguments op)
			   collect `(defmethod ,(intern-okbcop-name op)
				     ,@(if modifier (list modifier) nil)
				     (,@(loop with full-args
					      = (ok-utils:okbcop-args op)
					      for arg in
					      (remove-keywords-and-defaults
					       (remove-coercion-specs
						full-args))
					      for shifted = (intern
							     (symbol-name arg)
							     *package*)
					      collect (if (eq arg spec)
							  (list shifted class)
							  (list shifted t))))
				     ,@(if (and (= (length body) 1)
						(atom (first body)))
					   (list-if-not (funcall body op))
					   body))))))

;-----------------------------------------------------------------
;                         Iteration Macros
;-----------------------------------------------------------------

(defun make-selector-name (macro-name)
  (intern (concatenate 'string "." (symbol-name macro-name) "-SELECTOR.")
	  'ok-kernel))

(defun create-or-replace-method (generic-function qualifiers lambda-list
		      specializers method-function)
  "Adds a method as specified to the particular GF.  If the method allready
   exists then it redefines it."
  (let ((specs (loop for spec in specializers
		     collect (if (consp spec) spec (find-class spec)))))
    #-MCL
    (add-method
      generic-function
      (make-instance #-EXCL 'standard-method
		     ;;; Note: EXCL doesn't export standard-method,
		     ;;; so this is just a little patch until they
		     ;;; fix it.   JPR.
		     #+EXCL 'clos::standard-method
		     :qualifiers qualifiers
		     :lambda-list lambda-list
		     #+ti :parameter-specializers #-ti :specializers specs
		     :function method-function))
    #+MCL
    (ccl::%add-method
      (make-instance 'cl::standard-method
		     :Qualifiers qualifiers
		     :Specializers specs
		     :Name (ccl::function-name generic-function)
		     :Function method-function)
      generic-function)))


#-Monitor-OKBC
(defun record-reference (&rest args)
  (declare (ignore args))
  )

#-okbc-record-modifications
(defun record-modification (&rest args)
  (declare (ignore args))
  )

;==============================================================================

;;; This defines a macro to create network okbc stub kb classes according to
;;; the approved naming convention.

(eval-when (compile load eval)
  (defparameter *network-okbc-kb-mixins* nil
    "A list of the default mixin classes to add to network stub KBs.
     See <code>defnetwork-okbc-kb</code>."))

(defmacro ok-back:defnetwork-okbc-kb (name (&rest mixins))
  "Defines network stub Kb classes for the KB class <code>name</code>.
   The network layer automatically generates network stub classes for
   KB classes that it doesn't know.  This macro allows the opportunity to
   override the default behavior, possibly adding extra mixins, such as
   <code>caching-mixin</code>.  The default mixins used for network stub KB
   classes is defined in <code>*network-okbc-kb-mixins*</code>.<P>

   Another reason for using this macro would be
   for an application in which methods are defined for the KB class on the
   client side.  This is a rare, but legitimate use.  Without the network
   stub class (and the abstract class) being defined, these methods cannot
   be added.  For example, if we had an application that made a strong
   assumption about all frames being named, but ended up communicating with
   a KB that allowed annonymous frames, we might want to allocate frame names
   on the client side for this particular KB class.  For example, in the
   kb class <code>my-kb</code> we might do the following:<PRE>
   (ok-back:defnetwork-okbc-kb my-kb (ok-back:caching-mixin))

   (defvar *name-to-frame-mapping-table* (make-hash-table))

   (defmethod ok-back:get-frame-name-internal :around
      ((frame t) (kb ok-back:my-kb-network-kb) (kb-local-only-p t))
     (or (gethash frame *name-to-frame-mapping-table*)
         (let ((result (call-next-method)))
           (if result
               result
               (let ((name (gentemp)))
                  (setf (gethash frame *name-to-frame-mapping-table*) name)
                  name)))))</PRE>"   
  (let ((network-name (intern (concatenate 'string (string name) "-NETWORK-KB")
			      :ok-back))
	(abstract-name (intern (concatenate 'string "ABSTRACT-" (string name)
					    "-KB")
			       :ok-back)))
    `(progn (unless (find-class ',abstract-name nil)
	      (defokbcclass ,abstract-name () ()))
      (unless (let ((c (find-class ',network-name nil)))
		(and c (let ,(if (append mixins *network-okbc-kb-mixins*)
				 '((kb-type (class-prototype-safe c)))
				 nil)
			 (and ,@(loop for m
				      in (append mixins
						 *network-okbc-kb-mixins*)
				      collect `(typep kb-type ',m))))))
	(defokbcclass ,network-name (,abstract-name ,@mixins
						   ,@*network-okbc-kb-mixins*
						   network-kb)
	  ((abstract-name :accessor abstract-name
			  :initarg abstract-name
			  :initform ',abstract-name
			  :allocation :class))))
      (find-class ',network-name))))

(defmacro ok-back:defnetwork-okbc-structure-kb (name)
  "This is the defstruct equivalent of <code>defnetwork-okbc-kb</code>.
   Because this applies to defstruct KBs, no mixins apply."
  (let ((network-name (intern (concatenate 'string (string name) "-NETWORK-KB")
			      :ok-back))
	(abstract-name (intern (concatenate 'string "ABSTRACT-" (string name)
					    "-KB")
			       :ok-back)))
    `(progn
      (defstruct (,abstract-name (:include network-structure-kb)))
      (defstruct (,network-name (:include ,abstract-name)))
      ',network-name)))

;------------------------------------------------------------------------------

;;; Caching stuff

(defmacro ok-utils:defmethod-with-cache-method (name args &body body)
  "This macro is just like defmethod, and defines a method and wraps a
   cache wrapper around it (as an :around method).  This is useful is you
   are using the standard OKBC caching code in your back end, and you want
   to add specific cached calls on top of the standard ones."
  (let ((arg-names (remove-keywords-and-defaults args)))
    (flet ((make-cache-args (class)
	     (let ((res nil))
	       (loop for arg in args
		     for rest on args
		     until (member arg lambda-list-keywords)
		     do (push (if (consp arg) (list (first arg) class) arg)
			      res)
		     finally (when (member arg lambda-list-keywords)
			       (loop for arg in rest
				     do (push arg res))))
	       (reverse res))))
      `(progn
	(defmethods ,name :around ,
	  (make-cache-args
	   '(caching-mixin caching-structure-kb))
	  (with-okbc-cache
	      ((ok-cache:cache kb) nil (list ',name ,@arg-names) kb)
	    (call-next-method)))
	(defmethods ,name ,args ,@body)))))

;==============================================================================

(defokbcgeneric ok-back:fast-hash-key (thing)
  (:documentation "In some Lisp implementations, some data structures hash
   much faster or more evenly than others.  For example, symbols might have
   better hashing behavior than CLOS instances.  Because of this difference
   in performance, a number of places in the OKBC implementation indirect
   before hashing occurs from objects to the hash keys that give faster hashing
   for those objects.  <P>

   This generic function maps from an object to the fast-hash-key for that
   object.  If there is a fast-hash-key for an object, it will typically be
   a symbol in a slot on that object, and a method will be defined on this
   generic function that is a slot accessor for that object.  In some
   implementations, the difference in hashing performance can be so great
   as more than to outweigh the method dispatch to get the fast-hash-key."))

(defmethod ok-back:fast-hash-key ((thing t)) thing)

(defvar ok-utils:*err-on-read-only-violations-p* t
  "When true (the default) causes an error to be signalled when a read-only
   violaiton is detected.  When false, a warning is issued as a result of a
   read-only violation.")

(defvar ok-utils:*inhibit-read-onlyness-p* nil
  "When false (the default) allows the checking of read-only constraints on
   KBs.  This variable is useful to bind in back ends that are dealing
   with otherwise read-only KBs but have reason to write to them, for
   example during loading.")

(defmacro ok-utils:with-read-only-checking
    ((kb &optional (return kb) format-string &rest args)
     &body body)
  "Executes the <code>body</code> so that if <code>kb</code> is a read-only
   KB, a read-only violation will be signalled.  Whether an error or a warning
   is signalled is controlled by
   <code>*err-on-read-only-violations-p*</code>.  Whether a violation
   is signalled or not is also controlled by
   <code>*inhibit-read-onlyness-p*</code>.
   If a read-only violation is detected, and an error is not signalled,
   the value <code>return</code> is returned.<p>

   <code>Format-string</code> (if supplied) and <code>args</code> are used to
   generate the error message.  If they are not supplied a default error
   message is generated."
  `(if (and (not *inhibit-read-onlyness-p*) ,kb (ok-utils:read-only-p ,kb))
    (with-kb-io-syntax (:kb ,kb :purpose :user-interface)
      (let ((error-message
	     ,(if format-string
		  `(format nil ,format-string ,@args)
		  `(format nil "KB ~S is read-only.  ~
                     (Re)Definitions and modifications are not allowed."
		    (name ,kb)))))
	(if ok-utils:*err-on-read-only-violations-p*
	    (error 'okbc:read-only-violation :error-message error-message)
	    (warn error-message)))
      ,return)
    (progn ,@body)))

(defmacro ok-utils:fast-gethash-for-symbol (hash-key ht)
  "Just like <code>gethash</code> only the <code>hash-key</code> is assumed
   to be a symbol.  In some implementations this results in faster hashing."
  `(#+Lucid lucid:gethash-fast-for-symbol #-Lucid gethash ,hash-key ,ht))

;;; Substitution groups....

(defun case-replace (from to)
  (cond ((string= (string-upcase from) from) (string-upcase to))
	((string= (string-downcase from) from) (string-downcase to))
	((string= (string-capitalize from) from) (string-capitalize to))
	(t (string-capitalize to))))

(defun string-subst (new old string)
  (let ((index (search (string old) string :test #'char-equal)))
    (if index
	(concatenate 'string
	 (subseq string 0 index)
	 (case-replace
	  (subseq string index (+ index (length (string old)))) (string new))
	 (string-subst
	  new old (subseq string (+ index (length (string old))))))
	string)))

(defun string-subst-symbol (new old symbol)
  (let ((new-string (string-subst (string-upcase new) (string-upcase old)
				  (symbol-name symbol))))
    (intern new-string (symbol-package symbol))))

(defun substitute-within-sexpression (new old tree)
  (typecase tree
    (cons (cons (substitute-within-sexpression new old (first tree))
		(substitute-within-sexpression new old (rest  tree))))
    (symbol (typecase old
	      (symbol (if (eq old tree) new tree))
	      (string (if (search old (string tree) :test #'char-equal)
			  (string-subst-symbol new old tree)
			  tree))
	      (otherwise tree)))
    (string (typecase old
	      ((or string symbol) (string-subst new old tree))
	      (otherwise tree)))
    (otherwise tree)))

(defun substitute-all-within-sexpression (news-and-olds tree)
  (if news-and-olds
      (substitute-all-within-sexpression
       (rest news-and-olds)
       (substitute-within-sexpression
	(first (first news-and-olds)) (second (first news-and-olds)) tree))
      tree))

(defmacro ok-utils:with-substitution-groups
    ((&rest substitution-alists) &body body)
  "A utility macro that takes a number of forms in <code>body</code> and
   replicates that code substituting the symbols and strings provided in
   <code>substitution-alists</code>.  This is useful is a chunk of code is
   going to be basically the same but for a few tiny changes for a number
   of different cases.  Using this macros lets you substitute accessor names
   within methods and such like.  For example:<PRE>
   (with-substitution-groups (((\"STRUCTURE-TUPLE-KB\" \"TUPLE-KB\")))
     (defmethod get-foo ((kb tuple-kb))
        (tuple-kb-foo kb)))</PRE> will expand into:
   <PRE>   (PROGN (DEFMETHOD GET-FOO ((KB TUPLE-KB))
            (TUPLE-KB-FOO KB))
          (DEFMETHOD GET-FOO ((KB STRUCTURE-TUPLE-KB))
            (STRUCTURE-TUPLE-KB-FOO KB)))</PRE>"
  `(progn
    ,@body
    ,@(loop for news-and-olds in substitution-alists
	    append (substitute-all-within-sexpression
		    news-and-olds body))))

;------------------------------------------------------------------------------

(defun define-funarg-handler
    (funarg internal-name arguments-to-kb-specialize arg-names)
  `(defmethod ,internal-name
    ,(loop for arg in arg-names
	   collect (cond ((member arg arguments-to-kb-specialize)
			  (list arg 'kb))
			 ((eq arg funarg)
			  (list 'procedure 'procedure))
			 (t arg)))
    (let ((environment
	   (append (procedure-environment procedure)
		   (list ,@(loop for arg in arg-names
				 unless (eq arg funarg)
				 collect `(list ',arg ,arg)))))
	  (*bound-vars* '(&args ,@arg-names)))
      (declare (special *bound-vars*))
      (prepare-procedure
       procedure ,(or (first arguments-to-kb-specialize) '*current-kb*))
      (if (procedure-function-object procedure)
	  (progv
	      (mapcar #'first environment)
	      (mapcar #'second environment)
	    (,internal-name
	     ,@(loop for arg in arg-names until (eq arg funarg) collect arg)
	     (procedure-function-object procedure)
	     ,@(loop for args on arg-names
		     until (eq (first args) funarg)
		     finally (return (rest args)))))
	  (let ((expression (procedure-expression procedure))
		    
		(formals (procedure-arguments procedure)))
	    (assert (= (length formals) 1) ()
		    "OKBC Mapping functions must take one argument.  ~
                     It expects ~S"
		    formals)
	    (,internal-name
	     ,@(loop for arg in arg-names until (eq arg funarg) collect arg)
	     #'(lambda (object)
		 (trivial-eval-for-okbc
		  expression
		  (extend-environment-for-args environment formals
					       (list object))))
	     ,@(loop for args on arg-names
		     until (eq (first args) funarg)
		     finally (return (rest args)))))))))

(defmethod internal-name-to-op-name ((thing t))
  nil) ;; stub method
(defmethod op-name-to-internal-name ((thing t))
  nil) ;; stub method

(defun define-procedure-handlers
    (internal-name args arguments-to-kb-specialize
		   potentially-functional-arguments)
  (let ((arg-names (remove-keywords-and-defaults args)))
    (let ((funargs potentially-functional-arguments))
      (if (and funargs
	       (loop for arg in arg-names
		     thereis (member arg arguments-to-kb-specialize)))
	  (loop for funarg in funargs
		collect
		(define-funarg-handler
		    funarg internal-name arguments-to-kb-specialize
		    arg-names))
	  nil))))

;------------------------------------------------------------------------------

;;; Network stuff

(defparameter *write-by-hand-nokbc-methods*
  '(okbc:create-kb
    okbc:get-kbs-of-type
    okbc:openable-kbs
    okbc:goto-kb
    okbc:copy-kb 
    okbc:copy-frame
    okbc:close-connection))

(defun network-okbc-method (name args arguments-to-kb-specialize
				potentially-functional-arguments)
  (let ((internal-name
	 (intern (concatenate 'string (string name) "-INTERNAL") :ok-back))
	(arg-names (remove-keywords-and-defaults args))
	(funargs (list-if-not potentially-functional-arguments)))
    (cond ((and (not (member name *write-by-hand-nokbc-methods*))
		(or (loop for arg in arg-names
			  thereis (member arg arguments-to-kb-specialize))
		    (member 'connection arg-names)))
	   `((defmethods ,internal-name
		 ,(loop for arg in arg-names
			collect (cond ((member arg arguments-to-kb-specialize)
				       (list arg '(network-kb
						   network-structure-kb)))
				      ((member arg funargs)
				       (list arg '(t procedure)))
				      ((eq arg 'connection)
				       '(connection
					 abstract-network-connection))
				      (t arg)))
	       (,(if (member 'connection arg-names)
		     'make-network-call-from-connection
		     'make-network-call)
		,(if (member 'connection arg-names)
		     'connection
		     (first arguments-to-kb-specialize))
		',(progn nil)
		',internal-name
		,@(loop for arg in arg-names
			collect
			(cond (;;(member arg arguments-to-kb-specialize)
			       nil
			       `(list 'find-okbc-kb-of-type
				 (list 'quote
				  (abstract-kb-class-name-from-kb
				   ,(first arguments-to-kb-specialize)))
				 (list 'quote
				  (name ,arg))))
			      ((eq arg 'connection)
			       :__establish-local-connection)
			      (t arg))))))) 
	  (t nil))))


(defun define-network-coercion-forms
    (internal-name arg-names arguments-to-kb-specialize args-with-coercions)
  (let ((coerced
	 (and arguments-to-kb-specialize
	      (coerce-frame-args
	       arg-names (first arguments-to-kb-specialize)
	       (mapcar #'second args-with-coercions) nil))))
    (cond (coerced
	   `((defmethod ,internal-name :around
	      ,(loop for arg in arg-names
		     collect
		     (cond ((eq arg (first arguments-to-kb-specialize))
			    (list arg 'ok-back:network-coercion-mixin))
			   (t (list arg t))))
	      (cond ((or (not (inside-okbc-server-p))
			 *inside-network-coercion-p*)
		     (call-next-method))
		    (t ,@coerced
		       (let ((*inside-network-coercion-p* t))
			 (call-next-method ,@arg-names)))))))
	  (t nil))))

;------------------------------------------------------------------------------

(defun ok-utils:fast-equal (a b)
  "An optimized version of <code>equal</code> that just tests for
   <code>string=</code>ness for strings, and <code>eql</code>ness for all
   other atoms.  This is provided because <code>equal</code> is too slow in
   some implementations for the simple notion of equality usually needed
   by OKBC."
  (declare (optimize (speed 3) (safety 0)
		     #+lucid (compilation-speed 0)
		     #+EXCL (debug 0)))
  (or (eql a b)
      (typecase a
	(cons
	 (and (consp b)
	      (and (fast-equal (first (the cons a)) (first (the cons b)))
		   (fast-equal (rest  (the cons a)) (rest  (the cons b))))))
	(string (and (stringp b) (string= (the string a) (the string b))))
	(otherwise nil))))

(defun length-sensitive-remove-duplicates-equal (list)
  (if (nthcdr 20 list)
      (remove-duplicates-equal-using-trie list)
      (remove-duplicates list :test #'fast-equal)))

(defmacro maybe-trim-values-to-return
    (all-values kb number-of-values kb-local-only-p more-status
		exact-p &rest extra-values)
    `(multiple-value-bind (.values. .more-status.)
      (maybe-trim-values-to-return-internal
       ,all-values ,kb ,number-of-values ,kb-local-only-p ,more-status)
      (values .values. ,exact-p .more-status. ,@extra-values)))

(defun define-number-of-values-method
    (internal-name args arg-names arguments-to-kb-specialize returned-values)
  (if (and (member 'number-of-values args :key 'first-if-list :test #'string=)
	   (not (member internal-name '(ok-back:prefetch-internal
					ok-back:fetch-internal))))
      (let ((kb (first arguments-to-kb-specialize))
	    (kb-local-only-p (find 'kb-local-only-p arg-names
				   :test #'string=)))
	`((defmethod ,internal-name :around
	      (,@(loop for arg in arg-names
		       collect
		       (cond ((eq arg kb)
			      (list arg 'handle-number-of-values-mixin))
			     ((string= arg 'number-of-values)
			      '(number-of-values integer))
			     (t (list arg t)))))
	    :around
	    (multiple-value-bind (all-values exact-p more-status
					     ,@(nthcdr 3 returned-values))
		(call-next-method)
	      (maybe-trim-values-to-return all-values ,kb number-of-values
					   ,kb-local-only-p more-status
					   exact-p
					   ,@(nthcdr 3 returned-values))))))
      nil))

;------------------------------------------------------------------------------

(defmacro with-okbc-cache ((cache multiple-value-p key kb) &body body)
  (let ((with-cache-body
	    `(multiple-value-bind (result found-p trie-node)
	      (get-hybrid-trie-returning-node .key. .cache.)
	      (if found-p
		  ,(if multiple-value-p
		       '(progn
			 (assert (consp result) ()
			  "Consistency error.  Multiple values not found: ~S"
			  result)
			 (values-list result))
		       'result)
		  (multiple-value-bind (new-result run-p)
		      (ok-cache:cache-miss-hook (first .key.) .key. ,kb)
		    (if run-p
			(let ((*ok-to-cache-p* t))
			  ;; Will be set to T by any side-effect either here
			  ;; or on the server side if we're in networked mode.
			  (let ((result-of-run ,(if multiple-value-p
						 `(multiple-value-list
						   (.body.))
						 `(.body.))))
			    (when *ok-to-cache-p*
			      (when (and (not (eq (hybrid-trie-value
						   trie-node)
						  tries:+no-value+))
					 (not (equal (hybrid-trie-value
						      trie-node)
						     result-of-run)))
				(error "Cache was not flushed!  old value was ~
                                        ~S.  New value is ~S, in ~S"
				       (hybrid-trie-value trie-node)
				       result-of-run trie-node))
			      ,@(if multiple-value-p
				    `((when (not (consp result-of-run))
					(error
					 "Consistency error.  ~
                                          Multiple values not found: ~S"
					 result-of-run)))
				    nil)
			      (set-hybrid-trie-value
			       trie-node result-of-run)
			      (ok-cache:cache-fill-hook (first .key.) .key. ,kb
							result-of-run
							,multiple-value-p))
			    ,(if multiple-value-p
				 '(values-list result-of-run)
				 'result-of-run)))
			(progn (when *ok-to-cache-p*
				 (when (and (not (eq (hybrid-trie-value
						      trie-node)
						     tries:+no-value+))
					    (not (equal (hybrid-trie-value
							 trie-node)
							new-result)))
				   (error
				    "Cache was not flushed.  Old value was ~
                                     ~S.  New value is ~S"
				    (hybrid-trie-value trie-node)
				    new-result))
				 ,@(if multiple-value-p
				       `((when (and 
						(not (consp new-result)))
					   (error
					    "Consistency error.  ~
                                             Multiple values not found: ~S"
					    new-result)))
				       nil)
				 (set-hybrid-trie-value trie-node
							   new-result)
				 (ok-cache:cache-fill-hook
				  (first .key.) .key. ,kb
				  new-result ,multiple-value-p))
			       ,(if multiple-value-p
				    '(values-list new-result)
				    'new-result))))))))
    `(flet ((.body. () ,@body))
      (declare (dynamic-extent #+Lucid .body. #-Lucid (function .body.)))
      (if ok-cache:*allow-okbc-caching-p*
	  (let ((allow-p (ok-cache:allow-caching-p ,kb)))
	    (macrolet
		((with-cache () ',with-cache-body))
	      (case allow-p
		(:ephemeral
		 (if (boundp 'ok-cache:*ephemeral-cache*)
		     (let ((.key. ,key)
			   (.cache. ok-cache:*ephemeral-cache*))
		       (with-cache))
		     (let ((ok-cache:*ephemeral-cache*
			    (new-root-hybrid-trie
			     :ephemeral-okbc-cache nil)))
		       (let ((.key. ,key)
			     (.cache. ok-cache:*ephemeral-cache*))
			 (with-cache)))))
		((t) (let ((.key. ,key)
			   (.cache. ,cache))
		       (with-cache)))
		(otherwise (.body.)))))
	  (.body.)))))

(defun define-okbcop-cache-handle-function
  (name internal-name args arg-names values-p)
  `(defun ,name (,@(if values-p '(.values.) nil) ,@args)
    (,internal-name ,@(if values-p '(.values.) nil) ,@arg-names)))

(defmacro export-okbc-symbol (symbol package)
  #+Allegro
  (case comp:*cltl1-compile-file-toplevel-compatibility-p*
    ((nil :warn) `(eval-when (:compile-toplevel :load-toplevel :execute)
		   (export ,symbol ,package)))
    (otherwise `(export ,symbol ,package)))
  #-Allegro
  `(export ,symbol ,package))

(defun define-cache-methods
    (name args arguments-to-kb-specialize returns-multiple-values-p
	  number-of-returned-values causes-side-effects-p)
  (let ((internal-name
	 (intern (concatenate 'string (string name) "-INTERNAL")
		 :ok-back))
	(cached-p-name
	 (intern (concatenate 'string "CACHED-P-" (string name))
		 :ok-cache))
	(cached-p-internal-name
	 (intern (concatenate 'string "CACHED-P-" (string name) "-INTERNAL")
		 :ok-cache))
	(encache-name
	 (intern (concatenate 'string "ENCACHE-" (string name))
		 :ok-cache))
	(encache-internal-name
	 (intern (concatenate 'string "ENCACHE-" (string name) "-INTERNAL")
		 :ok-cache))
	(arg-names (remove-keywords-and-defaults args))
	(supplied-p (supplied-p-ify args)))
    ;; Don't handle mapping functions.  The function will usually be a
    ;; closure, and will cause us to lose, and we really care about
    ;; caching the okbcops that run inside the mapping function, anyway. 
    (cond
      ((or (not arguments-to-kb-specialize)
	   (loop for arg in arguments-to-kb-specialize
		 thereis (not (member arg args :key 'first-if-list)))
	   (let ((s (symbol-name name))
		 (cookie "ENUMERATE-"))
	     (and (> (length s) (length cookie))
		  (string= cookie s :end2 (length cookie)))))
       nil)
      ;; Do not generate cache methods for any okbc op that takes a kb-type.
      ((member 'kb-type arguments-to-kb-specialize :test #'string=) nil)
      ;; Special cases for non-caching.
      ((member name '(implement-with-kb-io-syntax okbc:kb-modified-p)
	       :test #'string=) nil)
      (causes-side-effects-p
       (flet ((side-effect-method (class)
	        (loop for karg in (if (eq t causes-side-effects-p)
				      arguments-to-kb-specialize
				      (list-if-not causes-side-effects-p))
		      collect
		      `(defmethod ,internal-name :around
			 ,(loop for arg in arg-names
				collect
				(cond ((eq arg karg)
				       (list arg class))
				      (t (list arg t))))
			 (if (eq (ok-cache:caching-policy ,karg) :defensive)
			     (progn
			       (when ok-cache:*allow-okbc-caching-p*
				 (ok-cache:flush-cache ,karg))
			       (let ((ok-cache:*allow-okbc-caching-p* nil))
				 (call-next-method)))
			     (call-next-method))))))
	 (append (loop for karg in arguments-to-kb-specialize
		       collect
		       `(defmethods ,internal-name :before
			 ,(loop for arg in arg-names
				collect
				(cond ((eq arg karg)
				       (list arg '(kb structure-kb)))
				      (t (list arg t))))
			 (when (boundp '*ok-to-cache-p*)
			   (setq *ok-to-cache-p* nil))
			 ,@(when (or (not (member name '(okbc:copy-kb
							 okbc:copy-frame)))
				     (string-equal karg "TO-KB"))
			     `((setf (kb-has-been-modified-p
				      ,karg) t)))))
	       (if (first (remove 'kb-type arguments-to-kb-specialize
				  :test #'string=))
		   (append (side-effect-method 'caching-mixin)
			   (side-effect-method 'caching-structure-kb))
		   nil))))
      (t (flet ((non-side-effect-method (class)
		  `((defmethod ,internal-name :around
		      ,(loop for arg in arg-names
			     collect
			     (cond ((eq arg (first arguments-to-kb-specialize))
				    (list arg class))
				   (t (list arg t))))
		      (with-okbc-cache
			  ((ok-cache:cache ,(first arguments-to-kb-specialize))
			   ,returns-multiple-values-p
			   (list ',internal-name ,@arg-names)
			   ,(first arguments-to-kb-specialize))
			(call-next-method)))))
		(cached-p-forms ()
		  (append
		   `((export-okbc-symbol
		      (intern ,(string cached-p-name) :ok-cache)
		      :ok-cache)
		     (export-okbc-symbol
		      (intern ,(string cached-p-internal-name)
		       :ok-cache)
		      :ok-cache))
		   (list (define-okbcop-cache-handle-function
			     cached-p-name cached-p-internal-name args
			     arg-names nil))
		   ;; remove progn
		   (rest (define-defokbcop-compiler-macro
			     cached-p-name cached-p-internal-name nil
			     supplied-p nil nil nil arg-names nil
			     arguments-to-kb-specialize))
		   `((defmethods ,cached-p-internal-name
			 ,(loop for arg in arg-names
				collect
				(cond ((eq arg
					   (first arguments-to-kb-specialize))
				       (list arg '(caching-mixin
						   caching-structure-kb)))
				      (t (list arg t))))
		       (ok-cache:cache-entry-found-p
			(ok-cache:cache ,(first arguments-to-kb-specialize))
			(list ',internal-name ,@arg-names)
			,(first arguments-to-kb-specialize)))
		     (defmethod ok-utils:okbcop-args
			 ((okbcop (eql ',cached-p-name)))
		       (values ',args '(boolean) ',arg-names)))))
		(encache-forms ()
		  (append
		   `((export-okbc-symbol
		      (intern ,(string encache-name) :ok-cache)
		      :ok-cache)
		     (export-okbc-symbol
		      (intern ,(string encache-internal-name) :ok-cache)
		      :ok-cache))
		   (list (define-okbcop-cache-handle-function
			     encache-name encache-internal-name args
			     arg-names t))
		   ;; remove progn
		   (rest (define-defokbcop-compiler-macro
			     encache-name encache-internal-name nil
			     (cons '.values. supplied-p)
			     nil nil nil (cons '.values. arg-names) nil
			     arguments-to-kb-specialize))
		   `((defmethods ,encache-internal-name
			 (.values.
			  ,@(loop
			     for arg in arg-names
			     collect
			     (cond ((eq arg
					(first arguments-to-kb-specialize))
				    (list arg '(caching-mixin
						caching-structure-kb)))
				   (t (list arg t)))))
		       (encache
			.values. ,returns-multiple-values-p
			(ok-cache:cache ,(first arguments-to-kb-specialize))
			(list ',internal-name ,@arg-names)
			,(first arguments-to-kb-specialize)
			,@(if returns-multiple-values-p
			      (progn
				(assert (and (numberp number-of-returned-values)
					     (> number-of-returned-values 1)))
				(list number-of-returned-values))
			      nil)))
		     (defmethod ok-utils:okbcop-args
			 ((okbcop (eql ',encache-name)))
		       (values ',(cons '.values. args) nil
			       ',(cons '.value. arg-names)))))))
	   (if (first (remove 'kb-type arguments-to-kb-specialize
			      :test #'string=))
	       (append (non-side-effect-method 'caching-mixin)
		       (non-side-effect-method 'caching-structure-kb)
		       (cached-p-forms)
		       (encache-forms))
	       nil))))))

;==============================================================================

;;; Plundered from TI source code.  Rewrite this if anyone ever gives
;;; us a hard time.

(defmacro ok-utils:with-timeout ((duration . timeout-forms) &body body)
  "Execute <code>body</code> with a timeout set for a <code>duration</code> of
   a second from time of entry.
   If the timeout elapses while <code>body</code> is still in progress,
   the <code>timeout-forms</code> are executed and their values returned, and
   whatever is left of <code>body</code> is not done, except for its
   <code>unwind-protect</code>s.
   If <code>body</code> returns, is values are returned and the timeout
   is cancelled.   The timeout is also cancelled if <code>body</code> throws
   out of the form."
  #-(or Lucid EXCL Harlequin-Common-Lisp)
  (cerror "Go ahead, anyway" "Need to implement with-timeout")
  `(let ((.proc. (prepare-timeout #+Lucid *current-process*
				  #+(or EXCL Harlequin-Common-Lisp)
				  mp:*current-process*
				  #-(or Lucid EXCL Harlequin-Common-Lisp)
				  nil ;; add something here!!
				  ,duration )))
     (handler-case
	 (unwind-protect
	   (progn . ,body)
	   (remove-timer .proc.))
       (timeout ()
	. ,timeout-forms))))

(defvar *timer-process* nil)
(defvar *free-timers* nil)
(defvar *timer-queue* nil)

(defstruct (timer-item (:type list))
  time-for-wakeup
  next-item
  process-id
  action)

(defun get-timer (time process-id action)
  (ok-utils:without-scheduling
    (if *free-timers*
	(let ((item
		(prog1 *free-timers*
		       (setf *free-timers*
			     (timer-item-next-item *free-timers*)))))
	  (setf (timer-item-action item) action
		(timer-item-process-id item) process-id
		(timer-item-time-for-wakeup item) time)
	  item)
	(make-timer-item :time-for-wakeup time
			 :process-id process-id
			 :action action))))

(defun enqueue-timer (timer-item)
  (ok-utils:without-scheduling
    (if  (null *timer-queue*)
	 (progn
	   (setf *timer-queue* timer-item)
	   (setf (timer-item-next-item timer-item) nil))
	 (let ((item *timer-queue*)
	       (trailer nil)
	       (time (timer-item-time-for-wakeup timer-item)))
	   (loop
	     (cond ((or (null item)
			(< time (timer-item-time-for-wakeup item)))
		    (setf (timer-item-next-item timer-item) item)
		    (if trailer
			(setf (timer-item-next-item trailer) timer-item)
			(setf *timer-queue* timer-item))
		    (return))
		   (t (psetq item (timer-item-next-item item)
			     trailer item))))))))

(defun timer-init ()
  (setf *timer-queue* nil
	*free-timers* nil)
  #+Harlequin-Common-Lisp
  (when (not mp:*current-process*) (mp:initialize-multiprocessing))
  (setf *timer-process*
	#+Lucid
	(make-process :name "timer-process"
		      :function 'timer-top-level :priority 35.)
	#+EXCL
	(mp:process-run-function '(:name "timer-process"
				   :priority 35)
				 'timer-top-level)
	#+Harlequin-Common-Lisp
	(mp:process-run-function "timer-process"
				 '(:priority 35)
				 'timer-top-level)
	#-(or Lucid EXCL Harlequin-Common-Lisp)
	(progn (cerror "Go ahead, anyway"
		       "Need to implement timer process creation!")
	       nil))
  #+Lucid (restart-process *timer-process*)
  #+(or EXCL Harlequin-Common-Lisp) (mp:process-reset *timer-process*)
  #-(or Lucid EXCL Harlequin-Common-Lisp)
  (cerror "Go ahead, anyway"
	  "Need to implement process reset for timer process"))

(defun prepare-timeout (process duration)
  (let ((item (get-timer (+ (get-universal-time) duration)
			 process 'timeout-action)))
    (unless (and (typep *timer-process*
			#+Lucid 'process
			#+(or Harlequin-Common-Lisp EXCL) 'mp:process
			#-(or Lucid EXCL Harlequin-Common-Lisp)
			(progn (cerror "Go ahead, anyway"
				       "Need to specify type for process")
			       'null))
		 (#+Lucid process-active-p
		  #+(or EXCL Harlequin-Common-Lisp) mp::process-active-p
		  #-(or Lucid EXCL Harlequin-Common-Lisp)
		  (lambda (x)
		    (declare (ignore x))
		    (cerror "Go ahead, anyway"
			    "Need to implement process-active-p")
		    nil)
		  *timer-process*))
      (timer-init))
    (enqueue-timer item)
    item))

(defun pop-timer ()
  ;;Remove first timer off *timer-queue* and return it to *free-timers*.
  (ok-utils:without-scheduling
    (when *timer-queue*
      (prog1 *timer-queue*
	     (psetf *timer-queue* (timer-item-next-item *timer-queue*)
		    (timer-item-next-item *timer-queue*) *free-timers*
		    *free-timers* *timer-queue*)))))

(defun time-wait ()
  ;;wait function for timer-process.
  (and *timer-queue*
       (not (< (get-universal-time)
			(timer-item-time-for-wakeup *timer-queue*)))))

(defun timer-top-level ()
  ;;top-level function for timer-process
  (loop
    (#+Lucid process-wait
     #+(or EXCL Harlequin-Common-Lisp) mp:process-wait
     #-(or Lucid EXCL Harlequin-Common-Lisp)
     (lambda (whostate function)
       (declare (ignore whostate function))
       (cerror "Go ahead, anyway" "Need to implement process-wait"))
     "timer-wait" #'time-wait)
    (let ((item (pop-timer)))
	  (funcall (timer-item-action item) (timer-item-process-id item))
	  (setf (timer-item-process-id item ) nil))))

(define-condition timeout (condition) nil)

(defparameter timeout-instance (make-condition 'timeout))

(defun timeout-action (process)
  (#+Lucid interrupt-process
   #+(or EXCL Harlequin-Common-Lisp) mp:process-interrupt
   #-(or Lucid EXCL Harlequin-Common-Lisp)
   (lambda (process function &rest args)
     (declare (ignore function args))
     (cerror "Go ahead, anyway" "Need to implement interrupt-process")
     (apply function args))
   process 'error timeout-instance))

(defun remove-timer (item-to-remove)
  (ok-utils:without-scheduling
    (when *timer-queue*
      (let ((item *timer-queue*)
	    (trailer nil))
	(loop
	  (cond ((null item)
		 (return))
		((eq item item-to-remove)
		 (if trailer
		     (setf (timer-item-next-item trailer)
			   (timer-item-next-item item-to-remove))
		     (setf *timer-queue*
			   (timer-item-next-item item-to-remove)))
		 (setf (timer-item-next-item  item-to-remove) *free-timers*
		       *free-timers* item-to-remove
		       (timer-item-process-id item-to-remove) nil)
		 (return))
		(t (psetq item (timer-item-next-item item)
			  trailer item))))))))


