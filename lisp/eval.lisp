(in-package :ok-kernel)

(defparameter *all-procedures* (make-hash-table :test #'equal))
(defvar *compile-named-procedures-p* t)

(defmethod print-object ((fun procedure) (stream t))
  (print-unreadable-object (fun stream :identity t :type t)
     (when (procedure-name fun)
       (format stream "~A " (procedure-name fun)))
     (format stream "~A" (procedure-arguments fun))))

(defun intern-procedure
    (&key (name nil) (arguments nil) (expression nil) (environment nil)
	  (function-object nil) (kb (current-kb)))
  "Takes the arguments that are passed to <code>create-procedure</code>
   and interns a procedure object to represent that procedure."
  (let ((key (list name arguments expression environment)))
    (let ((match (gethash key *all-procedures*)))
      (if match
	  (progn (when function-object
		   (setf (procedure-function-object match)
			 function-object))
		 (values match nil))
	  (let ((new (make-procedure
		      :name               name
		      :arguments          (if (stringp arguments)
					      nil
					      arguments)
		      :arguments-string   (if (stringp arguments)
					      arguments
					      nil)
		      :expression         (if (stringp expression)
					      nil
					      (substitute-internals
					       expression))
		      :expression-string  (if (stringp expression)
					      expression
					      nil)
		      :environment        (if (stringp environment)
					      nil
					      environment)
		      :environment-string (if (stringp environment)
					      environment
					      nil)
		      :function-object function-object
		      :as-sexpressions-p (and (listp arguments)
					      (listp expression)
					      (listp environment))
		      :interpreted-wrt-kb nil)))
	    (setf (gethash key *all-procedures*) new)
	    (when name
	      (setf (gethash (string-upcase (okbc-string name))
			     (or (and kb (name-to-procedure-table kb))
				 *name-to-procedure-table*))
		    new))
	    (values new t))))))

;==============================================================================

(defun simplify-expanded-form (form looking-for &optional (parent nil))
  (if (consp form)
      (if (eq (first form) looking-for)
	  (simplify-expanded-form-1 parent)
	  (loop for x in form
		for res = (simplify-expanded-form x looking-for form)
		when res return res))
      nil))

(defun simplify-expanded-form-1 (form)
  (if (eq 'let* (first form))
      (simplify-expanded-form-2
       (destructuring-bind (bindings expression) (rest form)
	 ;; (print :=============)
	 (let ((necessary-bindings
		(loop for b on bindings
		      for binding = (first b)
		      for (sym var) = binding
		      for gensym = (first binding)
		      for arg in (rest expression)
		      ;; for remaining-args on (rest expression)
		      until (not (eq arg gensym))
		      ;; do (print (list :gensym gensym :arg arg :var var :rest remaining-args))
		      when (is-in-tree gensym
				       (mapcar #'second (rest bindings)))
		      collect (list (intern (string sym) :okbc)
				    (substitute-gensyms var)))))
	   (let ((remaining-bindings
		  (loop with b = bindings
			for binding = (first b)
			for gensym = (first binding)
			for arg in (rest expression)
			until (or (not b) (not (eq arg gensym)))
			do (pop b)
			finally (return (loop for (sym var) in b
					      collect
					      (list (intern (string sym)
							    :okbc)
						    var))))
		  #+ignore ;; this is the verison that tickles a bug in HCL
		  (loop for b on bindings
			for binding = (first b)
			for gensym = (first binding)
			for arg in (rest expression)
			until (not (eq arg gensym))
			finally (return (loop for (sym var) in b
					      collect
					      (list (intern (string sym)
							    :okbc)
						    var))))))
	     (list (first form)
		   (append necessary-bindings remaining-bindings)
		   (cons (first expression)
			 (append (loop for b on bindings
				       for binding = (first b)
				       for (gensym value) = binding
				       for arg in (rest expression)
				       while (eq arg gensym)
				       collect
				       (substitute-gensyms
					(if (is-in-tree
					     gensym
					     (mapcar #'second
						     (rest bindings)))
					    gensym
					    value)))
				 (mapcar #'first remaining-bindings))))))))
      (continuable-error
	 "Cannot interpret/simplify form ~S" form)))

(defun substitute-gensyms (tree)
  (if (consp tree)
      (cons (substitute-gensyms (first tree))
	    (substitute-gensyms (rest  tree)))
      (if (and (symbolp tree) (not (symbol-package tree)))
	  (intern (symbol-name tree) :okbc)
	  tree)))

(defun simplify-expanded-form-2 (form)
  (if (eq 'let* (first form))
      (destructuring-bind (bindings expression) (rest form)
	(if (not bindings)
	    expression
	    form))
      (continuable-error
	"Cannot interpret/simplify form ~S" form)))

(defun substitute-internals (form)
  (typecase form
    (cons
     (let ((name (and (symbolp (first form))
		      (gethash (symbol-name (first form)) *all-okbcops-ht*))))
       (if name
	   (let ((args (rest form)))
	     (let ((expander (body-expander-function name)))
	       (continuable-assert expander ()
				   "Cannot find body expander function for ~S"
				   name)
	       (if expander
		   (let ((new-args
			  (loop for x in args
				collect (substitute-internals x))))
		     (let ((new-expr
			    (funcall expander (cons name new-args))))
		       (simplify-expanded-form
			new-expr (intern-okbcop-name name) nil)))
		   (continuable-error
		      "Cannot expand call to ~S" name))))
	   (if (and (symbolp (first form))
		    (string= 'procedure (first form)))
	       (trivial-eval-for-okbc (cons 'procedure (rest form))
				     nil)
	       (loop for x in form collect (substitute-internals x))))))
    (otherwise form)))

(defun default-create-procedure (name arguments body environment kb)
  (let ((name (if (or (stringp name) (consp name))  nil name))
	(args (if (or (stringp name) (consp name)) name arguments))
	(body (if (or (stringp name) (consp name))
		  (cons arguments body)
		  body)))
    (cond ((or (stringp args)
	       (stringp body)
	       (and (consp body) (= (length body) 1) (stringp (first body))))
	   (continuable-assert
	    (and (= (length body) 1) (stringp (first body))) ()
	    "When you specify a string for the args to a ~
             procedure, the body must also be a string.")
	   (intern-procedure
	    :name name :arguments args :expression (first body)
	    :environment nil :function-object nil :kb kb))
	  (t (let ((environment
		    (append environment
			    (second (member '&environment args)))))
	       (let ((args (loop for arg in args
				 until (string= arg '&environment)
				 collect (substitute-global-args arg))))
		 (let ((substituted
			(substitute-internals
			 (if (and (rest body) (consp (first body)))
			     (cons :progn body)
			     (first body)))))
		   (let ((expanded
			  (let ((*bound-vars*
				 (append
				  args
				  '(&args)
				  (locally
				      (declare (special *bound-vars*))
				    *bound-vars*))))
			    (declare (special *bound-vars*))
			    (expand-okbc-expression substituted))))
		     (continuable-assert
		      (listp environment) ()
		      "procedure environment must be of the form ~
                    ((sym value) ...), not ~S" environment)
		     (loop for x in environment
			   do (continuable-assert
			       (and (consp x) (= (length x) 2)
				    (symbolp (first x)))
			       ()
			       "Each environment entry must be of the form ~
                          (sym value), not ~S"
			       x))
		     (intern-procedure
		      :name name
		      :arguments args
		      :expression substituted
		      :environment environment
		      :kb kb
		      :function-object
		      (compile nil
			       #+Lucid
			       `(lcl::named-lambda ,name (,@args)
				 (declare (special ,@args))
				 ,expanded)
			       #-Lucid
			       `(lambda (,@args)
				 (declare (special ,@args))
				 ,expanded)))))))))))


(defmacro ok-utils:procedure (name arguments &body body)
  "Defines a procedure.  The syntax can be of two forms:
    <PRE>
     (procedure (x y z) .....)
     (procedure name1 (x y z) .....)</PRE>
   The former defines an anonymous function (like lambda in Lisp);
   the latter causes a function named <code>name</code> to be defined.  A
   procedure is a legal argument to any OKBC operator in
   a position that expects a function.
   For example,<PRE>
    (call-procedure
      #'(lambda (frame) (get-frame-pretty-name frame :kb kb))
      :kb kb :arguments (list my-frame))</PRE>
   and<PRE>
    (call-procedure
      (procedure (frame) (get-frame-pretty-name frame :kb kb))
      :kb my-kb :arguments (list my-frame))</PRE>
   are semantically identical.  Procedures and lambda expressions differ
   as follows:
   <OL>
   <LI>All bindings in procedures are dynamic, not lexical.
   <LI>Only a restricted set of operations is available in
   procedures.
   <LI>Lambda defines a <i>lexical</i> closure over any free references;
   a <code>procedure</code> defines a <i>dynamic</i> closure over its free
   references.  The environment of the procedure is
   pre-filled with bindings for the names of the arguments to
   the OKBC operator in which it is being executed.  In the above
   case, <code>okbc:call-procedure</code> takes arguments <code>KB</code>,
   <code>arguments</code>,and <code>kb-local-only-p</code>.
   These arguments will take on the values <code>my-kb</code>,
   <code>(my-frame)</code>,
   and <code>nil</code> (the default), respectively.
   <LI>Lambda expressions are only meaningful within the Lisp system
   in which the OKBC system is running.  Procedures are
   executable on any (possibly network-connected) OKBC KB.
   <LI>Procedures are package-insensitive in all respects
   other than quoted constants.
   </OL>

   The <code>procedure</code> form allows an alternate form in which its
   <code>arguments</code> and <code>body</code> arguments are expressed as
   strings.  This is useful
   for non-lisp OKBC clients in which it may be inconvenient to build
   the list structure for a procedure body.  Thus,
   <code>(procedure (x y) (list x y))</code>
   is functionally equivalent to
   <code>(procedure \"(x y)\" \"(list x y)\")</code>.<P>

   To build a dynamic closure for a procedure, we
   must explicitly construct the necessary environment.  For
   example, if we want a procedure that closes over
   some values <code>&lt;&lt;val1&gt;&gt;</code> and
   <code>&lt;&lt;val2&gt;&gt;</code>, to which we
   want to refer by using the names <code>var1</code> and <code>var2</code>,
   we would use the following syntax:<PRE>
   (procedure (a b &envirionment ((var1 &lt;&lt;val1&gt;&gt;)
                                  (var2 &lt;&lt;val2&gt;&gt;)))
     ...Some expressions mentioning a, b, var1, and var2...)</PRE>
   Note that  persistent side effects to <code>&lt;&lt;var1&gt;&gt;</code>
   and <code>&lt;&lt;var2&gt;&gt;</code>
   cannot be made from within the procedure.<P>

   The end-of-line comment character within procedures is
   the semicolon.  Thus, we can say the following:<PRE>
   (procedure foo (x y)
     ;; This defines the function FOO, which takes two arguments, x and y
     .....)</PRE>"
  (let ((name (if (or (stringp name) (consp name))  nil name))
	(args (if (or (stringp name) (listp name)) name arguments))
	(body (if (or (stringp name) (listp name))
		  (cons arguments body)
		  body)))
    (etypecase args
      (string
       (continuable-assert
	(and (= (length body) 1) (stringp (first body))) ()
	"When you specify a string for the args to a ~
         procedure, the body must also be a string.")
       `(intern-procedure
	 :name ',name :arguments ,args :expression ,(first body)
	 :environment nil :function-object nil))
      (list
       (let ((environment (second (member '&environment args))))
	 (let ((args (loop for arg in args
			   until (string= arg '&environment)
			   collect arg)))
	   (let ((substituted
		  (substitute-internals
		   (if (rest body) (cons :progn body) (first body)))))
	     (let ((expanded (let ((*bound-vars*
				    (append
				     args
				     (locally (declare (special *bound-vars*))
				       *bound-vars*))))
			       (declare (special *bound-vars*))
			       (expand-okbc-expression substituted))))
	       `(let ((.env. ,environment))
		 (continuable-assert (listp .env.) ()
		  "procedure environment must be of the form ~
                   ((sym value) ...), not ~S" .env.)
		 (loop for x in .env.
		  do (continuable-assert (and (consp x) (= (length x) 2)
				      (symbolp (first x)))
		      () "Each environment entry must be of the form ~
                          (sym value), not ~S"
		      x))
		 (intern-procedure
		  :name ',name
		  :arguments ',args
		  :expression ',substituted
		  :environment ,environment
		  :function-object
		  #'(lambda (,@args)
		      (declare (special ,@args))
		      ,expanded)))))))))))

(defmethod prepare-procedure ((procedure t) (kb t) &optional (force-p nil))
  (when (or force-p
	    (not (procedure-as-sexpressions-p procedure))
	    (and (procedure-interpreted-wrt-kb procedure)
		 (not (eq kb (procedure-interpreted-wrt-kb
			      procedure))))
	    ;; Just in case we are not compiled
	    (and *compile-named-procedures-p*
		 (procedure-name procedure)
		 (not (procedure-function-object procedure))))
    (with-kb-io-syntax (:kb kb)
      (let ((arguments
	     (if (stringp (procedure-arguments-string procedure))
		 (safely-read-from-string
		  (procedure-arguments-string procedure))
		 (procedure-arguments procedure)))
	    (expression
	     (if (stringp
		  (procedure-expression-string procedure))
		 (loop with next-index = 0
		       with form = nil
		       do (multiple-value-setq (form next-index)
			    (safely-read-from-string
			     (procedure-expression-string
			      procedure)
			     nil :_eof :start next-index))
		       until (eq :_eof form)
		       collect form)
		 (procedure-expression procedure)))
	    (environment
	     (if (stringp (procedure-environment-string
			   procedure))
		 (safely-read-from-string
		  (procedure-environment-string procedure))
		 (procedure-environment procedure))))
	(let ((expanded (runtime-expand-procedure
			 (procedure-name procedure)
			 arguments expression environment kb)))
	  (setf (procedure-arguments procedure)
		(procedure-arguments expanded))
	  (setf (procedure-expression procedure)
		(procedure-expression expanded))
	  (setf (procedure-environment procedure)
		(procedure-environment expanded))
	  (setf (procedure-function-object procedure)
		(procedure-function-object expanded))
	  (setf (procedure-as-sexpressions-p procedure) t)
	  (setf (procedure-interpreted-wrt-kb procedure) kb))))))


;==============================================================================

(defvar *bound-vars* nil)

(defun extend-environment-for-args (environment formals actuals)
  (if formals
      (cons (list (first formals) (first actuals))
	    (extend-environment-for-args
	     environment (rest formals) (rest actuals)))
      environment))

(defmethod trivial-eval-for-okbc ((expression cons) environment)
  (trivial-eval-for-okbc-cons (first expression) expression environment))

(defmethod trivial-eval-for-okbc ((expression number) (environment t))
  expression)

(defmethod trivial-eval-for-okbc ((expression string) (environment t))
  expression)

(defmethod trivial-eval-for-okbc
    ((expression procedure) (environment t))
  expression)

(defmethod trivial-eval-for-okbc ((expression symbol) environment)
  (if (keywordp expression)
      (let ((string (symbol-name expression)))
	(if (loop for index from 0 below (length string)
		  for char = (schar string index)
		  for code = (char-code char)
		  thereis (and (>= code #.(char-code #\a))
			       (<= code #.(char-code #\z))))
	    ;; Then we are mixed case, so upcase.
	    (intern (string-upcase string) *keyword-package*)
	    expression))
      (let ((entry (assoc expression environment :test #'string-equal)))
	(cond (entry (second entry))
	      ((string-equal expression T) t)
	      ((string-equal expression NIL) nil)
	      ((string-equal expression "TRUE") t)
	      ((string-equal expression "FALSE") nil)
	      ((boundp expression) (symbol-value expression))
	      (*unbound-variable-eval-hook*
	       (funcall *unbound-variable-eval-hook* expression environment))
	      (t (continuable-error
		  "~S is unbound.  The known bindings are ~{~%     ~S~}"
		  expression environment))))))

(defun check-length (expression length)
  (continuable-assert (= (length expression) length) ()
		      "Expression ~S must be of length ~D" expression length))

(defun check-length-exceeds (expression length)
  (continuable-assert (> (length expression) length) ()
		      "Expression ~S must be of length greater than ~D"
		      expression length))

(defparameter *all-okbc-procedure-evaluators* nil)

;(loop for sym in '(get-kbs)
;      do (setf (gethash sym *acceptable-okbcops-for-call-procedure*) t))

(defun ok-utils:split-into-lines (string)
  "Given a <code>string</code>, splits it into a list of strings, one for
   each line in the original source string."
  (loop for nl-index = (position #\newline string :test #'char=)
	until (not string)
	collect (if nl-index
		    (subseq string 0 nl-index)
		    string)
	do (setq string
		 (if nl-index
		     (subseq string (+ nl-index 1))
		     nil))))

(defun print-string-flushed-left (doc stream &optional (indent "         "))
  (let ((lines (split-into-lines doc)))
    (loop for line in lines
	  do (format stream "~%~A~A" indent
		     (string-trim '(#\space #\tab) line)))))

(defun latex-print-string-flushed-left (doc stream)
  (let ((lines (split-into-lines doc)))
    (loop
     with verbatim-indent = nil
     for line in lines
     do
     (cond
       ((and (not verbatim-indent)
	     (setq verbatim-indent (search "\\begin{verbatim}" line)))
	(format stream "~%~a" 	(string-trim '(#\space #\tab) line)))
       ((and verbatim-indent
	     (search "\\end{verbatim}" line))
	(setq verbatim-indent nil)
	(format stream "~%~a" 	(string-trim '(#\space #\tab) line)))
       (verbatim-indent
	(format stream "~%~a"
	 (subseq line
		 (min verbatim-indent
			  (or
			      (position-if-not
			       #'(lambda (c) (char= c #\space)) line)
			      0)))))
       (t
	(format stream "~%~a" (string-trim '(#\space #\tab) line)))))))

(defun document-procedure-evaluators (&optional (stream *standard-output*))
  (let ((sorted (sort (copy-list *all-okbc-procedure-evaluators*)
		      #'string-lessp :key #'prin1-to-string))
	(okbc-sorted
	 (sort (let ((l nil))
		 (maphash #'(lambda (k v)
			      (declare (ignore v))
			      (when (not (member
					  k *all-okbc-procedure-evaluators*))
				(push k l)))
			  *acceptable-okbcops-for-call-procedure*)
		 l)
	       #'string-lessp
	       :key #'prin1-to-string)))
    (with-standard-io-syntax
	(let ((*print-readably* nil))
	  (format stream
		  "~&Non OKBC Operations handled by procedures:")
	  (loop for f in sorted
		for doc? = (gethash f *acceptable-okbcops-for-call-procedure*)
		for doc = (cond ((stringp doc?) doc?)
				(doc? (documentation f 'function))
				(t nil))
		do (format stream "~%     ~A" f)
		when (stringp doc)
		do (print-string-flushed-left doc stream))
	  (format stream "~3%  Standard OKBC operators:")
	  (loop for f in okbc-sorted
		when (and (symbolp f) (eq (symbol-package f) *okbc-package*))
		do (format stream "~%     ~A" f))
	  (format stream "~3%  OKBC extension operators:")
	  (loop for f in okbc-sorted
		for s = (and (symbolp f)
			     (not (eq (symbol-package f) *okbc-package*))
			     (find-symbol (symbol-name f) *okbc-package*))
		for doc = (and s (ignore-errors (documentation s 'function)))
		when (not (and (symbolp f)
			       (eq (symbol-package f) *okbc-package*)))
		do (format stream "~%     ~A" f)
		(when (stringp doc)
		  (let ((lines (split-into-lines doc)))
		    (loop for line in lines
			  do (format stream "~%         ~A"
				     (string-trim '(#\space #\tab)
						  line))))))))))

(defparameter *latex-cannot-be-in-lr-mode*
  '("<" "<=" ">" ">=" ))

(defun lisp-to-latex-string (thing)
  (if (member thing  *latex-cannot-be-in-lr-mode* :test #'string-equal)
      (concatenate 'string "{\\tt " (string thing) " }")
      thing))

(defun document-procedure-evaluators-latex
    (&optional (stream *standard-output*))
  (let ((sorted (sort (copy-list *all-okbc-procedure-evaluators*)
		      #'string-lessp :key #'princ-to-string)))
    (with-standard-io-syntax
	(let ((*print-readably* nil))
	  (format stream
	   "~&%% Non OKBC Operations handled by procedures:~%")
;          (format stream
;           "~&\\newcommand{\\code}[1]{\\mbox{\\tt #1}}~%")
	  (loop for f in sorted
		for doc? = (gethash f *acceptable-okbcops-for-call-procedure*)
		for doc = (cond ((stringp doc?) doc?)
				(doc? (documentation f 'function))
				(t nil))
		do
		(format stream "~%\\begin{okbcfspec}{~(~a~)}"
			(lisp-to-latex-string f) )
		when (stringp doc)
		do ;; (print-string-flushed-left doc stream "")
		(latex-print-string-flushed-left doc stream)
		do
		(format stream "~%\\end{okbcfspec}~%"))))))
	  

(defmacro ok-utils:def-trivial-eval-for-okbc-cons
    ((&rest args) &key doc-string body expander)
  "This macro is used to define handlers for the OKBC procedure language
   for list (cons) expressions beginning with a particular operator.  The macro
   defines both an expander to use in the source expansion of the operator by
   the procedure language compiler, and a body form to use in the procedure
   language interpreter.<p>

   <code>Doc-string</code> is a TeX doc string for the operator.<br>
   <code>Body</code> is the code body to use when interpreting the
   expression.<br>
   <code>Expander</code> is the expander form to use when compiling a reference
   to this form.<br>
   For example, (doc string omitted for clarity)<PRE>
   (def-trivial-eval-for-okbc-cons
       ((key (eql :and)) (expression cons) environment)
       :body (loop for arg in (rest expression)
                   always (trivial-eval-for-okbc arg environment))
       :expander `(and ,@(loop for arg in (rest expression)
                               collect (expand-okbc-expression arg))))</PRE>
   defines the <code>:and</code> operator."
  (assert (and body expander) ()
	  "You must supply both a body and an expander for ~S" args)
  (let ((key (second (first args))))
    `(progn ,@(if (and (consp key) (eq 'eql (first key)))
		  `((pushnew ,(second key) *all-okbc-procedure-evaluators*)
		    (setf (gethash ,(second key)
			   *acceptable-okbcops-for-call-procedure*)
		     ,(or doc-string t)))
		  nil)
      ,(if (and (consp body) (consp (first body)))
	   `(defmethod trivial-eval-for-okbc-cons (,@args) ,@body)
	   `(defmethod trivial-eval-for-okbc-cons (,@args) ,body))
      (defmethod expand-okbc-expression-cons (,@(butlast args)) ,expander))))

(defmacro ok-utils:def-trivial-no-args
    (name lisp-operator &key (doc-string nil))
  "This macro is used to define simple no arg operators in the procedure
   language.  For example,<PRE>
   (def-trivial-no-args :current-kb current-kb
       :doc-string \"Returns the current KB.\")</PRE>
   defines the <code>:current-kb</code> operator (OKBC procedure language
   operators are named by keywords) as the Lisp function
   <code>current-kb</code>.
   The <code>doc-string</code> is a piece of TeX source describing the
   operator."
  (let ((expander-body `(list ',lisp-operator)))
    `(def-trivial-eval-for-okbc-cons
      ((key (eql ,name)) (expression cons) (environment t))
      ,@(if doc-string (list :doc-string doc-string) nil)
      :body (progn (check-length expression 1) (,lisp-operator))
      :expander (progn (check-length expression 1) ,expander-body))))

(defmacro ok-utils:def-trivial-monadic
    (name lisp-operator &key (doc-string nil))
  "This macro is used to define simple monadic operators in the procedure
   language.  For example,<PRE>
   (def-trivial-monadic :first first
       :doc-string \"The first element of a list.\\\\\\\\
                     \\\\code{(first '(a b c)) = A}\\\\\\\\
                     \\\\code{(first NIL) = NIL}\")</PRE>
   defines the <code>:first</code> operator (OKBC procedure language
   operators are named by keywords) as the Lisp function <code>first</code>.
   The <code>doc-string</code> is a piece of TeX source describing the
   operator."
  (let ((expander-body
	 `(list ',lisp-operator
	        (expand-okbc-expression (second expression)))))
    `(def-trivial-eval-for-okbc-cons
      ((key (eql ,name)) (expression cons) environment)
      ,@(if doc-string (list :doc-string doc-string) nil)
      :body (progn (check-length expression 2)
		   (,lisp-operator
		    (trivial-eval-for-okbc (second expression) environment)))
      :expander (progn (check-length expression 2)
		       ,expander-body))))

(defmacro ok-utils:def-trivial-diadic
    (name lisp-operator &key (doc-string nil))
  "This macro is used to define simple diadic operators in the procedure
   language.  For example,<PRE>
   (def-trivial-diadic :+ +
       :doc-string \"Diadic addition of numbers.\\\\\\\\
                     \\\\code{(+ 42 2.5) = 44.5}\")
   </PRE>
   defines the addition operator (<code>:+</code> - OKBC procedure language
   operators are named by keywords) as the Lisp function <code>+</code>.
   The <code>doc-string</code> is a piece of TeX source describing the
   operator."
  (let ((expander-body
	 `(list ',lisp-operator
	        (expand-okbc-expression (second expression))
	        (expand-okbc-expression (third expression)))))
    `(def-trivial-eval-for-okbc-cons
      ((key (eql ,name)) (expression cons) environment)
      ,@(if doc-string (list :doc-string doc-string) nil)
      :body (progn (check-length expression 3)
		   (,lisp-operator
		    (trivial-eval-for-okbc (second expression) environment)
		    (trivial-eval-for-okbc (third expression) environment)))
      :expander (progn (check-length expression 3)
		       ,expander-body))))

(defmethod expand-okbc-expression ((expression cons))
  (expand-okbc-expression-cons (first expression) expression))

(defmethod expand-okbc-expression ((expression number)) expression)

(defmethod expand-okbc-expression ((expression string)) expression)

(defmethod expand-okbc-expression ((expression procedure)) expression)

(defmethod expand-okbc-expression ((expression symbol))
  (let ((tail (and (not (keywordp expression))
		   (member expression *bound-vars* :test #'string-equal))))
    (cond ((keywordp expression)
	   (intern (string-upcase expression) :keyword))
	  ((string-equal expression 'kb) 'kb)
	  ((string-equal expression 'procedure) 'procedure)
	  ((string-equal expression 'arguments) 'arguments)
	  ((string-equal expression t) t)
	  ((string-equal expression nil) nil)
	  (tail
	   (if (member '&args tail)
	       (first tail)
	       `(locally (declare (special ,(first tail))) ,(first tail))))
	  (t `(locally (declare (special ,expression)) ,expression)))))

(defun substitute-global-args (expression)
  (or (and (symbolp expression)
	   (find expression '(kb procedure arguments) :test #'string=))
      expression))

(def-trivial-eval-for-okbc-cons
    ((key cons) (expression cons) environment)
    :body 
  (progn (continuable-assert (string= 'lambda (first key)) ()
			     "Illegal procedure ~S" key)
	 (let ((args (loop for arg in (rest expression)
			   for formal in (second key)
			   collect (list formal
					 (trivial-eval-for-okbc
					  arg environment)))))
	   (loop with value = nil
		 with new-env = (append args environment)
		 for form in (rest (rest key))
		 do (setq value (trivial-eval-for-okbc form new-env))
		 finally (return value))))
  :expander
  (progn (continuable-assert (string= 'lambda (first key)) ()
			     "Illegal procedure ~S" key)
	 (destructuring-bind (args &rest body) (rest key)
	   `((lambda (,@args)
	       (declare (special ,@args))
	       ,@(loop for form in body
		       collect (expand-okbc-expression form)))
	     ,@(loop for arg in (rest expression)
		     collect (let ((*bound-vars* (append args *bound-vars*)))
			       (expand-okbc-expression arg)))))))

(def-trivial-eval-for-okbc-cons
    ((key (eql 'quote)) (expression cons) (environment t))
    :doc-string
    "The \\code{QUOTE} operator denotes a literal object.
     \\code{QUOTE} can be used either in the form \\code{(quote foo)} or with
     the shorthand syntax \\code{'foo} to denote the literal symbol foo,
     as opposed to the value of the variable \\code{foo}.  For example, if
     \\code{foo} has the value \\code{42}, then the expression
     \\code{(list (quote foo) foo)} will
     have the value \\code{(FOO 42)}."
    :body (progn (check-length expression 2)
		 (second expression))
    :expander (progn (check-length expression 2)
		     expression))

(def-trivial-diadic :+ +
  :doc-string "Diadic addition of numbers.\\\\
   \\code{(+ 42 2.5) = 44.5}")
(def-trivial-diadic :- -
  :doc-string "Diadic subtraction of numbers.\\\\
   \\code{(- 42 2.5) = 39.5}")
(def-trivial-diadic :* *
  :doc-string "Diadic multiplication of numbers.\\\\
   \\code{(* 42 2.5) = 105.0}")
(def-trivial-diadic :/ /
  :doc-string "Diadic division of numbers.\\\\
  \\code{(/ 42 2.5) = 16.8}")
(def-trivial-diadic := =
  :doc-string "Equality of numeric quantities.\\\\
  \\code{(= 42 2.5) = NIL}\\\\
  \\code{(= 42 42) = T}\\\\
  \\code{(= 42 42.0) = T}")
(def-trivial-diadic :> >
  :doc-string "The numeric greater-than operator.\\\\
   \\code{(> 42 2.5) = T}")
(def-trivial-diadic :< <
  :doc-string "The numeric less-than operator.\\\\
   \\code{(< 42 2.5) = NIL}")
(def-trivial-diadic :<= <=
  :doc-string
  "The numeric less-than-or-equal operator.\\\\
   \\code{(<= 42 2.5) = NIL}\\\\
   \\code{(<= 2.5 42) = T}\\\\
   \\code{(<= 42 42) = T}")
(def-trivial-diadic :>= >=
  :doc-string
  "The numeric greater-than-or-equal operator.\\\\
   \\code{(>= 42 2.5) = T}\\\\
   \\code{(>= 2.5 42) = NIL}\\\\
   \\code{(>= 42 42) = T}")
(def-trivial-diadic :eql eql
  :doc-string "The object identity equality operator.  This operator returns
               true if the arguments represent the same object or the arguments
               are numbers and the numbers are equal.  This is similar to the
               \\code{==} operator in C and Java.\\\\
               \\code{(eql 42 42) = T}\\\\
               \\code{(eql 42.0 42.0) = NIL}\\\\
               \\code{(eql 'foo 'foo) = T}\\\\
               \\code{(eql '(foo \"Hello\") '(foo \"Hello\")) = NIL}\\\\
               \\code{(eql '(foo \"Hello\") '(foo \"hello\")) = NIL}\\\\
               \\code{(eql \"A string\" \"A string\") = NIL}\\\\
               \\code{(eql \"A string\" \"A String\") = NIL}")
(def-trivial-diadic :equal equal
  :doc-string "An equality operator like \\code{EQL}, but that also takes
               list structure into account, and that treats strings with the 
               same characters as equal.\\\\
               \\code{(equal 42 42) = T}\\\\
               \\code{(equal 42.0 42.0) = T}\\\\
               \\code{(equal 'foo 'foo) = T}\\\\
               \\code{(equal '(foo \"Hello\") '(foo \"Hello\")) = T}\\\\
               \\code{(equal '(foo \"Hello\") '(foo \"hello\")) = NIL}\\\\
               \\code{(equal \"A string\" \"A string\") = T}\\\\
               \\code{(equal \"A string\" \"A String\") = NIL}")
(def-trivial-diadic :equalp equalp
  :doc-string "An equality operator like \\code{EQUAL}, but that also does
               case-insensitive string comparison.\\\\
               \\code{(equalp 42 42) = T}\\\\
               \\code{(equalp 42.0 42.0) = T}\\\\
               \\code{(equalp 'foo 'foo) = T}\\\\
               \\code{(equalp '(foo \"Hello\") '(foo \"Hello\")) = T}\\\\
               \\code{(equalp '(foo \"Hello\") '(foo \"hello\")) = T}\\\\
               \\code{(equalp \"A string\" \"A string\") = T}\\\\
               \\code{(equalp \"A string\" \"A String\") = NIL}")
(def-trivial-diadic :nth nth
  :doc-string "Returns the zero-indexed Nth element of a list.\\\\
               \\code{(nth 0 '(a b c d)) = A}\\\\
               \\code{(nth 2 '(a b c d)) = C}\\\\
               \\code{(nth 9 '(a b c d)) = NIL}")

(defmacro ok-utils:nth-rest (n list)
  "Returns the zero-indexed Nth tail of a list.<BR>
   <code>(nth-rest 0 '(a b c d)) = (A B C D)</code><BR>
   <code>(nth-rest 2 '(a b c d)) = (C D)</code><BR>
   <code>(nth-rest 9 '(a b c d)) = NIL</code>"
  `(nthcdr ,n ,list))

(def-trivial-diadic :nth-rest nthcdr
  :doc-string "Returns the zero-indexed Nth tail of a list.\\\\
               \\code{(nth-rest 0 '(a b c d)) = (A B C D)}\\\\
               \\code{(nth-rest 2 '(a b c d)) = (C D)}\\\\
               \\code{(nth-rest 9 '(a b c d)) = NIL}")
(def-trivial-diadic :firstn firstn
  :doc-string "Returns the zero-indexed first \\code{N} elements of a list.\\\\
               \\code{(firstn 0 '(a b c d)) = NIL}\\\\
               \\code{(firstn 2 '(a b c d)) = (A B)}\\\\
               \\code{(firstn 9 '(a b c d)) = (A B C D)}")

(def-trivial-monadic :not not
  :doc-string
  "The monadic negation operator.  Non-\\code{NIL} values map to \\code{NIL},
   and \\code{NIL} maps to \\code{T}.")
(def-trivial-monadic :first first
  :doc-string "The first element of a list.\\\\
               \\code{(first '(a b c)) = A}\\\\
               \\code{(first NIL) = NIL}")
(def-trivial-monadic :rest rest
  :doc-string "The tail of a list.\\\\
              \\code{(rest '(a b c)) = (B C)}\\\\
              \\code{(rest NIL) = NIL}")
(def-trivial-monadic :reverse reverse
  :doc-string "The non-destructive reversed elements of a list or string.\\\\
               \\code{(reverse '(a b c)) = (C B A)}\\\\
               \\code{(reverse \"Hello\") = \"olleH\"}")
(def-trivial-monadic :length length
  :doc-string "Returns the length of a list.\\\\
               \\code{(length NIL) = 0}\\\\
               \\code{(length '(a b c)) = 3}")
(def-trivial-monadic :consp consp
  :doc-string "A predicate that is true if its argument is a non-NIL list.\\\\
               \\code{(consp '(a b c)) = T}\\\\
               \\code{(consp ()) = NIL}\\\\
               \\code{(consp \"Hello\") = NIL}")

(defmacro ok-utils:variablep (x)
  "A predicate that is true if <code>x</code> is a KIF variable."
  `(ok-utils:variable? ,x))

(def-trivial-monadic :variablep ok-utils:variable?
  :doc-string "Is true if its argument is a KIF variable.\\\\
               \\code{(variablep '(a b c)) = NIL}\\\\
               \\code{(variablep ?frame) = T}")

(def-trivial-eval-for-okbc-cons
    ((key (eql :and)) (expression cons) environment)
    :doc-string "Short-circuit conjunction of any number of arguments.  This
                 is equivalent to the \\verb|&&| operator in C or Java.  A
                 conjunct is true if it is not \\code{NIL}-valued.  The whole
                 \\code{AND} expression returns \\code{NIL} immediately after
                 finding the first \\code{NIL} conjunct."
    :body (loop for arg in (rest expression)
		always (trivial-eval-for-okbc arg environment))
    :expander `(and ,@(loop for arg in (rest expression)
			    collect (expand-okbc-expression arg))))

(def-trivial-eval-for-okbc-cons
    ((key (eql :or)) (expression cons) environment)
    :doc-string "Short-circuit polyadic disjunction.  This is equivalent to the
                 \\verb'||' operator in C or Java.  A disjunct is true if it is
                 not \\code{NIL}.  The whole \\code{OR} expression returns the
                 value of the first non-\\code{NIL} disjunct."
    :body (loop for arg in (rest expression)
		thereis (trivial-eval-for-okbc arg environment))
    :expander `(or ,@(loop for arg in (rest expression)
			   collect (expand-okbc-expression arg))))

(def-trivial-eval-for-okbc-cons
    ((key (eql :if)) (expression cons) environment)
    :doc-string "The conditional operator.\\\\
                 Syntax: \\code{(if <<condition>> <<then>> <<else>>)}\\\\
                 or      \\code{(if <<condition>> <then>>)}\\\\
                 Example: \\code{(if (= x 42) (list x 100) (- x 100))}\\\\
                 If \\code{x} is \\code{42} then return the list
                 containing \\code{x} and \\code{100},
                 otherwise return \\code{x} - \\code{100}.
                 If no \\code{<<else>>} clause is
                 provided and \\code{<<condition>>} evaluates to \\code{NIL},
                 then returns \\code{NIL}."
    :body (case (length expression)
	    (3 (if (trivial-eval-for-okbc (second expression) environment)
		   (trivial-eval-for-okbc (third expression) environment)
		   nil))
	    (4 (if (trivial-eval-for-okbc (second expression) environment)
		   (trivial-eval-for-okbc (third expression) environment)
		   (trivial-eval-for-okbc (fourth expression) environment)))
	    (otherwise (continuable-error
			  "Illegal IF expression ~S" expression)))
    :expander `(if ,@(loop for arg in (rest expression)
			   collect (expand-okbc-expression arg))))

(def-trivial-eval-for-okbc-cons
    ((key (eql :list)) (expression cons) environment)
    :doc-string "An operator that builds a list out of its arguments.  List
                 can take any number of arguments.  The arguments are
                 evaluated, so you must {\\tt quote} any symbol or list
                 literals, except for keywords, {\\tt T}, and {\\tt NIL}.
                 For example, \\code{(list x 42 'x)} returns the list of three
                 elements; the current value of \\code{x}, \\code{42}, and 
                 the symbol \\code{X}."
    :body (loop for arg in (rest expression)
		collect (trivial-eval-for-okbc arg environment))
    :expander `(list ,@(loop for arg in (rest expression)
			     collect (expand-okbc-expression arg))))

(def-trivial-eval-for-okbc-cons
    ((key (eql :list*)) (expression cons) environment)
    :doc-string "An operator that builds a list by appending all but its last
                 argument to its last argument, which must be a list.
                 For example, if \\code{X} has the list \\code{(D E F)} as its
                 value, \\code{(list* 'A 'B 'C x)} will return
                 \\code{(A B C D E F)}."
    :body (progn (continuable-assert (rest expression) ()
				     "Insufficient args supplied to :list*")
		 (loop for arg in (rest expression)
		       for rest on (rest expression)
		       append (if (rest rest)
				  (list (trivial-eval-for-okbc
					 arg environment))
				  (progn 
				    (continuable-assert
				     (listp arg) ()
				     "Last argument to :list* ~S is not a list"
				     arg)
				    (trivial-eval-for-okbc arg environment)))))
    :expander `(list* ,@(loop for arg in (rest expression)
			      collect (expand-okbc-expression arg))))

(def-trivial-eval-for-okbc-cons
    ((key (eql :append)) (expression cons) environment)
    :doc-string "An operator that builds a list by appending its arguments,
                 each of which must be a list.
                 For example, if \\code{X} has the list \\code{(D E F)} as its
                 value, \\code{(append '(A B C) x)} will return
                 \\code{(A B C D E F)}."
    :body (progn (continuable-assert (rest expression) ()
			 "Insufficient args supplied to :append")
		 (loop for arg in (rest expression)
		       append (trivial-eval-for-okbc arg environment)))
    :expander `(append ,@(loop for arg in (rest expression)
			       collect (expand-okbc-expression arg))))

(def-trivial-eval-for-okbc-cons
    ((key (eql :push)) (expression cons) environment)
    :doc-string "Pushes a new value onto a list named by a variable.  For
                 example, if \\code{x} has the value \\code{(B C D)}, then
                 after evaluating the expression \\code{(push 'A x)}, \\code{x}
                 will have the value \\code{(A B C D)}.
                 The call to \\code{push} returns the new value of the
                 variable."
    :body (progn (check-length expression 3)
		 (let ((entry (assoc (third expression) environment))
		       (new-value (trivial-eval-for-okbc
				   (second expression) environment)))
		   (cond ((and *allow-interpreted-global-assignments-p*
			       environment)
			  (if entry
			      (push new-value (second entry))
			      (let ((new (list (third expression)
					       (list new-value))))
				(nconc environment (list new)))))
			 (t (continuable-assert
			     entry ()
			     "Cannot push onto ~S.  ~
                              It is not in the enviroinment.  ~
                              You can only push onto bound SYMBOLs."
			     (third expression))
			    (push new-value (second entry))))))
    :expander (progn (check-length expression 3)
		     (continuable-assert (symbolp (third expression)))
		     (member (third expression) *bound-vars*)
		     `(progn (continuable-assert
			      (and (boundp ',(third expression))
				   (listp ,(expand-okbc-expression
					    (third expression)))))
		       ,(if (consp (expand-okbc-expression (third expression)))
			    (append (butlast
				     (expand-okbc-expression
				      (third expression)))
				    `((push ,(expand-okbc-expression
					      (second expression))
				       ,(first (last (expand-okbc-expression
						      (third expression)))))))
			    `(push ,(expand-okbc-expression
				     (second expression))
			      ,(expand-okbc-expression (third expression)))))))

(def-trivial-eval-for-okbc-cons
    ((key (eql :setq)) (expression cons) environment)
    :doc-string "Sets a new value for a variable.  For
                 example, \\code{(setq A 42)} assigns the value \\code{42} to
                 the variable \\code{A}.  It is an error to set the value of
                 a variable that is not already bound.
                 The call to \\code{setq} returns the new value of the
                 variable."
    :body (progn (check-length expression 3)
		 (let ((entry (assoc (second expression) environment))
		       (new-value (trivial-eval-for-okbc
				   (third expression) environment)))
		   (cond ((and *allow-interpreted-global-assignments-p*
			       environment)
			  (if entry
			      (setf (second entry) new-value)
			      (let ((new (list (second expression) new-value)))
				(nconc environment (list new)))))
			 (t (continuable-assert
			     entry ()
			     "Cannot setq ~S.  ~
                              It is not in the enviroinment.  ~
                              You can only setq bound SYMBOLs."
			     (second expression))
			    (setf (second entry) new-value)))
		   new-value))
    :expander (progn (check-length expression 3)
		     (continuable-assert (and (symbolp (second expression))
					      (member (second expression)
						      *bound-vars*)))
		     `(progn (continuable-assert
			      (boundp ',(second expression)))
		       ,(if (consp (expand-okbc-expression
				    (second expression)))
			    (append
			     (butlast
			      (expand-okbc-expression
			       (second expression)))
			     `((setq ,(first (last (expand-okbc-expression
						    (second expression))))
				,(expand-okbc-expression (third expression)))))
			    `(setq ,(expand-okbc-expression
				     (second expression))
			      ,(expand-okbc-expression (third expression)))))))

(def-trivial-eval-for-okbc-cons
    ((key (eql :member)) (expression cons) environment)
    :doc-string "\\code{(Member <<value>> <<list>>)} is true if the value is in
                 the list.  The operation \\kfn{eql-in-kb} is used to test
                 equality.
                 If the value is found, the first sub-list
                 containing the value is returned.
                 For example, \\code{(member 42 '(1 2 42 200 2001))}
                 will return \\code{(42 200 2001)}.  If the value is not found,
                 member returns \\code{NIL}."
    :body (progn (check-length expression 3)
		 (member (trivial-eval-for-okbc (second expression)
						environment)
			 (trivial-eval-for-okbc (third expression) environment)
			 :test #'(lambda (x y)
				   (eql-in-kb-internal
				    x y (trivial-eval-for-okbc 'kb environment)
				    nil))))
    :expander (progn (check-length expression 3)
		     `(member
		       ,(expand-okbc-expression (second expression))
		       ,(expand-okbc-expression (third expression))
		       :test #'(lambda (x y)
				 (eql-in-kb-internal
				  x y (symbol-value 'kb) nil)))))

(defun funspec-sort-key (x)
  (if (consp x)
      (funspec-sort-key (first x))
      x))

(defmethod funspec-sort-predicate ((x (eql nil)) (y (eql nil)) (kb t)) nil)
(defmethod funspec-sort-predicate ((x (eql nil)) (y t)         (kb t)) t)

(defmethod funspec-sort-predicate ((x (eql t)) (y (eql t))   (kb t)) nil)
(defmethod funspec-sort-predicate ((x (eql t)) (y (eql nil)) (kb t)) nil)
(defmethod funspec-sort-predicate ((x (eql t)) (y t)         (kb t)) t)

(defmethod funspec-sort-predicate ((x number) (y (eql nil)) (kb t)) nil)
(defmethod funspec-sort-predicate ((x number) (y (eql t))   (kb t)) nil)
(defmethod funspec-sort-predicate ((x number) (y number)    (kb t)) (< x y))
(defmethod funspec-sort-predicate ((x number) (y t)         (kb t)) t)

(defmethod funspec-sort-predicate ((x string) (y (eql nil)) (kb t)) nil)
(defmethod funspec-sort-predicate ((x string) (y (eql t))   (kb t)) nil)
(defmethod funspec-sort-predicate ((x string) (y number)    (kb t)) nil)
(defmethod funspec-sort-predicate ((x string) (y string)    (kb t))
  (string< x y))
(defmethod funspec-sort-predicate ((x string) (y t)         (kb t)) t)

(defmethod funspec-sort-predicate ((x symbol) (y (eql nil)) (kb t)) nil)
(defmethod funspec-sort-predicate ((x symbol) (y (eql t))   (kb t)) nil)
(defmethod funspec-sort-predicate ((x symbol) (y number)    (kb t)) nil)
(defmethod funspec-sort-predicate ((x symbol) (y string)    (kb t)) nil)
(defmethod funspec-sort-predicate ((x symbol) (y symbol)    (kb t))
  (if (eq (symbol-package x) (symbol-package y))
      (string< (symbol-name x) (symbol-name y))
      (string< (package-name (symbol-package x))
	       (package-name (symbol-package y)))))
(defmethod funspec-sort-predicate ((x symbol) (y t)         (kb t)) t)

(defmethod funspec-sort-predicate ((x kb) (y (eql nil)) (kb t)) nil)
(defmethod funspec-sort-predicate ((x kb) (y (eql t))   (kb t)) nil)
(defmethod funspec-sort-predicate ((x kb) (y number)    (kb t)) nil)
(defmethod funspec-sort-predicate ((x kb) (y string)    (kb t)) nil)
(defmethod funspec-sort-predicate ((x kb) (y symbol)    (kb t)) nil)
(defmethod funspec-sort-predicate ((x kb) (y kb)        (kb t))
  (funspec-sort-predicate (name x) (name y) kb))
(defmethod funspec-sort-predicate ((x kb) (y t)         (kb t)) t)

(defmethod funspec-sort-predicate ((x t) (y t) (kb t))
  (multiple-value-bind (framex xfound-p)
      (coerce-to-frame-internal x kb nil nil)
    (multiple-value-bind (framey yfound-p)
	(coerce-to-frame-internal y kb nil nil)
      (if xfound-p
	  (if yfound-p
	      (string< (get-frame-pretty-name-internal framex kb nil)
		       (get-frame-pretty-name-internal framey kb nil))
	      t)
	  (if yfound-p
	      nil
	      (string<
	       (value-as-string-internal x kb :user-interface t nil)
	       (value-as-string-internal y kb :user-interface t nil)))))))

(def-trivial-eval-for-okbc-cons
    ((key (eql :sort)) (expression cons) environment)
    :doc-string
  "\\code{(Sort <<list>> <<kb>>)} copies the \\code{<<list>>}, sorts the copy,
   and returns it.
   The elements of the list are sorted according to the
   following predicate, with lower ranked values appearing closer to the
   front of the resulting list.  If an element of \\code{<<list>>} is itself a
   list, then the first element of that element is iteratively taken until a
   non-list is found.  A total ordering is established within the data types
   understood by OKBC.  Objects of a type that is earlier in the following
   table are earlier in the sort.  For pairs of objects of the same type as
   shown in the table, the predicate specified in the right hand column is
   used.
   \\begin{tabularx}{\\linewidth}{XX}
   {\\em Data type}      & {\\em Comparison operation} \\\\
   False                 & --- \\\\
   True                  & --- \\\\
   Numbers               & Numeric less-than \\\\
   Strings               & String less-than \\\\
   Symbols               & String less-than of package name, string less-than of symbol name if package names match \\\\
   KBs                   & String less-than on KB names \\\\
   Frame identifications in \\karg{kb} & String less-than on pretty-names \\\\
   All other values      & String less-than on value-as-string of the values \\\\
   \\end{tabularx}"
  :body (progn
	  (check-length expression 3)
	  (let ((list (trivial-eval-for-okbc (second expression) environment))
		(kb   (trivial-eval-for-okbc (third  expression) environment)))
	    (sort (copy-list list)
		  #'(lambda (x y) (funspec-sort-predicate x y kb))
		  :key #'funspec-sort-key)))
  :expander
  (progn (check-length expression 3)
	 `(let ((.list. ,(expand-okbc-expression (second expression)))
		(.kb.   ,(expand-okbc-expression (third expression))))
	   (sort (copy-list .list.)
	    #'(lambda (x y) (funspec-sort-predicate x y .kb.))
	    :key #'funspec-sort-key))))

(defun ensure-okbc-error-p (type)
  (continuable-assert
   (and (symbolp type)
	(let ((s (find-symbol (symbol-name type) :okbc)))
	  (and s
	       (let ((c (find-class s nil)))
		 (and c (subtypep
			 s 'okbc:abstract-error))))))
   nil
   "~S doesn't name an OKBC error" type)
  (find-symbol (symbol-name type) :okbc))

(def-trivial-eval-for-okbc-cons
    ((key (eql :error)) (expression cons) environment)
    :doc-string
  "\\code{(Error <<type>> \\&rest args)} signals an error of the
   specified type.  For example,\\\\
   (error :not-coercible-to-frame :frame fff :kb kb)\\\\
   signals a \\kfn{not-coercible-to-error} error, saying that the value of
   {\\tt fff} is not a frame in the KB identified by {\\tt kb}."
  :body (progn (check-length-exceeds expression 1)
	       (let ((type (ensure-okbc-error-p
			    (trivial-eval-for-okbc
			     (second expression) environment))))
		 (let ((args (loop for arg in (rest (rest expression))
				   collect (trivial-eval-for-okbc
					    arg environment))))
		   (apply 'error type args))))
  :expander (progn
	      (check-length-exceeds expression 1)
	      `(let ((.type. (ensure-okbc-error-p
			      ,(expand-okbc-expression (second expression)))))
		(error
		 .type.
		 ,@(loop for arg in (rest (rest expression))
			 collect (expand-okbc-expression arg))))))

(def-trivial-eval-for-okbc-cons
    ((key (eql :connection)) (expression cons) environment)
    :doc-string
  "\\code{(Connection <<kb>>)} returns the connection associated with
   \\karg{kb}"
  :body (progn (check-length expression 2)
	       (connection (trivial-eval-for-okbc
			    (second expression) environment)))
  :expander (progn
	      (check-length expression 2)
	      `(connection ,(expand-okbc-expression (second expression)))))

(def-trivial-eval-for-okbc-cons
    ((key (eql :remove)) (expression cons) environment)
    :doc-string "\\code{(Remove <<value>> <<list>>)} returns a new list from
                 which has been removed all instances of the value in the
                 original list. The operation \\kfn{eql-in-kb} is used to test
                 equality.
                 List order is preserved.
                 For example, \\code{(remove 42 '(1 2 42 200 42 2001))}
                 will return \\code{(1 2 200 2001)}.  If the value is not
                 found,remove will return a copy of the original list."
    :body (progn (check-length expression 3)
		 (remove (trivial-eval-for-okbc (second expression)
						environment)
			 (trivial-eval-for-okbc (third expression) environment)
			 :test #'(lambda (x y)
				   (eql-in-kb-internal
				    x y (trivial-eval-for-okbc 'kb environment)
				    nil))))
    :expander (progn (check-length expression 3)
		     `(remove
		       ,(expand-okbc-expression (second expression))
		       ,(expand-okbc-expression (third expression))
		       :test #'(lambda (x y)
				 (eql-in-kb-internal
				  x y (symbol-value 'kb) nil)))))

(def-trivial-eval-for-okbc-cons
    ((key (eql :remove-duplicates)) (expression cons) environment)
    :doc-string "\\code{(Remove-duplicates <<list>>)} returns a new list from
                 which has been removed all duplicate entries in the original
                 list.   The operation \\kfn{eql-in-kb} is used to test
                 equality.
                 List order is preserved.
                 For example,
                 \\code{(remove-duplicates '(1 2 42 200 42 2001))}
                 will return \\code{(1 2 200 42 2001)}."
    :body (progn (check-length expression 2)
		 (remove-duplicates
		  (trivial-eval-for-okbc (second expression) environment)
		  :test #'(lambda (x y)
			    (eql-in-kb-internal
			     x y (trivial-eval-for-okbc 'kb environment)
			     nil))))
    :expander (progn (check-length expression 2)
		     `(remove-duplicates
		       ,(expand-okbc-expression (second expression))
		       :test #'(lambda (x y)
				 (eql-in-kb-internal
				  x y (symbol-value 'kb) nil)))))

(def-trivial-eval-for-okbc-cons
    ((key (eql :getf)) (expression cons) environment)
    :doc-string "\\code{(Getf <<list>> <<key>>)} gets the property value
                 associated
                 with the key in the list, where the list is an alternating
                 list of keys and values.
                 For example, \\code{(getf '(a 2 b 200) 'b)}
                 will return \\code{200}.  If the key is not found,
                 \\code{getf}
                 returns \\code{NIL}."
    :body (progn (check-length expression 3)
		 (getf (trivial-eval-for-okbc (second expression) environment)
		       (trivial-eval-for-okbc (third expression) environment)))
    :expander (progn (check-length expression 3)
		     `(getf
		       ,(expand-okbc-expression (second expression))
		       ,(expand-okbc-expression (third expression)))))

(def-trivial-eval-for-okbc-cons
    ((key (eql :assoc)) (expression cons) environment)
    :doc-string "\\code{(Assoc <<key>> <<list>>)} gets the element associated
                 with the key in the list, where the list is a list
                 of lists, keyed by the first element of each sublist.
                 For example, \\code{(assoc 'b '((a 2) (b 200)))}
                 will return \\code{(b 200)}.  If the key is not found, 
                 \\code{assoc} returns \\code{NIL}."
    :body (progn (check-length expression 3)
		 (assoc (trivial-eval-for-okbc (second expression) environment)
		        (trivial-eval-for-okbc (third expression)
					       environment)))
    :expander (progn (check-length expression 3)
		     `(assoc
		       ,(expand-okbc-expression (second expression))
		       ,(expand-okbc-expression (third expression)))))

(def-trivial-eval-for-okbc-cons
    ((key (eql :progn)) (expression cons) environment)
    :doc-string "Evaluates all of its arguments in sequence, and returns the
                 value returned by the last argument.  All arguments but the
                 last are therefore  interesting only if they perform
                 side-effects.  For example
                 \\code{(progn (push 42 x) (push 2001 x) x)}
                 will push \\code{42} onto \\code{X}, and will then push
                 \\code{2001} onto the new value of \\code{x}, and will finally
                 return the current value of \\code{x}.
                 Thus, if \\code{x} previously had the value \\code{(A B C)},
                 it will now have the value \\code{(2001 42 A B C)}."
    :body (loop for arg in (rest expression)
		for result = (trivial-eval-for-okbc arg environment)
		finally (return result))
    :expander `(progn ,@(loop for arg in (rest expression)
			      collect (expand-okbc-expression arg))))

(defun expand-let (op expression)
  (destructuring-bind (bindings &rest body) (rest expression)
    (let ((vars (loop for b in bindings collect (if (consp b) (first b) b))))
      (let ((vars-bound-so-far *bound-vars*))
	`(,op (,@(loop for b in bindings
		       for var = (first-if-list b)
		       collect
		       (if (consp b)
			   (list var
				 (let ((*bound-vars* vars-bound-so-far))
				   (expand-okbc-expression
				    (second b))))
			   var)
		       when (string= 'let* op)
		       do (push var vars-bound-so-far)))
	  (declare (special ,@vars))
	  ,@(loop for form in body
		  collect (let ((*bound-vars*
				 (append vars *bound-vars*)))
			    (expand-okbc-expression form))))))))

(def-trivial-eval-for-okbc-cons
    ((key (eql :let)) (expression cons) environment)
    :doc-string "Establishes bindings for variables and executes a body with
                 those bindings.\\\\
                 Syntax:
                       \\begin{verbatim}
                        (let ((<<var1>> <<val1>>)
                              (<<var2>> <<val2>>)
                              ....
                              (<<varn>> <<valn>>))
                           <<body expression-1>>
                           <<body expression-2>>
                           ....
                           <<body expression-n>>)
                        \\end{verbatim}
                  All the \\code{<<vali>>} expressions are evaluated before
                  the bindings for the variables are established. I.e., it is
                  as if the \\code{<<vali>>} are evaluated in parallel.
                  The value returned by the \\code{LET} expression is the
                  value of the last body expression.  For example,
                  \\begin{verbatim}
                  (let ((x '(a b c d))
                        (y 2001))
                    (push 100 x)
                    (push y x)
                    x)
                  \\end{verbatim}
                 will return \\code{(2001 100 A B C D)}."
    :body (destructuring-bind (bindings &rest body) (rest expression)
	    (let ((augmented-environment
		   (append (loop for (var expr) in bindings
				 collect (list var (trivial-eval-for-okbc
						    expr environment)))
			   environment)))
	      (loop for arg in body
		    for result = (trivial-eval-for-okbc
				  arg augmented-environment)
		    finally (return result))))
    :expander (expand-let 'let expression))

(def-trivial-eval-for-okbc-cons
    ((key (eql :let*)) (expression cons) environment)
    :doc-string "Establishes bindings for variables and executes a body with
                 those bindings.
                 Syntax:
                       \\begin{verbatim}
                          (let* ((<<var1>> <<val1>>)
                                 (<<var2>> <<val2>>)
                                 ....
                                 (<<varn>> <<valn>>))
                            <<body expression-1>>
                            <<body expression-2>>
                            ....
                            <<body expression-n>>)
                       \\end{verbatim}
                  Each \\code{<<valN>>} expression is evaluated and a binding
                  is established for \\code{<<varN>>} {\\em before} the system
                  proceeds to the next binding.  The value returned by the
                  \\code{LET*} expression is the value of the last body
                  expression.  For example,
                  \\begin{verbatim}
                  	(let* ((x '(a b c d))
                         (y (list* 2001 x)))
                    (push 100 x)
                    (list x y))
                  \\end{verbatim}
                 will return \\code{((100 A B C D) (2001 A B C D))}.
                 \\code{LET*} is
                 equivalent to a series of nested \\code{LET} expressions, so
                 \\begin{verbatim}
                 (let* ((x 42)
                        (y (list x 200)))
                   y)
                 is equivalent to
                 (let ((x 42))
                   (let ((y (list x 200)))
                     y))
                  \\end{verbatim}"
  :body (destructuring-bind (bindings &rest body) (rest expression)
	  (if bindings
	      (let ((augmented-environment
		     (destructuring-bind (var expr) (first bindings)
		       (cons (list var
				   (trivial-eval-for-okbc expr environment))
			     environment))))
		(trivial-eval-for-okbc-cons
		 key (cons (first expression) (cons (rest bindings) body))
		 augmented-environment))
	      (loop for arg in body
		    for result = (trivial-eval-for-okbc arg environment)
		    finally (return result))))
  :expander (expand-let 'let* expression))

(def-trivial-eval-for-okbc-cons
    ((key (eql :multiple-value-bind)) (expression cons) environment)
    :doc-string "Establishes bindings for variables from the multiple values
                 resulting from evaluating a form and executes a body with
                 those bindings.
                 Syntax:
                       \\begin{verbatim}
                          (multiple-value-bind (<<var1>> <<var2>> ... <<varN>>)
                              <<values-returning-form>>
                            <<body expression-1>>
                            <<body expression-2>>
                            ....
                            <<body expression-n>>)
                       \\end{verbatim}
                  A binding is established for each of the \\code{<<vars>>}
                  from the (at least) N values returned by
                  <<values-returning-form>>.  The value returned by the
                  \\code{MULTIPLE-VALUE-BIND} expression is the value of the
                  last body expression.  For example,
                  \\begin{verbatim}
                  	(multiple-value-bind (frame found-p)
                           (coerce-to-frame thing :kb kb)
                          found-p)
                  \\end{verbatim}
                 will return the value of the \\code{found-p} flag."
  :body (destructuring-bind (vars values-form &rest body) (rest expression)
	  (if vars
	      (let ((augmented-environment
		     (let ((values (multiple-value-list
				       (trivial-eval-for-okbc
					values-form environment))))
		       (append (loop for var in vars
				     for index from 0
				     for val = (nth index values)
				     collect (list var val))
			       environment))))
		(loop for arg in body
		      for result = (trivial-eval-for-okbc
				    arg augmented-environment)
		      finally (return result)))
	      (progn (trivial-eval-for-okbc values-form environment)
		     (loop for arg in body
			   for result = (trivial-eval-for-okbc arg environment)
			   finally (return result)))))
  :expander (expand-mvb expression))

(defun expand-mvb (expression)
  (destructuring-bind (vars value-form &rest body) (rest expression)
    `(multiple-value-bind (,@vars) ,(expand-okbc-expression value-form)
      (declare (special ,@vars))
      ,@(loop for form in body
	      collect (let ((*bound-vars*
			     (append vars *bound-vars*)))
			(expand-okbc-expression form))))))

(defmacro ok-utils:do-list ((var list) &body body)
  "Loops over all the elements in a list binding the variable
   <code>var</code> to each successive list element, and executing
   a set of body forms, and finally returning a list whose
   elements are the values evaluated for each list element.
   Syntax:
<PRE>  (do-list (var &lt;&lt;list expression&gt;&gt;)
     &lt;&lt;body form 1&gt;&gt;
     &lt;&lt;body form 2&gt;&gt;
     ...
     &lt;&lt;body form n&gt;&gt;)</PRE>
    For example,
<PRE>  (do-list (x '(1 2 3 4 5))
    (+ x 100))</PRE>
  will return \\code{(101 102 103 104 105)}."
  `(loop for ,var in ,list collect (locally ,@body)))

(def-trivial-eval-for-okbc-cons
    ((key (eql :do-list)) (expression cons) environment)
    :doc-string "Loops over all the elements in a list binding the variable
                 \\code{var} to each successive list element, and executing
                 a set of body forms, and finally returning a list whose
                 elements are the values evaluated for each list element.
                 Syntax:
                 \\begin{verbatim}
                        (do-list (var <<list expression>>)
                           <<body form 1>>
                           <<body form 2>>
                           ...
                           <<body form n>>)
                 \\end{verbatim}
                 For example,
                  \\begin{verbatim}
                         (do-list (x '(1 2 3 4 5))
                            (+ x 100))
                  \\end{verbatim}
                 will return \\code{(101 102 103 104 105)}."
    :body (destructuring-bind ((loop-var list-expression) &rest body)
	      (rest expression)
	    (let ((list (trivial-eval-for-okbc list-expression environment)))
	      (loop for element in list
		    collect (let ((augmented-environment
				   (cons (list loop-var element) environment)))
			      (loop for arg in body
				    for result = (trivial-eval-for-okbc
						  arg augmented-environment)
				    finally (return result))))))
    :expander (destructuring-bind ((loop-var list-expression) &rest body)
		  (rest expression)
		`(loop for .loop-var.
		  in ,(expand-okbc-expression list-expression)
		  collect (let ((,loop-var .loop-var.))
			    (declare (special ,loop-var))
			    ,@(loop for form in body
				    collect
				    (let ((*bound-vars*
					   (cons loop-var *bound-vars*)))
				      (expand-okbc-expression form)))))))

(defmacro ok-utils:while (condition &body body)
  "Loops while a condition is true, executing a body. Syntax:
<PRE>  (while &lt;&lt;condition expression&gt;&gt;
    &lt;&lt;body form 1&gt;&gt;
    &lt;&lt;body form 2&gt;&gt;
    ...
    &lt;&lt;body form n&gt;&gt;)</PRE>
  For example,
<PRE>  (while (has-more enumerator)
    (push (next enumerator) result))</PRE>
  will collect all the values in the enumerator by pushing
  them onto the list called <code>result</code>.  Note that this
  will build a list in the reverse order of the list built in
  the example for <code>while-collect</code>."
  `(loop while ,condition do (locally ,@body)))

(def-trivial-eval-for-okbc-cons
    ((key (eql :while)) (expression cons) environment)
    :doc-string "Loops while a condition is true, executing a body.
                 Syntax:
                 \\begin{verbatim}
                   (while <<condition expression>>
                     <<body form 1>>
                     <<body form 2>>
                     ...
                     <<body form n>>)
                 \\end{verbatim}
                 For example,
                  \\begin{verbatim}
                   (while (has-more enumerator)
                     (push (next enumerator) result))
                  \\end{verbatim}
                 will collect all the values in the enumerator by pushing
                 them onto the list called \\code{result}.  Note that this
                 will build a list in the reverse order of the list built in
                 the example for \\code{while-collect}."
    :body (destructuring-bind (condition-expression &rest body)
	      (rest expression)
	    (loop while (trivial-eval-for-okbc condition-expression
					       environment)
		  do (loop for arg in body
			   for result = (trivial-eval-for-okbc
					 arg environment)
			   finally (return result))))
    :expander (destructuring-bind (condition-expression &rest body)
		  (rest expression)
		`(loop while ,(expand-okbc-expression condition-expression)
		  do (progn ,@(loop for form in body
				    collect (expand-okbc-expression form))))))

(defmacro ok-utils:while-collect (condition &body body)
  "Loops while a condition is true, collecting up the results of executing a
   body.  Syntax:
<PRE>  (while-collect <<condition expression>>
    <<body form 1>>
    <<body form 2>>
    ...
    <<result body form>>)</PRE>
  For example, 
<PRE>  (while-collect (has-more enumerator)
    (next enumerator))</PRE>
  will collect all the values in the enumerator."
  `(loop while ,condition collect (locally ,@body)))

(def-trivial-eval-for-okbc-cons
    ((key (eql :while-collect)) (expression cons) environment)
    :doc-string "Loops while a condition is true, collecting up the results of
                 executing a body.
                 Syntax:
                 \\begin{verbatim}
                  (while-collect <<condition expression>>
                    <<body form 1>>
                    <<body form 2>>
                    ...
                    <<result body form>>)
                 \\end{verbatim}
                 For example, 
                 \\begin{verbatim}
                  (while-collect (has-more enumerator)
                    (next enumerator))
                 \\end{verbatim}
                 will collect all the values in the enumerator."
    :body (destructuring-bind (condition-expression &rest body)
	      (rest expression)
	    (loop while (trivial-eval-for-okbc condition-expression
					       environment)
		  collect (loop for arg in body
				for result = (trivial-eval-for-okbc
					      arg environment)
				finally (return result))))
    :expander (destructuring-bind (condition-expression &rest body)
		  (rest expression)
		`(loop while ,(expand-okbc-expression condition-expression)
		  collect (progn ,@(loop for form in body
					 collect (expand-okbc-expression
						  form))))))

(defun coerce-to-acceptable-okbcop (symbol)
  (or (and (gethash symbol *acceptable-okbcops-for-call-procedure*)
	   symbol)
      (and (not (eq *okbc-package* (symbol-package symbol)))
	   (let ((s (find-symbol (string-upcase symbol) *okbc-package*)))
	     (and s (eq *okbc-package* (symbol-package s))
		  (or (and (gethash s *acceptable-okbcops-for-call-procedure*)
			   s)
		      (let ((internal (op-name-to-internal-name s)))
			(and (gethash internal
				      *acceptable-okbcops-for-call-procedure*)
			     s))))))
      (and (not (eq *keyword-package* (symbol-package symbol)))
	   (let ((s (find-symbol (string-upcase symbol) *keyword-package*)))
	     (and s (gethash s *acceptable-okbcops-for-call-procedure*) s)))))

(defvar *environment-from-calling-context* nil)

(def-trivial-eval-for-okbc-cons ((key t) (expression cons) environment)
    :body (let ((match (coerce-to-acceptable-okbcop key)))
	    (if match
		(if (keywordp match)
		    (trivial-eval-for-okbc-cons
		     match (cons match (rest expression)) environment)
		    (apply match (loop for arg in (rest expression)
				       collect (trivial-eval-for-okbc
						arg environment))))
		(let ((fun (gethash (string-upcase key)
				    (or (and (current-kb)
					     (name-to-procedure-table
					      (current-kb)))
					*name-to-procedure-table*))))
		  (if fun
		      (let ((*environment-from-calling-context* environment))
			(call-procedure-internal
			 fun (trivial-eval-for-okbc 'kb environment)
			 (loop for arg in (rest expression)
			       collect (trivial-eval-for-okbc
					arg environment))))
		      (continuable-error
			"~S is not an acceptable OKBC operator" key)))))
    :expander (let ((match (coerce-to-acceptable-okbcop key)))
		(if match
		    (if (keywordp match)
			(expand-okbc-expression-cons
			 match (cons match (rest expression)))
			`(,match ,@(loop for arg in (rest expression)
				       collect (expand-okbc-expression arg))))
		    `(let ((fun (gethash ',(string-upcase key)
					 (or (and (current-kb)
						  (name-to-procedure-table
						   (current-kb)))
					     *name-to-procedure-table*))))
		      (if fun
			  (call-procedure-internal
			   fun (symbol-value 'kb)
			   (list ,@(loop for arg in (rest expression)
					 collect
					 (expand-okbc-expression arg))))
			  (continuable-error
			   "~S is not an acceptable OKBC operator" ',key))))))

(defvar *force-running-of-procedures-in-interpreted-mode-p* nil)

(defun eval-call-procedure (procedure kb arguments)
  (let ((*bound-vars* '(&args procedure kb arguments)))
    (declare (special *bound-vars*))
    (prepare-procedure procedure kb))
  (if (and (not *force-running-of-procedures-in-interpreted-mode-p*)
	   (procedure-function-object procedure))
      (let ((env (append (procedure-environment procedure)
			 (list (list 'procedure procedure)
			       (list 'kb kb)
			       (list 'arguments arguments)))))
	(progv (mapcar #'first env)
	    (mapcar #'second env)
	  (apply (procedure-function-object procedure)
		 arguments)))
      (let ((expression (procedure-expression procedure))
	    (environment
	     (append (procedure-environment procedure)
		     (list (list 'kb kb)
			   (list 'arguments arguments))
		     *environment-from-calling-context*))
	    (formals (procedure-arguments procedure)))
	(continuable-assert (= (length formals) (length arguments)) ()
		    "Number of arguments supplied (~D) does not match ~
                     argument count for Procedure (~D)."
		    (length arguments) (length formals))
	(call-procedure-internal
	 #'(lambda (&rest objects)
	     (trivial-eval-for-okbc
	      expression
	      (extend-environment-for-args
	       environment formals objects)))
	 kb arguments))))

(defmethods call-procedure-internal ((procedure procedure)
				    (kb (kb structure-kb)) (arguments t))
  (eval-call-procedure procedure kb arguments))

(defun call-procedure-from-symbol (procedure kb arguments)
  (if procedure
      (let ((match (gethash (string-upcase (okbc-string procedure))
			    (name-to-procedure-table kb))))
	(if match
	    (call-procedure-internal match kb arguments)
	    (continuable-error
		"~S is not a registered procedure." procedure)))
      (continuable-error "NIL cannot name a procedure.")))

(defvar *max-depth-for-procedure-calls* 50)
(defvar *current-depth-of-procedure-calls* nil)

(defmethod call-procedure-internal :around
    ((procedure t) (kb t) (arguments t))
 (call-next-method)
 #+ignore
 (if *current-depth-of-procedure-calls*
     (let ((*current-depth-of-procedure-calls*
	    (+ *current-depth-of-procedure-calls* 1)))
       (when (> *current-depth-of-procedure-calls*
		*max-depth-for-procedure-calls*)
	 (continuable-error
	  "Recursion depth too deep in procedure language
           virtual machine whilst calling ~S with arguments ~{~S~^, ~}"
	  procedure arguments))
       (call-next-method))
     (let ((*current-depth-of-procedure-calls* 0))
       (call-next-method))))

(defmethods call-procedure-internal
    ((procedure (symbol quasi-symbol)) (kb (kb structure-kb)) (arguments t))
  (call-procedure-from-symbol procedure kb arguments))

(defun runtime-expand-procedure (name args body environment kb)
  (etypecase args
    (string
     (continuable-assert (and (= (length body) 1) (stringp (first body))) ()
			 "When you specify a string for the args to a ~
                  procedure, the body must also be a string.")
     (intern-procedure
      :name name :arguments args :expression (first body) :environment nil
      :kb kb))
    (list
     (let ((env (trivial-eval-for-okbc
		 (second (member '&environment args))
		 environment)))
       (let ((args (loop for arg in args
			 until (string= arg '&environment)
			 collect (substitute-global-args arg))))
	 (continuable-assert
	  (listp env) ()
	  "The environment must be of the form ((sym value) ...), ~
           not ~S" env)
	 (loop for x in env
	       do (continuable-assert
		   (and (consp x) (= (length x) 2)
			(symbolp (first x))) ()
			"Each environment entry must be of the form ~
                         (sym value), not ~S"
			x))
	 (let ((substituted
		(substitute-internals
		 (if (and (consp body)
			  (consp (first body))
			  (not (member (first (first body)) '(lambda))))
		     (if (rest body)
			 (cons :progn body)
			 (first body))
		     body)))) ;; end up with a simple form
	   (intern-procedure
	    :name name
	    :arguments args
	    :expression substituted
	    :environment (append env environment)
	    :kb kb
	    :function-object
	    (if (and *compile-named-procedures-p* name)
		(let ((expanded-args
		       (loop for arg in args
			     collect (or (find arg *bound-vars*
					       :test #'string-equal)
					 arg))))
		  (let ((expanded
			 (let ((*bound-vars*
				(append
				 args
				 '(&args)
				 (locally
				     (declare (special *bound-vars*))
				   *bound-vars*))))
			   (declare (special *bound-vars*))
			   (expand-okbc-expression substituted))))
		    (let ((lambda-expression
			   `((,@expanded-args)
			     (declare (special
				       ,@(remove-duplicates
					  (append
					   expanded-args
					   (loop for rest on *bound-vars*
						 when (eq (first rest) '&args)
						 return (rest rest))))))
			     ,expanded)))
		      (compile nil
			       #+Lucid
			       (cons 'lcl::named-lambda
				     (cons name lambda-expression))
			       #-Lucid
			       (cons 'lambda lambda-expression)))))
		nil))))))))

