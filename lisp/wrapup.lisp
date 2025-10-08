(in-package :ok-kernel)

;; Reset the KB ID counter to a good-seeming number.
;; KB IDs should ideally be globally unique.
(setq *unique-kb-ids* (start-point-for-kb-ids))

(defun band-boot-reset-ID-counters ()
  (setq *image-unique-tag* (image-unique-tag t))
  (setq *unique-kb-ids* (start-point-for-kb-ids))
  (setq *server-unique-kb-id-offset* (make-server-kb-id-start-point)))

;;; At band start up time we want to reset the KB ID start point.
#+Lucid
(defadvice (lucid::lucid-banner :reset-kb-unique-id-counter) (&rest args)
  ;; Do this at banner display time so that we don't interfere with any
  ;; user-supplied *enter-top-level-hook* or disksave :restart-function.
  (let ((results (multiple-value-list (apply-advice-continue args))))
    (band-boot-reset-ID-counters)
    (values-list results)))

#+Harlequin-Common-Lisp
(lw:defadvice (system::top-level-entry-function :reset-kb-unique-id-counter
						:around)
     (&rest args)
  ;; Do this at banner display time so that we don't interfere with any
  ;; user-supplied *enter-top-level-hook* or disksave :restart-function.
  (let ((results (multiple-value-list (apply #'lw:call-next-advice args))))
    (band-boot-reset-ID-counters)
    (values-list results)))

#+Allegro
;;; Note: we don't use the #+allegro-4.3 feature because we don't know what
;;; will happen when the version number gets bumped, but they should keep
;;; the same syntax for *restart-actions*.  We do it this way rather than
;;; by using the two magic functions because we expect that a user will want
;;; to use them.
(progn #+(and allegro-version>= (version>= 4 3))
       (pushnew 'band-boot-reset-ID-counters excl:*restart-actions*)
       ;; In older versions it would appear that we push on a form to eval.
       ;; I don't have an instance of a pre-4.3 Franz, so this might not
       ;; work, but then again all sorts of other things might not in a really
       ;; old Franzes too.
       #-(and allegro-version>= (version>= 4 3))
       (pushnew '(:eval (band-boot-reset-ID-counters)) excl:*restart-actions*
		:test #'equal))

#-(or Lucid Allegro Harlequin-Common-Lisp)
(cerror "Go ahead anyway"
	"Need to implement a way to handle the band start call of ~S"
	'band-boot-reset-ID-counters)

(defun create-meta-kb ()
  (let ((inst (make-instance 'meta-kb :name '$meta-kb$
			     :cache nil
			     :indexing-type :full-index
			     :allow-caching-p :ephemeral)))
    (tuple-store:ensure-full-index (tuple-kb:tuple-kb-tuple-store inst))
    inst))

;;; Now actually instantiate the meta kb.
(defvar $meta-kb$ 
  (create-meta-kb)
  "An internal variable whose value is always the Meta-KB for the current
   OKBC implementation.  The value of this variable is equivalent to a call
   to <code>(meta-kb :connection (local-connection))</code>")


#+Allegro
(loop for class-name in *all-okbc-classes-to-finalize*
      do (clos:finalize-inheritance (find-class class-name)))

(eval-when (compile load)

  (defun hack-arg-for-manual-entry (arg)
    (cond ((or (and (consp arg)
		    (= (length arg) 2)
		    (string= (first arg) :kb)
		    (equal (second arg) '(current-kb)))
	       (and (consp arg)
		    (= (length arg) 2)
		    (string= (first arg) :kb-type)
		    (equal (second arg)
			   '(okbc:get-kb-type (okbc:current-kb)))))
	   (first arg))
	  ((and (consp arg) (eq nil (second arg)) (first arg)))
	  (t arg)))

  (defun generate-manual-entry-for-okbc-op (op stream)
    (when (member :front (which-ends op))
      (with-standard-io-syntax
	  (multiple-value-bind (args values)
	    (if (assoc op *all-okbcfuns*)
		(destructuring-bind (args values)
		    (rest (assoc op *all-okbcfuns*))
		  (values args values))
		(okbcop-args op))
	    (let ((args (mapcar 'hack-arg-for-manual-entry args))
		  (arg-names (loop for arg in args
				   when (not (member arg lambda-list-keywords))
				   collect (first-if-list arg)))
		  (docs (raw-documentation op))
		  (*print-case* :downcase)
		  (*package* (find-package :okbc))
		  (*print-readably* nil)
		  (enumerate-p (and (> (length (string op))
				       (length "ENUMERATE-"))
				    (string= "ENUMERATE-" (string op)
					     :end2 (length "ENUMERATE-"))))
		  (optional-status
		   (if (or (null args) (assoc op *all-okbcfuns*))
		       :involuntary
		       (if (or (not (op-name-to-internal-name op))
			       (non-mandatory-okbcop-p
				(symbol-function (op-name-to-internal-name op))
				(find-class 'ok-back:standard-defaults-kb)))
			   :optional
			   :mandatory)))
		  (has-enumerator-p
		   (and (op-name-to-internal-name op)
			(has-enumerator-p (op-name-to-internal-name op)))))
	      (let ((unmentioned
		     (loop for arg in arg-names
			   for arg-name = (string arg)
			   when (and (not (search arg-name docs :test
						  #'string-equal))
				     (not (member arg-name
						  '(frame
						    slot
						    facet
						    value
						    kb
						    number-of-values
						    inference-level
						    kb-local-only-p
						    slot-type
						    value-selector
						    test
						    kb-type
						    connection
						    error-p)
						  :test #'string=)))
			   collect arg)))
		(when (and unmentioned (not enumerate-p))
		  (format t
		   "~2%!!! Warning:  In the doc string for ~S, ~
                        ~%!!! the following argument(s) is/are not mentioned: ~
                      ~{~%!!!     ~S~^, ~}"
		    op unmentioned)))
	      (let ((unmentioned
		     (loop for arg in values
			   for arg-name = (string arg)
			   when (and (not (search arg-name docs :test
						  #'string-equal))
				     (not (member arg-name
						  '(more-status
						    boolean
						    list-of-connections
						    enumerator
						    exact-p)
						  :test #'string=)))
			   collect arg)))
		(when (and unmentioned (not enumerate-p))
		  (format t
		   "~2%!!! Warning:  In the doc string for ~S, ~
                        ~%!!! the following returned value(s) is/are not ~
                              mentioned: ~
                      ~{~%!!!     ~S~^, ~}"
		    op unmentioned)))
	      (format stream "~2%")
	      (if docs
		  (progn (format stream "\\begin{~A}{~S}{ "
			   (if (assoc op *all-okbcfuns*)
			       "okbcfun"
			       "okbcop")
			   op)
			 ;; Bind package here because the core files are in the
			 ;; ok-kernel package, so the args may not be exported
			 ;; from the okbc package.
			 (let ((*package* (find-package :ok-kernel)))
			   (loop for arg in args
				 for first-p = t then nil
				 when (not first-p) do (princ " " stream)
				 do (case arg
				      (&key (princ "\\&key" stream))
				      (otherwise 
				       (if (and (consp arg)
						(eq t (second arg))) 
					   (format stream "(~S \\true)"
					     (first arg))
					   (prin1 arg stream)))))
			   (if values
			       (format stream "} { ~{~S~^ ~} }" values)
			       (format stream "} { \\void }")))
			 (format stream " { ~A }"
			   (ecase optional-status
			     (:involuntary " ")
			     (:optional "O")
			     (:mandatory "M")))
			 (format stream " { ~A }"
			   (if (causes-side-effects-p op) "W" "R"))
			 (format stream " { ~A }~%"
			   (if has-enumerator-p "E" ""))
			 ;;(print-string-flushed-left docs stream "")
			 (princ docs stream)
			 (format stream "~%\\end{~A}"
			   (if (assoc op *all-okbcfuns*)
			       "okbcfun"
			       "okbcop")))
		  (format t "~%;;; !!!! No documentation for okbcop ~A !!!"
		    op)))))))

  (defun generate-manual-entry-for-condition (condition slot-inits stream)
    (with-standard-io-syntax
	(let ((docs (raw-documentation condition))
	      (*print-case* :downcase)
	      (*package* (find-package :okbc))
	      (*print-readably* nil))
	  (let ((unmentioned
		 (loop for init-name in slot-inits
		       when (and (not (search (string init-name) docs :test
					      #'string-equal))
				 (not (member init-name
					      '(frame
						slot
						slot-type
						facet
						value
						kb)
					      :test #'string=)))
		       collect init-name)))
	    (when unmentioned
	      (format t
	       "~2%!!! Warning:  In the doc string for condition ~S, ~
                        ~%!!! the following slot inits(s) is/are not ~
                              mentioned: ~
                      ~{~%!!!     ~S~^, ~}"
		condition unmentioned)))
	  (format stream "~2%")
	  (if docs
	      (progn (format stream "\\begin{okbccondition}{~S}{ " condition)
		     (loop for init in slot-inits
			   for first-p = t then nil
			   when (not first-p) do (princ " " stream)
			   do (princ init stream))
		     (format stream " }")
		     (let ((super (class-name
				   (first (clos::class-direct-superclasses
					   (find-class condition))))))
		       (if (eq 'error super)
			   (format stream " { }~%")
			   (format stream " { \\kcond{~A} }~%" super)))
		     ;;(print-string-flushed-left docs stream "")
		     (princ docs stream)
		     (format stream "~%\\end{okbccondition}"))
	      (format t "~%;;; !!!! No documentation for okbccondition ~A !!!"
		condition)))))

  (defun get-manual-categories ()
    (let ((all nil))
      (loop for op in (append *all-okbcops* (mapcar #'first *all-okbcfuns*))
	    do (pushnew (manual-category op) all))
      all))

  (defun target-spec-path (name type)
    ;; Probe for the file just in case.  This will chase any
    ;; links and put the file in the right place.
    (let ((file-path (make-pathname
		      :defaults (tex-doc-path)
		      :name name
		      :type type)))
      (or (probe-file file-path) file-path)))

  (defun mandatory/optional-ops ()
    (with-open-file (stream (target-spec-path "okbc-mandatory-op-specs" "tex")
		      :direction :output :if-exists :supersede
		      :if-does-not-exist :create)
      (loop with first-p = t
	    for op in (sort (copy-list *all-okbcops*) #'string<)
	    unless (non-mandatory-okbcop-p
		    (symbol-function (op-name-to-internal-name op)))
	    do (when (not first-p) (format stream ",~%"))
	    (format stream "\\kfn{~A}" (string-downcase op))
	    (setq first-p nil)))
    (with-open-file (stream (target-spec-path "okbc-optional-op-specs" "tex")
		      :direction :output :if-exists :supersede
		      :if-does-not-exist :create)
      (loop with first-p = t
	    for op in (sort (copy-list *all-okbcops*) #'string<)
	    when (non-mandatory-okbcop-p
		  (symbol-function (op-name-to-internal-name op)))
	    do (when (not first-p) (format stream ",~%"))
	    (format stream "\\kfn{~A}" (string-downcase op))
	    (setq first-p nil)))
    (with-open-file (stream (target-spec-path
			     "okbc-system-defined-op-specs" "tex")
		      :direction :output :if-exists :supersede
		      :if-does-not-exist :create)
      (loop with first-p = t
	    for op in (sort (mapcar #'first *all-okbcfuns*) #'string<)
	    do (when (not first-p) (format stream ",~%"))
	    (format stream "\\kfn{~A}" (string-downcase op))
	    (setq first-p nil))))

  (defun generate-manual-text ()
    (with-open-file (stream (target-spec-path "okbc-op-specs" "tex")
		      :direction :output :if-exists :supersede
		      :if-does-not-exist :create)
      (loop for op in (sort (append *all-okbcops*
				    (mapcar #'first *all-okbcfuns*))
			    #'string<)
	    do (generate-manual-entry-for-okbc-op op stream)))
    (loop for category in (get-manual-categories)
	  for path = (target-spec-path (format nil "okbc-~A-op-specs"
					 (string-downcase category))
				       "tex")
	  for ops = (loop for op in (append *all-okbcops*
					    (mapcar #'first *all-okbcfuns*))
			  when (eq category (manual-category op))
			  collect op)
	  do (with-open-file (stream path :direction :output
				     :if-exists :supersede
				     :if-does-not-exist :create)
	       (loop for op in (sort ops #'string<)
		     for first-p = t then nil
		     when (not first-p) do (format stream ",~%")
		     do (format stream "\\kfn{~A}" (string-downcase op)))))
    (let ((path (target-spec-path "okbc-condition-specs" "tex")))
      (with-open-file (stream path :direction :output :if-exists :supersede
			      :if-does-not-exist :create)
	(loop for (condition . slot-inits)
	      in (sort (copy-list *all-okbc-conditions*) 'string< :key #'first)
	      do (generate-manual-entry-for-condition condition slot-inits
						      stream))))
    (let ((path (target-spec-path "okbc-fspec-specs" "tex")))
      (with-open-file (stream path :direction :output :if-exists :supersede
			      :if-does-not-exist :create)
	(document-procedure-evaluators-latex stream)))
    (mandatory/optional-ops))

  (defun starts-with (string substring)
    (and (>= (length string) (length substring))
	 (string-equal substring string :end2 (length substring))))

  (defun documentation-worthy-symbol (sym)
    (and (or (eq *package* (symbol-package sym))
	     (eq (symbol-package sym) *okbc-package*))
	 (not (gethash (symbol-name sym) *all-okbcops-ht*))
	 (not (member sym *all-okbcfuns*))
	 (not (ok-utils:internal-name-to-op-name sym))
	 (not (concrete-kb-class-from-abstract-kb-class-name sym))
	 (or (boundp sym)
	     (fboundp sym)
	     (and (find-class sym nil)
		  (not (assoc sym *all-okbc-conditions*))))
       ;;; Don't document the machine-generated cache methods.
	 (or (not (eq (symbol-package sym) *ok-cache-package*))
	     (not (or (starts-with (symbol-name sym) "ENCACHE-")
		      (starts-with (symbol-name sym) "CACHED-P-"))))))

  (defun find-undocumented-symbols (package)
    (let ((missing nil))
      (do-external-symbols (sym package)
	(when (and (documentation-worthy-symbol sym)
		   (not (or (documentation sym 'type)
			    (documentation sym 'structure)
			    (documentation sym 'function)
			    (documentation sym 'variable))))
	  (push sym missing)))
      (when missing
	(format t
	 "~%The following symbols are undocumented in package ~A (~D):~
          ~{~%  ~A~^,~}"
	  (package-name package) (length missing) (sort missing #'string<)))))

  (defparameter *okbc-package-documentation-header-alist*
    '((tries
       "
<HTML>
<TITLE>Documentation for the TRIES package</TITLE>
<H2>Documentation for the TRIES package</H2>

This document contains documentation for the <code>TRIES</code> package,
which is a utility package shipped with the OKBC release.<P>

This software implements an efficient key-to-value mapping data structure
that will typically give much better performance than <code>equal</code>
hash-tables.<p>

Two distinct variants of the <code>TRIE</code> data structure are supplied
with API for each.  One implementation, called <code>trie</code> uses cons
cells very efficiently so as to implement the TRIE discrimination net in
as space-efficient a manner as possible.  The result is a data structure that
is consp, and whose contents are effectively unintelligible to anyone,
but for which the API works fine.  You can freely use this implementation
for any application for which you will feel no need to delve inside the
TRIE itself.<P>

A second implementation, called <code>structure-trie</code> implements the same
data structure concepts and an equivalent API using defstruct for the nodes
in the discrimination net.  This is less space efficient, but has the
advantage that you can see better what's going on in the inspector and
debugger.  Another advantage of this version is that you can subclass the
<code>structure-trie</code> defstruct.  The implementation provides an
example of this called <code>root-trie</code> which is useful as the root
node of a trie data structure.<P>

The APIs for these two versions of the data structure are disjoint.  For each
operation on <code>trie</code>s called, say, <code>trie-foo</code> there is
a conforming <code>structure-trie-foo</code>.<p>

A further set of API is provided to allow the use of hybrid trie structures
that mix the two data structure variants.  In this version, the API is
implemented as CLOS methods (called <code>hybrid-trie-foo</code>, so using
this approach will allow you to achieve the best space efficiency whilst
still being able to use <code>structure-trie</code> subclass nodes to store
extra application-specific data.  The downside of this approach is that the
accesses to the data structures are slower than they would be for either of
the more specialized cases.<P>

If you use the hybrid trie operations, you can switch in your code between
using the cons or the defstruct variant simply by switching a feature
and recompiling.  Adding the <code>use-minimal-tries</code> feature will give
the most space-efficient version.<P>

Note that when using the hybrid trie operations, <code>structure-trie</code>s
can point to <code>trie</code>s, but <i>not</i> vice versa.  This gives the
best all-round space efficiency.<P>

Note also that the tries will automatically switch into using hash tables
when necessary.  When they do so, they use the
<code>ok-utils:fast-hash-key</code> index function to extract the hash key.
Specializing this generic function as appropriate for your application will
deliver the best performance from your tries.")
      (okbc-test
       "
<HTML>
<TITLE>Documentation for the OKBC-TEST package</TITLE>
<H2>Documentation for the OKBC-TEST package</H2>

This document contains documentation for the <code>OKBC-TEST</code> package
in OKBC, which defines the OKBC test suite for the Lisp implementation.
The test suite is expected to be useful primarily to OKBC back end
authors.")
      (ok-cache
       "
<HTML>
<TITLE>Documentation for the OK-CACHE package</TITLE>
<H2>Documentation for the OK-CACHE package</H2>

This document contains documentation for the <code>OK-CACHE</code> package
in OKBC.  The functions, variables and classes described
are expected to be useful both to OKBC application authors and to OKBC back end
authors.

All exported <code>OK-CACHE</code> API is documented here except for the
cache operations associated with each OKBC operation.  For each OKBC front
end API operation <code>foo</code>, two caching operations are defined:
<code>ok-cache:cached-p-foo</code> and <code>ok-cache:encache-foo</code>.<P>

The <code>ok-cache:cached-p-foo</code> operation takes exactly the same
arguments as the front end APi operation (with the same defaulting scheme),
and returns true if there is a cached value for that call.  The cached-p
operations return two values: the flag that says whether the call has been
cached or not, and the cache node for the call
(see <code>cache-entry-found-p</code>).<P>

The <code>ok-cache:encache-foo</code> operation encaches a value for a front
end API call.  It takes the same arguments as the front end API operation,
except it has an extra leftmost argument that embodies the value(s) to be
encached under the specified arguments.<P>

For example, the following code checks to see whether a value is in the
cache for a certain call to <code>get-frame-name</code>, and if it is it
returns that value.  Failing this, it calls <code>get-frame-details</code>
and then returns the frame name.<PRE>
  (if (ok-cache:cached-p-get-frame-name frame :kb my-kb)
      (okbc:get-frame-name frame :kb my-kb)
      (progn (okbc:get-frame-details frame :kb my-kb :inference-level :direct)
             (okbc:get-frame-name frame :kb my-kb)))</PRE>
Further performance can be achieved if necessary by plucking the values
directly out of the cache and out of the details plist.
  (multiple-value-bind (found-p cache-node)
     (ok-cache:cached-p-get-frame-name frame :kb my-kb)
    (if found-p
        (tries:hybrid-trie-value cache-node)
        (getf (okbc:get-frame-details frame :kb my-kb :inference-level :direct)
              :name)))</PRE>
The first argument to the encache- operations is the value to cache if the
operation only returns one value.  If the operation returns multiple values,
then this argument can be one of two options: a list of the form
<code>(:values v0 v1 ... vn-1)</code>, where the values represent all of the
values expected to be retuned by the operation.  This list must be of the
correct length.  If the argument is not of this form, it is taken to denote
a single value for the zeroth returned value.  All other values will be filled
in with NIL.<P>

Just as there is an <code>ok-back:foo-internal</code> back end generic function
for each front end operation, there is also an
<code>ok-cache:cached-p-foo-internal</code>, and an
<code>ok-cache:encache-foo-internal</code> generic function to mirror the
cache calls in the front end API.  These should be used by back and middle end
code that does manual cache manipulation.
<HR>")
      (ok-utils
       "
<HTML>
<TITLE>Documentation for the OK-UTILS package</TITLE>
<H2>Documentation for the OK-UTILS package</H2>

This document contains documentation for the OKBC Lisp implementation utilities
package <code>OK-UTILS</code>.  The functions, variables and classes described
are expected to be useful both to OKBC application authors and to OKBC back end
authors.

<HR>")
      (ok-back
       "
<HTML>
<TITLE>Documentation for the OK-BACK package</TITLE>
<H2>Documentation for the OK-BACK package</H2>

This document contains documentation for the exported symbols in the
<code>OK-BACK</code> Lisp package.  The functions, variables and classes
described are expected to be used by OKBC back end authors.  It is almost
certainly an error for any OKBC application to use any of these symbols.<P>

<B>It is an error for any application to intern <i>any</i> symbol in the
<code>OK-BACK</code> package.</B>  Back end authors should not write any code
in the <code>OK-BACK</code> package.  No symbols should be interned in the
<code>OK-BACK</code> package unless they are exported, documented, and
the only symbols that should be so interned are KB class names.<P>

Note:  This documentation covers all external <code>OK-BACK</code> symbols
<i>except for those that are covered by the specification</i>.  For all
operations in the
<A HREF=\"http://ontolingua.stanford.edu/doc/release/okbc/okbc-spec/index.html\">
OKBC specification</A> that are implementable in the back end, there exists a
generic function in the back end API with the same name with
\"<code>-INTERNAL</code>\" appended to it, and homed in the
<code>OK-BACK</code> package.  All arguments to these generic functions are
positional, and may be specialized.  Thus, the front end API operation
<code>okbc:get-slot-values</code> defined as:<BR>
<TABLE width=100%><DT>
 <TR>
  <TD valign=top>
   <TABLE>
    <TR>
     <TD valign=top> <code><B>okbc:get-behavior-values</B></code> </TD>
     <TD valign=top align=left>((behavior :value) &key (kb (current-kb)))
    </TR>
   </TABLE>
  <TD valign=top align=right> <I>[operation]</I>
 </TR>
</TABLE>
is mirrored by a generic function in the back end API:<BR>
<TABLE width=100%><DT>
 <TR>
  <TD valign=top>
   <TABLE>
    <TR>
     <TD valign=top>
       <code><B>ok-back:get-behavior-values-internal</B></code> </TD>
     <TD valign=top align=left>(behavior kb)
    </TR>
   </TABLE>
  <TD valign=top align=right> <I>[generic function]</I>
 </TR>
</TABLE>

Which operation the back end author will need to implement can be determined
by using
<A href=\"ok-utils-lisp-package-docs.html#compliant-okbc-implementation-p\">
ok-utils:compliant-okbc-implementation-p</A>.

<HR>")))

  (#+Harlequin-Common-Lisp
   eval-when
   #+Harlequin-Common-Lisp (compile load eval)
   #-Harlequin-Common-Lisp progn
   (defun link-symbols-when-possible (string)
     (let ((code-index (search "<code>" string :test #'char-equal))
	   (pre-index (search "<pre>" string :test #'char-equal)))
       (if (and code-index (or (not pre-index) (< code-index pre-index)))
	   (let ((stop-index (search "</code>" string :test #'char-equal)))
	     (if stop-index
		 (concatenate
		  'string
		  (subseq string 0 (+ code-index (length "<code>")))
		  (maybe-link-<code>-body
		   (subseq string (+ code-index (length "<code>")) stop-index))
		  (subseq string stop-index (+ stop-index (length "</code>")))
		  (link-symbols-when-possible
		   (subseq string (+ stop-index (length "</code>")))))
		 string))
	   (if pre-index
	       (let ((stop-index (search "</pre>" string :test #'char-equal)))
		 (if stop-index
		     (concatenate
		      'string
		      (subseq string 0 (+ pre-index (length "<pre>")))
		      (maybe-link-<code>-body
		       (subseq string (+ pre-index (length "<pre>"))
                               stop-index))
		      (subseq string stop-index
                              (+ stop-index (length "</pre>")))
		      (link-symbols-when-possible
		       (subseq string (+ stop-index (length "</pre>")))))
		     string))
	       string))))

   (defun maybe-link-<code>-body (string)
     (let ((token-start (loop for index from 0 below (length string)
			      for char = (char string index)
			      when (or (alpha-char-p char)
				       (char= char #\:)
				       (char= char #\*))
			      return index)))
       (if token-start
	   (let ((token-stop (loop for index from token-start
                                   below (length string)
				   for char = (char string index)
				   when (not (or (alpha-char-p char)
						 (digit-char-p char)
						 (char= char #\-)
						 (char= char #\&)
						 (char= char #\:)
						 (char= char #\*)))
				   return index
				   finally (return (length string)))))
	     (if token-stop
		 (concatenate
		  'string
		  (subseq string 0 token-start)
		  (let ((substring (subseq string token-start token-stop))
			(usubstring (string-upcase
				     (subseq string token-start token-stop))))
		    (let ((colon-index (position #\: substring :test #'char=)))
		      (let ((package
			     (if colon-index
				 (if (zerop colon-index)
				     *keyword-package*
				     (find-package
				      (subseq usubstring 0 colon-index)))
				 *package*)))
			(if (and package
				 (member (package-name package)
					 '(ok-utils ok-back tries tuple-store
					   ok-cache ok-test)
					 :test #'string=))
			    (multiple-value-bind (sym status)
			      (find-symbol
			       (subseq usubstring (if colon-index
						      (+ colon-index 1)
						      0))
			       package)
			      (if (and sym (eq :external status))
				  (concatenate
				   'string
				   "<A HREF=\""
				   (if (eq package *package*)
				       ""
				       (concatenate
					'string
					(file-name-from-package package)
					".html"))
				   (concatenate 'string "#"
						(string-downcase sym))
				   "\">"
				   substring
				   "</A>")
				  substring))
			    substring))))
		  (maybe-link-<code>-body (subseq string token-stop)))
		 string))
	   string)))

   #+Harlequin-Common-Lisp
   (progn (when (not (compiled-function-p #'link-symbols-when-possible))
	    (compile 'link-symbols-when-possible))
	  (when (not (compiled-function-p #'maybe-link-<code>-body))
	    (compile 'maybe-link-<code>-body))))

  (defun file-name-from-package (package)
    (when (not (packagep package)) (setq package (find-package package)))
    (concatenate 'string (string-downcase (package-name package))
		 "-lisp-package-docs"))

  (defun symbol-description-string (m &optional (restrict-to nil))
    (cond ((and (macro-function m)
		(or (not restrict-to) (eq restrict-to 'function)))
	   "macro")
	  ((and (fboundp m) (or (not restrict-to) (eq restrict-to 'function)))
	   (if (ignore-errors (fdefinition `(setf ,m)))
	       (if (clos::generic-function-p (symbol-function m))
		   "accessor generic function"
		   "accessor function")
	       (if (clos::generic-function-p (symbol-function m))
		   "generic function"
		   "function")))
	  ((and (boundp m) (or (not restrict-to) (eq restrict-to 'variable)))
	   "variable")
	  ((and (find-class m nil)
		(or (not restrict-to)
                    (eq restrict-to 'type) (eq restrict-to 'structure)))
	   (if (subtypep m 'standard-object) "class" "defstruct"))
	  (t "???")))

  (defun generate-documentation-for-package (package &optional (quiet-p nil))
    (let ((file-name (file-name-from-package package))
	  (*package* (if (not (packagep package))
			 (find-package package)
			 package)))
      (with-open-file
	  (stream (target-spec-path (string-downcase file-name) "html")
	    :direction :output :if-exists :new-version
	    :if-does-not-exist :create)
	(let ((missing nil)
	      (found nil))
	  (do-external-symbols (sym *package*)
	    (when (documentation-worthy-symbol sym)
	      (when (find-class sym nil)
		(if (or (documentation sym 'type)
                        (documentation sym 'structure))
		    (push sym found)
		    (push (list sym 'type) missing)))
	      (when (fboundp sym)
		(if (documentation sym 'function)
		    (push sym found)
		    (push (list sym 'function) missing)))
	      (when (boundp sym)
		(if (documentation sym 'variable)
		    (push sym found)
		    (push (list sym 'variable) missing)))
	      (documentation sym 'function)
	      (documentation sym 'variable)))
	  (setq missing (sort missing #'string< :key #'first))
	  (when (and missing (not quiet-p))
	    (format t "~%The following symbols are undocumented in package ~
                     ~A (~D):"
	      (package-name *package*) (length missing))
	    (loop for (m type) in missing
		  for index from 1
		  do (format t "~%~3D  ~A (~A)" index m
			     (symbol-description-string m type))))
	  (format stream "~A"
	    (or (second (assoc (package-name *package*)
			       *okbc-package-documentation-header-alist*
			       :test #'string=))
		""))
	  (let ((sorted (sort found #'string<))
		(*print-case* :downcase))
	    (format stream "~&<H3>Table of Contents:</H3>~%<OL>")
	    (loop for sym in sorted
		  do (format stream
                       "~%  <LI><A HREF=\"#~A\"><code>~A</code></A>"
		       sym sym))
	    (format stream "~%</OL>~%<HR>")
	    (when (loop for sym in sorted
			thereis (documentation sym 'variable))
	      (format stream "~&<H3>Table of Variables:</H3>~%<OL>")
	      (loop for sym in sorted
		    when (documentation sym 'variable)
		    do (format stream
			"~%  <LI><A HREF=\"#~A\"><code>~A</code></A>"
			 sym sym))
	      (format stream "~%</OL>~%<HR>"))
	    (when (loop for sym in sorted
			thereis (or (documentation sym 'type)
                                    (documentation sym 'structure)))
	      (format stream
                 "~&<H3>Table of Classes and Defstructs:</H3>~%<OL>")
	      (loop for sym in sorted
		    when (or (documentation sym 'type)
                             (documentation sym 'structure))
		    do (format stream
			"~%  <LI><A HREF=\"#~A\"><code>~A</code></A>"
			 sym sym))
	      (format stream "~%</OL>~%<HR>"))
	    (when (loop for sym in sorted
			thereis (and (documentation sym 'function)
				     (not (macro-function sym))))
	      (format stream "~&<H3>Table of Functions:</H3>~%<OL>")
	      (loop for sym in sorted
		    when (and (documentation sym 'function)
			      (not (macro-function sym)))
		    do (format stream
			"~%  <LI><A HREF=\"#~A\"><code>~A</code></A>"
			 sym sym))
	      (format stream "~%</OL>~%<HR>"))
	    (when (loop for sym in sorted
			thereis (and (documentation sym 'function)
				     (macro-function sym)))
	      (format stream "~&<H3>Table of Macros:</H3>~%<OL>")
	      (loop for sym in sorted
		    when (and (documentation sym 'function)
			      (macro-function sym))
		    do (format stream
			"~%  <LI><A HREF=\"#~A\"><code>~A</code></A>"
			 sym sym))
	      (format stream "~%</OL>~%<HR>"))
	    (when missing
	      (format stream
	       "~%<H3>The following exported symbols are undocumented:</H3>~
              ~%<OL>")
	      (loop for (m type) in missing
		    do (format stream "~%<LI><code>~A</code> <i>(~A)</i>"
			 m (symbol-description-string m type)))
	      (format stream "~%</OL>~%<HR>"))
	    (format stream "~%<DL>")
	    (loop for sym in sorted
		  do (emit-html-documentation-for sym stream *package*))
	    (format stream "~%</DL>")
	    (format stream "~%</HTML>"))))))

  (defun emit-html-documentation-for (sym stream package)
    (let ((found-p nil)
	  (*package* package))
      (when (documentation sym 'variable)
	(format stream "~%<TABLE width=100%><DT><TR><TD valign=top> <code><B>~
                        <A NAME=\"~A\">~A</A></B></code>~
		        <TD valign=top align=right> ~
                        <I>[~A]</I></TR></TABLE><DD>~A"
	  sym sym (symbol-description-string sym 'variable)
	  (link-symbols-when-possible (documentation sym 'variable)))
	(setq found-p t))
      (when (or (documentation sym 'type) (documentation sym 'structure))
	(if found-p
	    (format stream "~%<TABLE width=100%><DT><TR><TD valign=top> ~
                            <code><B>~A</B></code> " sym)
	    (format stream
	     "~%<TABLE width=100%><DT><TR><TD valign=top> <code><B>~
              <A NAME=\"~A\">~A</A></B></code> "
	      sym sym))
	(format stream "<TD valign=top align=right> ~
                          <I>[~A]</I></TR></TABLE><DD>~A"
	  (symbol-description-string sym 'type)
	  (or (documentation sym 'type)
              (documentation sym 'structure)))
	(setq found-p t))
      (when (documentation sym 'function)
	(if found-p
	    (format stream "~%<TABLE width=100%><DT><TR><TD valign=top>~
                             <TABLE><TR><TD valign=top> ~
                                    <code><B>~A</B></code> " sym)
	    (format stream "~%<TABLE width=100%><DT><TR><TD valign=top>~
                             <TABLE><TR><TD valign=top> <code><B>~
                           <A NAME=\"~A\">~A</A></B></code> "
	      sym sym))
	(let ((*package* (if (string-equal :tries (package-name *package*))
			     *package*
			     (find-package :ok-kernel))))
	  (let ((arglist #+(or Lucid EXCL)
			 (arglist sym)
			 #+Harlequin-Common-Lisp
			 (lispworks:function-lambda-list sym)
			 #-(or Lucid EXCL Harlequin-Common-Lisp)
			 (error "Implement arglist for this Lisp!")))
	    (if arglist
		(format stream " </TD><TD valign=top align=left> ~S ~
                             </TR></TABLE> ~
                             <TD valign=top align=right> <I>[~A]"
		  arglist (symbol-description-string sym 'function))
		(format stream " </TD><TD valign=top align=left> () ~
                             </TR></TABLE> ~
                             <TD valign=top align=right> <I>[~A]"
		  (symbol-description-string sym 'function)))))
	(format stream "</I></TR></TABLE><DD>~A"
	  (link-symbols-when-possible (documentation sym 'function)))
	(setq found-p t))
      (when (not found-p)
	(warn "~%Couldn't find documentation for ~S" sym)))))

;; Now generate the HTMl manuals:

(eval-when (compile)
  (format *trace-output* "~&;;; Generating TeX for manual")
  (ignore-errors (generate-manual-text))

  (progn (generate-documentation-for-package :ok-utils)
	 (generate-documentation-for-package :ok-back)
	 (generate-documentation-for-package :ok-cache)
	 (generate-documentation-for-package :okbc-test)
	 (generate-documentation-for-package :tries)))

;==============================================================================

;;; This is a bit of mysterious magic that we have to do to
;;; mark all of the hash table that are keyed on non-trivial
;;; data structures that we've consed into static memory.
;;; It turns out that even though they are static, they are
;;; relocated at disksave time, so we have to mark the hash
;;; tables as dirty.  This causes them to be rehashed on first
;;; access after the disksave.
#+Lucid
(defmethod mark-to-require-rehash ((ht hash-table))
  (setf (sys:structure-ref ht 8 t) -1))

(defmethod mark-to-require-rehash ((thing t))
  nil)

(defmethod mark-to-require-rehash ((trie structure-trie))
  (if (tries:structure-trie-arcs-hashed-p trie)
      (let ((ht (structure-trie-arcs trie)))
	(mark-to-require-rehash ht)
	(maphash #'(lambda (key value)
		     (declare (ignore key))
		     (mark-to-require-rehash (rest value)))
		 ht))
      (loop for entry in (structure-trie-arcs trie)
	    do (mark-to-require-rehash (rest entry)))))

(defmethod mark-trie-to-require-rehash (trie)
  (if (hybrid-trie-arcs-hashed-p trie)
      (let ((ht (hybrid-trie-arcs trie)))
	(mark-to-require-rehash ht)
	(maphash #'(lambda (key value)
		     (declare (ignore key))
		     (mark-trie-to-require-rehash (rest value)))
		 ht))
      (loop for entry in (hybrid-trie-arcs trie)
	    do (mark-trie-to-require-rehash (rest entry)))))

(defun mark-all-necessary-hashtables-for-rehash ()
  (mark-to-require-rehash *frame-handle-to-frame-handle-key-table*)
  (mark-to-require-rehash *frame-object-to-frame-handle-table*)
  (mark-to-require-rehash *remote-value-to-remote-value-key-table*)
  (let ((meta-kb (meta-kb-internal (local-connection))))
    (loop for kb in (get-class-instances-internal
		     (find-class 'kb) meta-kb :taxonomic :all nil)
	  do (mark-to-require-rehash kb))
    (loop for kb in (get-class-instances-internal
		     (find-class 'structure-kb) meta-kb :taxonomic :all nil)
	  do (mark-to-require-rehash kb))))

#+Lucid
(lcl:defadvice (lcl:disksave :fix-up-hash-table-flags-for-okbc) (&rest args)
  (mark-all-necessary-hashtables-for-rehash)
  (lcl:apply-advice-continue args))

;;; We can now honestly say that OKBC is loaded.
(pushnew :okbc *features*)
