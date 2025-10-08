(in-package :fskb)

(defokbcclass ok-back::abstract-file-system-kb-kb () ())

(defokbcclass file-system-kb (ok-back::abstract-file-system-kb-kb
				  frame-name-interning-mixin
				  handle-number-of-values-mixin
				  default-inheritance-mixin
				  kb)
  ((root :initarg :root :initform (pathname "/") :accessor root)
   (versions-p :initarg :versions-p :accessor versions-p :initform nil)))

(defnetwork-okbc-kb file-system-kb ())

;==============================================================================

(defmethod concrete-kb-class-from-abstract-kb-class-name
    ((name (eql 'ok-back::abstract-file-system-kb-kb)))
  'file-system-kb)

(defmethod key-for-frame-handle-uniquification 
  ((thing pathname) (kb file-system-kb)) 
  (namestring thing))

;==============================================================================

(defmethod shared-initialize :after
  ((instance file-system-kb) (slot-names t) &rest args)
  (declare (ignore args))
  (setf (root instance) (pathname (root instance))))

(defmethod kb-testfn ((kb file-system-kb)) 'equal)

(defmethod get-instance-types-internal
    ((frame t) (kb file-system-kb) (inference-level (eql :direct))
     (number-of-values t) (kb-local-only-p t))
  (let ((instance (or (coerce-to-frame-internal
		       frame kb nil kb-local-only-p)
		      frame)))
    (and (pathnamep instance)
	 (if (class-p-internal instance kb kb-local-only-p)
	     (list :directory)
	     (list (make-pathname :name nil :type nil :version nil
				  :defaults instance))))))

(defmethod put-instance-types-internal
    ((frame t) (new-types t) (kb file-system-kb) (kb-local-only-p t))
  (error 'read-only-violation :error-message
	 "Cannot put types in this kind of KB"))

(defmethod primitive-p-internal
    ((class t) (kb file-system-kb) (kb-local-only-p t))
  t)

(defun version-path-p (p)
  (and (pathnamep p)
       (find #\~ (pathname-type p) :test #'char=)))

(defmethod get-class-instances-internal
    ((class t) (kb file-system-kb) (inference-level (eql :direct))
     (number-of-values t) (kb-local-only-p t))
  (if (class-p-internal class kb kb-local-only-p)
      (loop for path in (directory (make-pathname :defaults class :name :wild
						  :type :wild))
	    unless (or (member (pathname-name path) '(nil "" ".")
			       :test #'equal)
		       (and (not (versions-p kb)) (version-path-p path))
		       (class-p-internal path kb kb-local-only-p))
	    collect path)
      nil))

(defmethod get-class-superclasses-internal
    ((class t) (kb file-system-kb) (inference-level (eql :direct))
     (number-of-values t) (kb-local-only-p t))
  (if (class-p-internal class kb kb-local-only-p)
      (let ((directories (butlast (pathname-directory class))))
	(if (and directories
		 (>= (length directories)
		     (length (pathname-directory (root kb)))))
	    (list (make-pathname :defaults class :directory directories))
	    nil))
      nil))

(defmethod put-class-superclasses-internal
    ((class t) (new-superclasses t) (kb file-system-kb)
     (kb-local-only-p t))
  (error 'read-only-violation :error-message
	 "Cannot put superclasses in this kind of KB"))

(defun directory-file-p (path)
  #-(or Lucid EXCL) (error "directory-file-p not implemented yet for ~S" path)
  #+(or Lucid EXCL)
  (#+Lucid lucid::%directory-file-p
   #+EXCL excl::file-directory-p
   path))

(defmethod get-class-subclasses-internal
    ((class t) (kb file-system-kb) (inference-level (eql :direct))
     (number-of-values t) (kb-local-only-p t))
  (if (class-p-internal class kb kb-local-only-p)
      (let ((contents (directory (make-pathname :defaults class :name :wild
						:type :wild))))
	(loop for path in contents
	      when (and (directory-file-p path)
			(not (member (pathname-name path) '(nil "" ".")
				     :test #'equal))
			(or (not (versions-p kb)) (not (version-path-p path))))
	      collect (make-pathname :defaults class
				     :directory
				     (append (pathname-directory class)
					     (list (dir-component-from-path
						     path)))
				     :name nil :type nil :version nil)))
      nil))

(defmethod put-class-subclasses-internal
    ((class t) (new-subclasses t) (kb file-system-kb)
     (kb-local-only-p t))
  (error 'read-only-violation :error-message
	 "Cannot put subclasses in this kind of KB"))
  
(defmethod class-p-internal
    ((thing t) (kb file-system-kb) (kb-local-only-p t))
  (and (pathnamep thing)
       (not (or (pathname-name thing) (pathname-type thing)
		(pathname-version thing)))))

(defmethod facet-p-internal
    ((thing t) (kb file-system-kb) (kb-local-only-p t))
  nil)

(defmethod get-frame-pretty-name-internal
    ((frame t) (kb file-system-kb) (kb-local-only-p t))
  (let ((frame
	 (coerce-to-frame-internal frame kb t kb-local-only-p)))
    (if frame
	(namestring frame)
	nil)))

(defmethod get-frame-name-internal
    ((frame t) (kb file-system-kb) (kb-local-only-p t))
  ;;; This will be handled by frame-name-interning-mixin
  nil)

(defun dir-component-from-path (path)
  (if (pathname-type path)
      (concatenate 'string (pathname-name path) "." (pathname-type path))
      (pathname-name path)))

(defmethod file-system-kb-coerce-to-frame
 ((frame string) kb error-p kb-local-only-p)
  (let ((path (ignore-errors (pathname frame))))
    (if path
	(file-system-kb-coerce-to-frame
	 path kb error-p kb-local-only-p)
	(if error-p
	    (error 'not-coercible-to-frame :frame frame :kb kb)
	    (values nil nil)))))

(defmethod file-system-kb-coerce-to-frame
 ((frame pathname) kb error-p (kb-local-only-p t))
 (if (or (pathname-name frame) (pathname-type frame))
     (if (and (probe-file frame)
	      (or (versions-p kb) (not (version-path-p frame))))
	 (values (if (directory-file-p frame)
		     (make-pathname :defaults frame
				    :name nil :type nil
				    :directory
				    (append (pathname-directory frame)
					    (list (dir-component-from-path
						   frame))))
		     frame)
		 t)
	 (if error-p
	     (error 'not-coercible-to-frame :frame frame :kb kb)
	     (values nil nil)))
     (if (directory-file-p frame)
	 (values frame t)
	 (if error-p
	     (error 'not-coercible-to-frame :frame frame :kb kb)
	     (values nil nil)))))

(defmethod file-system-kb-coerce-to-frame
 ((frame t) kb error-p (kb-local-only-p t))
 (if error-p
     (error 'not-coercible-to-frame :frame frame :kb kb)
     (values nil nil)))

#-(and KSL HTTP)
(defvar user::*ls-program*
      #+Lucid (progn #+Solaris "/usr/ucb/ls"
		     #-Solaris "/bin/ls")
      #+EXCL  (progn #-Sunos4 "/usr/ucb/ls"
		     #+Sunos4 "/bin/ls")
      #+Harlequin-Common-Lisp
              (progn #+Sunos5 "/usr/ucb/ls"
		     #-Sunos5 "/bin/ls")
    #-(or Lucid EXCL Harlequin-Common-Lisp)
    (error "Implement me for this Lisp"))

(defun get-directory-line (path)
  #+(or Lucid EXCL Harlequin-Common-Lisp)
  (ignore-errors
   (if (probe-file path)
       (with-open-stream
	   (str #+Lucid
		(lcl:run-program user::*ls-program*
				 :arguments
				 (if (directory-file-p path)
				     (list "-ldg" (namestring path))
				     (list "-lg" (namestring path)))
				 :output :stream :wait nil)
		#+EXCL
		(excl::run-shell-command
		 (concatenate 'string
			      user::*ls-program*
			      (if (directory-file-p path) " -ldg " " -lg ")
			      (namestring path))
		 :output :stream
		 :wait nil)
		#+Harlequin-Common-Lisp
		(make-string-input-stream
		 (with-output-to-string (str)
		   (system::call-system-showing-output
		    (concatenate 'string
				 user::*ls-program*
				 (if (directory-file-p path) " -ldg " " -lg ")
				 (namestring path))
		    :output-stream str))))
	 (read-line str))
       nil))
  #-(or Lucid EXCL Harlequin-Common-Lisp)
  (error "Implement me for this Lisp."))

(defun target-of-link (path)
  (let ((line (get-directory-line path)))
    (and line
	 (char= #\l (char line 0))
	 (let ((pos (search "-> " line :test #'char=)))
	   (and pos (pathname (subseq line (+ pos 3))))))))

(defun chase-links-if-need-be (path)
  (let ((target (target-of-link path)))
    (if target
	(chase-links-if-need-be target)
	path)))

(defmethod coerce-to-frame-internal
    ((thing t) (kb file-system-kb) (error-p t) (kb-local-only-p t))
  (file-system-kb-coerce-to-frame thing kb error-p kb-local-only-p))

(defmethod get-frame-in-kb-internal
    ((thing t) (kb file-system-kb) (error-p t) (kb-local-only-p t))
  (let ((frame (chase-links-if-need-be
		(coerce-to-frame-internal
		 thing kb error-p kb-local-only-p))))
    (if frame
	(let ((rootd (pathname-directory (root kb)))
	      (framed (pathname-directory frame)))
	  (if (>= (length framed) (length rootd))
	      (if (loop for dr in rootd
			for df in framed
			always (equal dr df))
		  (values frame t)
		  (if error-p
		      (error 'not-coercible-to-frame :frame frame :kb kb)
		      (values nil nil)))))
	(if error-p
	    (error 'not-coercible-to-frame :frame frame :kb kb)
	    (values nil nil)))))

(defparameter *file-system-kb-behaviors*
  '((:constraint-checking-time :never)
    (:constraint-report-time :never)
    (:facets nil)
    (:annotations)
    (:inheritance :incoherence)
    (:class-slot-types :own)
    (:default-test-fn equal)))

(defmethod put-behavior-values-internal
    ((behavior t) (values t) (kb file-system-kb))
  (continuable-assert
     nil illegal-behavior-values :behavior behavior :proposed-values values))

(defmethod get-behavior-values-internal
    ((behavior t) (kb file-system-kb))
  (rest (assoc behavior *file-system-kb-behaviors*)))

(defmethod get-kb-behaviors-internal
    ((kb-type-or-kb file-system-kb) (connection t))
  (mapcar #'first *file-system-kb-behaviors*))

(defmethod get-behavior-supported-values-internal
    ((behavior t) (kb file-system-kb))
  (get-behavior-values-internal behavior kb))

(defmethod get-kbs-of-type-internal
    ((kb-type file-system-kb) (connection t))
  (let ((meta-kb (meta-kb-internal connection)))
    (relation-transitive-closure
     (class-of kb-type) meta-kb
     #'tuple-kb:get-class-instances-internal-implementation
     (list meta-kb :direct :all t)
     #'get-class-subclasses-internal
     (list meta-kb :direct :all t)
     t)))

(defmethod get-kb-roots-internal
    ((kb file-system-kb) (selector t) (kb-local-only-p t))
  (list (root kb)))

(defmethod get-kb-frames-internal
  ((kb file-system-kb) (kb-local-only-p t))
  (let ((result nil)
	(ht (make-hash-table :test #'equal)))
    (labels ((rec (path)
	       (let ((frame (get-frame-in-kb-internal
			     path kb nil kb-local-only-p)))
		 (when (and frame (not (gethash frame ht)))
		   (setf (gethash frame ht) t)
		   (push frame result)
		   (loop for p in (if (class-p-internal
				       frame kb kb-local-only-p)
				      (directory 
				       (make-pathname :name :wild
						      :type :wild
						      :defaults frame))
				      (directory frame))
			 unless (or (member (pathname-name p) '(nil "" ".")
					    :test #'equal)
				    (and (not (versions-p kb))
					 (version-path-p p)))
			 do (rec p))))))
      (rec (root kb)))
    result))

(defun frame-permissions (path)
  (let ((line (get-directory-line path))) (and line (subseq line 0 10))))

(defun frame-owner (path)
  (let ((line (get-directory-line path)))
    (and line (string-trim '(#\space) (subseq line 14 23)))))

(defun frame-group (path)
  (let ((line (get-directory-line path)))
    (and line (string-trim '(#\space) (subseq line 23 31)))))

(defun frame-link-p (path)
  (let ((line (get-directory-line path)))
    (and line (char= #\l (char line 0)))))

(defun frame-length (path)
  (let ((line (get-directory-line path)))
    (and line
	 #+(or Harlequin-Common-Lisp EXCL)
	 (parse-integer line
			:start 22
			:end 34)
	 #+Lucid
	 (progn #+Solaris
		(parse-integer line :start 33 :end 42)
		#-Solaris
		(parse-integer line :start 31 :end 40))
	 #-(or Lucid EXCL Harlequin-Common-Lisp)
	 (error "Implement me for this Lisp"))))

(defun frame-write-date (path)
  (file-write-date path))

(defmethod slot-p-internal ((thing t) (kb file-system-kb)
			    (kb-local-only-p t))
  (member thing '(:permissions :owner :group :length :write-date)))

(defmethod get-frame-slots-internal
    ((frame t) (kb file-system-kb) (inference-level (eql :direct))
     (slot-type (eql :own)) (kb-local-only-p t))
  '(:permissions :owner :group :length :write-date))

(defmethod get-frame-slots-internal
    ((frame t) (kb file-system-kb) (inference-level (eql :direct))
     (slot-type t) (kb-local-only-p t))
  nil)

(defmethod get-slot-values-in-detail-internal
    ((frame t) (slot t) (kb file-system-kb) (inference-level t)
     (slot-type (eql :own)) (number-of-values t) (value-selector t)
     (kb-local-only-p t))
  (let ((frame (coerce-to-frame-internal frame kb t kb-local-only-p)))
    (values
     (loop for v in
	   (case slot
		 (:permissions (list (frame-permissions frame)))
		 (:owner (list (frame-owner frame)))
		 (:group (list (frame-group frame)))
		 (:length (list (frame-length frame)))
		 (:write-date (list (frame-write-date frame)))
		 (otherwise nil))
	   collect (list v t nil))
     t nil nil)))

(defmethod detach-slot-internal ((frame t) (slot t) (kb file-system-kb)
				 (slot-type t) (kb-local-only-p t))
  (error 'read-only-violation :error-message
	 "Cannot detach slots in this kind of KB"))

(defmethod attach-slot-internal ((frame t) (slot t) (kb file-system-kb)
				 (slot-type t) (kb-local-only-p t))
  (error 'read-only-violation :error-message
	 "Cannot attach slots in this kind of KB"))

(defmethod put-slot-values-internal
    ((frame t) (slot t) (values t) (kb file-system-kb) (slot-type t)
     (value-selector t) (kb-local-only-p t))
  (error 'read-only-violation :error-message
	 "Cannot put slot values in this kind of KB"))

(defmethod get-slot-values-in-detail-internal
    ((frame t) (slot t) (kb file-system-kb) (inference-level t)
     (slot-type (eql :own)) (number-of-values t)
     (value-selector (eql :default-only)) (kb-local-only-p t))
  nil)

(defmethod get-slot-values-in-detail-internal
    ((frame t) (slot t) (kb file-system-kb) (inference-level t)
     (slot-type (eql :template)) (number-of-values t) (value-selector t)
     (kb-local-only-p t))
  nil)

(defmethod get-slot-facets-internal
    ((frame t) (slot t) (kb file-system-kb) (inference-level t)
     (slot-type t) (kb-local-only-p t))
  nil)

(defmethod detach-facet-internal ((frame t) (slot t) (facet t)
				  (kb file-system-kb)
				 (slot-type t) (kb-local-only-p t))
  (error 'read-only-violation :error-message
	 "Cannot detach facets in this kind of KB"))

(defmethod attach-facet-internal ((frame t) (slot t) (facet t)
				  (kb file-system-kb)
				 (slot-type t) (kb-local-only-p t))
  (error 'read-only-violation :error-message
	 "Cannot attach facets in this kind of KB"))

(defmethod get-facet-values-in-detail-internal
    ((frame t) (slot t) (facet t) (kb file-system-kb) (inference-level t)
     (slot-type t) (number-of-values t) (value-selector t) (kb-local-only-p t))
  nil)

(defmethod put-facet-values-internal
    ((frame t) (slot t) (facet t) (values t) (kb file-system-kb)
     (slot-type t) (value-selector t) (kb-local-only-p t))
  (error 'read-only-violation :error-message
	 "Cannot put facet values in this kind of KB"))

(defstruct (file-system-kb-locator (:include abstract-kb-locator))
  (path nil))

(defmethod create-kb-locator-internal ((thing file-system-kb)
				       (kb-type file-system-kb)
				       (connection t))
  (let ((instance (make-file-system-kb-locator
		   :name (name thing)
		   :path (make-pathname
			  :defaults tuple-kb::*root-path-for-saved-tuplekbs*
			  :name (with-standard-io-syntax
				 (prin1-to-string (name thing)))
			  :type "fskb"))))
    (put-instance-types-internal instance :kb-locator
				 (meta-kb-internal connection) t)
    instance))

(defmethod find-kb-locator-internal
    ((thing file-system-kb-locator) (kb-type file-system-kb) 
     (connection t))
  thing)

(defmethod find-kb-locator-internal
    ((thing symbol) (kb-type file-system-kb) (connection t))
  (let ((type (ignore-errors (get-kb-type-internal thing connection))))
    (and type (find-kb-locator-internal type kb-type connection))))

(defmethod find-kb-locator-internal
    ((thing file-system-kb) (kb-type file-system-kb) (connection t))
  (let ((locators (get-class-instances-internal
		   :kb-locator (meta-kb-internal connection)
		   :taxonomic :all nil)))
    (loop for locator in locators
	  when (and (typep locator 'file-system-kb-locator)
		    (eq (name locator) (name thing)))
	  return locator
	  finally (return (create-kb-locator-internal
			   thing kb-type connection)))))

(defmethod save-kb-internal ((kb file-system-kb) (error-p t))
  (continuable-assert (not error-p) nil
                      "Cannot save file system kbs")
  nil)

(defmethod save-kb-as-internal
  ((new-name-or-locator t) (kb file-system-kb))
  (generic-error "Cannot rename these KBs"))

(defmethod close-kb-internal ((kb file-system-kb) (save-p t))
  (when save-p (save-kb-internal kb t))
  (let ((locator (find-kb-locator-internal kb kb (connection kb))))
    (put-instance-types-internal
     locator nil (meta-kb-internal (local-connection)) t)
    (put-instance-types-internal
     kb nil (meta-kb-internal (local-connection)) t)
    (when (eq kb (current-kb)) (setq *current-kb* nil))))

(defmethod open-kb-internal
    ((kb-locator t) (kb-type file-system-kb) (connection t) (error-p t))
  (generic-error "Cannot open this kind of KB"))

(defmethod openable-kbs-internal
   ((kb-type file-system-kb) (connection t) (place t))
  nil)

(defmethod expunge-kb-internal ((kb-locator t) (kb-type file-system-kb)
				(connection t) (error-p t))
  (when error-p (generic-error "Cannot expunge CLOS KBs using OKBC")))

;(defmethod expunge-kb-internal ((kb file-system-kb) (connection t) (error-p t))
;  (close-kb-internal kb nil))

(defmethod delete-slot-internal
  ((slot t) (kb file-system-kb) (kb-local-only-p t))
  (error 'read-only-violation :error-message
	 "Cannot delete slots in this kind of KB"))

(defmethod delete-facet-internal
  ((facet t) (kb file-system-kb) (kb-local-only-p t))
  (error 'read-only-violation :error-message
	 "Cannot delete facets in this kind of KB"))

(defmethod rename-slot-internal ((slot t) (new-name t) (kb file-system-kb)
				 (kb-local-only-p t))
  (error 'read-only-violation :error-message
	 "Cannot rename slots in this kind of KB"))

(defmethod rename-facet-internal
  ((facet t) (new-name t) (kb file-system-kb) (kb-local-only-p t))
  (error 'read-only-violation :error-message
	 "Cannot rename facets in this kind of KB"))

(defmethod delete-frame-internal
    ((frame t) (kb file-system-kb) (kb-local-only-p t))
  (error 'read-only-violation :error-message
	 "Cannot delete frames in this kind of KB"))

(defmethod create-facet-internal
    ((name t) (kb file-system-kb) (frame-or-nil t) (slot-or-nil t)
     (slot-type t) (direct-types t) (doc t) (own-slots t) (own-facets t)
     (handle t) (pretty-name t) (kb-local-only-p t))
  (error 'read-only-violation :error-message
	 "Cannot create facets in this kind of KB"))

(defmethod create-slot-internal
    ((name t) (kb file-system-kb) (frame-or-nil t)
     (slot-type t) (direct-types t) (doc t) (own-slots t) (own-facets t)
     (handle t) (pretty-name t) (kb-local-only-p t))
  (error 'read-only-violation :error-message
	 "Cannot create slots in this kind of KB"))

(defmethod create-individual-internal
    ((name t) (kb file-system-kb) (direct-types t) (doc t) (own-slots t)
     (own-facets t) (handle t) (pretty-name t) (kb-local-only-p t))
  (error 'read-only-violation :error-message
	 "Cannot create individuals in this kind of KB"))

(defmethod create-class-internal
    ((name t) (kb file-system-kb) (direct-types t) (direct-superclasses t)
     (primitive-p t) (doc t) (template-slots t) (template-facets t)
     (own-slots t) (own-facets t) (handle t) (pretty-name t)
     (kb-local-only-p t))
  (error 'read-only-violation :error-message
	 "Cannot create classes in this kind of KB"))

(defmethod put-frame-name-internal
    ((frame t) (new-name t) (kb file-system-kb) (kb-local-only-p t))
  (error 'read-only-violation :error-message
	 "Cannot put frame name in this kind of KB"))

(defmethod put-frame-pretty-name-internal
    ((frame t) (name t) (kb file-system-kb) (kb-local-only-p t))
  (error 'read-only-violation :error-message
	 "Cannot put frame pretty name in this kind of KB"))

(defmethod decontextualize-internal
  ((value pathname) (from-context t) (kb file-system-kb))
  (multiple-value-bind (frame found-p)
      (coerce-to-frame-internal value kb nil nil)
    (if found-p
        (frs-independent-frame-handle-internal frame kb nil)
      value)))

(defmethod decontextualize-internal
  ((value cons) (from-context t) (kb file-system-kb))
  (cons (decontextualize-internal (first value) from-context kb)
	(decontextualize-internal (rest  value) from-context kb)))

(defmethod allocate-frame-handle-internal 
  ((frame-name t) (frame-type t) (kb file-system-kb)
   (frame-handle frame-handle))
  frame-handle)

(defmethod eql-in-kb-internal
    ((arg0 t) (arg1 t) (kb file-system-kb) (kb-local-only-p t))
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
	      nil))))


;==============================================================================

(defparameter *file-system-kb*
  (let ((connection (local-connection)))
    (or (find-kb-of-type-internal
	 '$file-system-kb$
	 (get-kb-type-internal 'file-system-kb connection)
	 (local-connection))
	(create-kb-internal
	 '$file-system-kb$
	 (get-kb-type-internal 'file-system-kb connection)
	 nil (list :root (probe-file "~/"))
	 connection))))
