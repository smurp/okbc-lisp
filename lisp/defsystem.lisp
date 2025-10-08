(in-package :user)

#+Lucid
(when #+SUN-OS (progn #+Solaris t #-Solaris nil)
      #+IRIX t
      #+AIX  t
      #-(or SUN-OS IRIX AIX) (error "Implement me (1)!")
      (pushnew :No-Underscore-In-Foreign-Functions *features*))

(eval-when (compile load eval)
  (defvar *okbc-source-root*
    (make-pathname :name nil :type nil :defaults
		   #+Lucid lcl::*source-pathname*
		   #+MCL ccl::*loading-file-source-file*
		   #+TI sys:fdefine-file-pathname
		   #-(or Lucid MCL TI) *load-pathname*)))

(defvar *binary-file-type*
  #+Lucid (first lcl::*load-binary-pathname-types*)
  #+EXCL excl::*fasl-default-type*
  #+MCL (pathname-type *.fasl-pathname*)
  #+Harlequin-common-lisp
  (progn #+win32 "fsl"
         #-(or win32)
         (error "You must define a binary file type for this HCL ~
                 implementation."))
  #-(or Lucid EXCL MCL Harlequin-Common-Lisp)
  (error "You must define a binary file type for this Lisp implementation."))

(defmacro with-okbc-compilation-environment (&body body)
  `(let (#+Allegro (excl:*global-gc-behavior* :auto)
	 #+Allegro (cl:*compile-verbose* nil)
	 #+Allegro (old-switch (sys:gsgc-switch :print)))
     (unwind-protect
	(progn #+Allegro (setf (sys:gsgc-switch :print) nil) ,@body)
       (progn #+Allegro (setf (sys:gsgc-switch :print) old-switch)
	      nil))))

;;; The following is a trivial build sequence for people who have not crafted
;;; their own defsystems for OKBC
(defmacro okbc-cl (root force-compile-p &rest files)
  ;; Compile and load sequentially.
  `(flet ((okbc-pathname (name)
	   (make-pathname :name (string-downcase name)
			  :defaults ,root)))
    (with-okbc-compilation-environment
      (loop for file in ',files
	    for path = (okbc-pathname file)
	    for binpath = (make-pathname :defaults path
					 :type *binary-file-type*)
	    when (or (not (probe-file binpath)) ,force-compile-p)
	    do (compile-file path :output-file binpath)
	    do (load path)))))


(defmacro okbc-c-l (root force-compile-p &rest files)
  ;; compile a bunch of files in the current environment, and
  ;; then load them.
  `(flet ((okbc-pathname (name)
	   (make-pathname :name (string-downcase name)
			  :defaults ,root)))
    (with-okbc-compilation-environment
      (loop for file in ',files
	    for path = (okbc-pathname file)
	    for binpath = (make-pathname :defaults path
					 :type *binary-file-type*)
	    when (or (not (probe-file binpath)) ,force-compile-p)
	    do (compile-file (okbc-pathname file)))
      (loop for file in ',files
	    do (load (okbc-pathname file))))))

#+KSL-makesystem
(define-ksl-system :okbc
    :modules
  `((package () ())
    (macros (package) (package) :force-downwards-compilation)
    (tries (package macros) (package macros) :force-downwards-compilation)
    (kb (macros tries) (macros tries) :force-downwards-compilation)
    ((:kb-defs
      clos-defs
      network-defs
      tuple-kb-defs)
     (kb) (kb) :force-downwards-compilation)
    ((:main core-a-to-f core-g-to-l core-m-to-z core conditions)
     (:kb-defs) (:kb-defs)
     :force-downwards-compilation)
    ((:extra auxilliary eval) (:main) (:main) :force-downwards-compilation)
    ((:inheritance default-inheritance) (:main) (:main)
     :force-downwards-compilation)
    ((:knowledge-model constraints tell-and-ask) (:main) (:main))
    ((:compliance compliance) (:main) (:main))
    ((:server-support #+(and Allegro allegro-version>= (version>= 5))
      server)
     (:main :kb-defs :inheritance :knowledge-model)
     (:main :kb-defs :inheritance :knowledge-model))
    ((:back-ends
      clos-methods
      network-methods
      meta-kb-methods
      tuple-kb-methods
      tuple-store)
     (:main :kb-defs :inheritance :knowledge-model :server-support)
     (:main :kb-defs :inheritance :knowledge-model :server-support))
    ((:test test-suite)
     (:main :kb-defs :back-ends :extra)
     (:main :kb-defs :back-ends :extra))
    ((:late wrapup version)
     (:main :kb-defs :back-ends :extra :compliance :knowledge-model
      :inheritance kb tries macros :test)
     (:main :kb-defs :back-ends :extra :compliance :knowledge-model
      :inheritance kb tries macros :test)))
  :source *okbc-source-root*
  :binary *okbc-source-root*)

#+:MK-DEFSYSTEM
(make:defsystem okbc
    :source-pathname *okbc-source-root*
    :source-extension #-(or TI :ACLPC) "lisp" #+TI "LISP" #+:ACLPC "lsp"
    :binary-pathname *okbc-source-root*
    :components
    ((:module util
	      :source-pathname ""
	      :components ((:file "package")
			   (:file "macros" :depends-on ("package"))
			   (:file "tries" :depends-on ("package" "macros"))
			   (:file "kb" :depends-on ("macros" "tries"))))
     (:module kb-defs
	      :source-pathname ""
	      :components ((:file "clos-defs")
			   (:file "network-defs")
			   (:file "tuple-kb-defs"))
	      :depends-on (util))
     (:module main
	      :source-pathname ""
	      :components ((:file "core-a-to-f")
			   (:file "core-g-to-l")
			   (:file "core-m-to-z")
			   (:file "core")
			   (:file "conditions"))
	      :depends-on (kb-defs))
     (:module extra
	      :source-pathname ""
	      :components ((:file "auxilliary")
			   (:file "eval"))
	      :depends-on (main))
     (:module inheritance
	      :source-pathname ""
	      :components ((:file "default-inheritance"))
	      :depends-on (main))
     (:module knowledge-model
	      :source-pathname ""
	      :components ((:file "constraints")
			   (:file "tell-and-ask"))
	      :depends-on (main))
     (:module compliance
	      :source-pathname ""
	      :components ((:file "compliance"))
	      :depends-on (main))
     (:module server-support
	      :source-pathname ""
	      :components (#+(and Allegro allegro-version>= (version>= 5))
			   (:file "server"))
	      :depends-on (main kb-defs inheritance knowledge-model))
     (:module back-ends
	      :source-pathname ""
	      :components ((:file "clos-methods")
			   (:file "network-methods")
			   (:file "meta-kb-methods")
			   (:file "tuple-kb-methods")
			   (:file "tuple-store"))
	      :depends-on (main kb-defs inheritance knowledge-model
				server-support))
     (:module test
	      :source-pathname ""
	      :components ((:file "test-suite"))
	      :depends-on (main kb-defs back-ends extra))
     (:module late
	      :source-pathname ""
	      :components ((:file "wrapup")
			   (:file "version"))
	      :depends-on (main kb-defs back-ends extra compliance))))

#|
;;; An Allegro defsystem will look something like this:
#+EXCL
(defsystem OKBC (:default-pathname #.*okbc-source-root*)
  (:module-group :kb-defs
		 (:parallel "clos-defs" "network-defs" "tuple-kb-defs"))
  (:module-group :main
		 (:parallel "core-a-to-f" "core-g-to-l" "core-m-to-z"
			    "core" "conditions"))
  (:module-group :extra (:parallel "auxilliary" "eval"))
  (:module-group :knowledge-model (:parallel "constraints" "tell-and-ask"))
  (:module-group :server-support #+(and Allegro allegro-version>= (version>= 5))
		 (:serial "server"))
  (:module-group :back-ends
		 (:parallel "clos-methods"
			    "network-methods"
			    "meta-kb-methods"
			    "tuple-kb-methods"
			    "tuple-store"))
  (:module-group :late (:parallel "wrapup" "version"))
  (:serial "package"
	   (:definitions "macros"
	       (:serial "tries" "kb" :kb-defs
			(:definitions :main
			    (:parallel :extra :knowledge-model
				       "compliance" "default-inheritance"
				       :server-support)
			  :back-ends "test-suite" :late)))))
|#

;==============================================================================

(defun compile-load-okbc (&optional (force-compile-p t))
  #+(or KSL-makesystem) (declare (ignore force-compile-p))
  #+KSL-makesystem (make-system::compile-system :okbc)
  #+:MK-DEFSYSTEM
  (with-okbc-compilation-environment
      (make:operate-on-system 'okbc :compile :force force-compile-p))
  #-(or MK-DEFSYSTEM KSL-makesystem)
  (with-compilation-unit ()
    (okbc-cl  *okbc-source-root* force-compile-p
	      package macros tries kb)
    (okbc-c-l *okbc-source-root* force-compile-p
	      clos-defs network-defs tuple-kb-defs)
    (okbc-c-l *okbc-source-root* force-compile-p
	      core core-a-to-f core-g-to-l core-m-to-z conditions)
    (okbc-c-l *okbc-source-root* force-compile-p
	      eval auxilliary default-inheritance constraints tell-and-ask
	      compliance)
    (okbc-c-l *okbc-source-root* force-compile-p
	      #+(and Allegro allegro-version>= (version>= 5)) server)
    (okbc-c-l *okbc-source-root* force-compile-p
	      clos-methods network-methods
	      tuple-kb-methods meta-kb-methods
	      tuple-store)
    (okbc-cl  *okbc-source-root* force-compile-p
	      test-suite)
    (okbc-cl  *okbc-source-root* force-compile-p
	      wrapup version)))
