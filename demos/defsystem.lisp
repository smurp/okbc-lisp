(in-package :user)

#-OKBC (error "You cannot load the OKBC demos you have loaded OKBC")

(defvar *okbc-demo-root*
  (make-pathname :directory (append (butlast
				     (pathname-directory *okbc-source-root*))
				    '("demos"))
		 :defaults *okbc-source-root*))

#+KSL-makesystem
(define-ksl-system :okbc-demos
  :modules
    `((package () ())
      ((:body demo-general demo2 file-system-kb kb-summary remote-listener)
       (package) (package)))
  :source *okbc-demo-root*
  :binary *okbc-demo-root*)

#+:MK-DEFSYSTEM
(make:defsystem okbc-demos
    :source-pathname *okbc-demo-root*
    :source-extension #-(or TI :ACLPC) "lisp" #+TI "LISP" #+:ACLPC "lsp"
    :binary-pathname *okbc-demo-root*
    :components
    ((:module package
	      :source-pathname ""
	      :components ((:file "package")))
     (:module body
	      :source-pathname ""
	      :components ((:file "demo-general")
			   (:file "demo2")
			   (:file "file-system-kb")
			   (:file "kb-summary")
			   (:file "remote-listener"))
	      :depends-on (package))))


(defun compile-load-okbc-demos (&optional (force-compile-p t))
  #+(or KSL-makesystem) (declare (ignore force-compile-p))
  #+KSL-makesystem (make-system::compile-system :okbc-demos)
  #+:MK-DEFSYSTEM
  (with-okbc-compilation-environment
    (make:operate-on-system 'okbc-demos :compile :force force-compile-p))
  #-(or MK-DEFSYSTEM KSL-makesystem)
  (with-compilation-unit ()
    (okbc-cl  *okbc-demo-root* force-compile-p package)
    (okbc-c-l *okbc-demo-root* force-compile-p
	      demo-general demo2 file-system-kb kb-summary remote-listener)))

