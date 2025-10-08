(in-package :demos)

(defun remote-listener (&key okbchost port help
			     #+ksl-okbc user-id
			     #+ksl-okbc password
			     #+ksl-okbc ksl)

  (cond (help
	 (format t "~%(remote-listener &rest option*)")
	 (format t "~%where options include:")
	 (format t "~%    :okbchost <hostname>: the host to connect to")
	 (format t "~%    :port <port number> : the port to connect to")
	 #+ksl-okbc
	 (format t "~%    :ksl  t      : run against the frame ontology")
	 (format t "~%                  If you pick Ontolingua:")
	 (format t "~%    :user-id <id>       : your KSL user id")
	 (format t "~%    :password <pwd>     : your KSL password"))
	(t (let  ((ksl-p #+ksl-okbc ksl #-ksl-okbc nil)
		  (user-id  #+ksl-okbc user-id  #-ksl-okbc nil)
		  (password #+ksl-okbc password #-ksl-okbc nil))
	     (let ((connection (get-demo-connection
				(or okbchost "ontolingua.stanford.edu")
				(or port 5915) user-id password ksl-p)))
	       (let ((meta-kb (meta-kb :connection connection)))
		 (let ((get-pretty-kb-types-proc
			(create-procedure
			 :arguments "()"
			 :body
			 "(let ((prototypes (get-kb-types)))
			    (do-list (x prototypes)
			      (list x (frs-name :kb-type x))))"
			 :kb meta-kb))
		       (get-pretty-kbs-of-type-proc
			(create-procedure
			 :arguments "(type)"
			 :body
			 "(let ((kbs (get-kbs-of-type :kb-type type)))
			    (do-list (x kbs)
			      (list x (get-frame-pretty-name x :kb kb))))"
			 :kb meta-kb)))
		   (register-procedure 'get-pretty-kb-types-proc
				       get-pretty-kb-types-proc :kb meta-kb)

		   (register-procedure 'get-pretty-kbs-of-type-proc
				       get-pretty-kbs-of-type-proc :kb meta-kb)
		   (loop
		    do
		    (let ((kb-type-specs
			   (call-procedure 'get-pretty-kb-types-proc
					   :kb meta-kb :arguments nil)))
		      (format *query-io* "~&Pick a KB type: ")
		      (loop for spec in kb-type-specs
			    for pname = (second spec)
			    for count from 0
			    do (format *query-io* "~&~2d   ~A" count pname))
		      (let ((kb-type
			     (loop for res = (prompt-and-read-frame-name
					      "Choose" 0)
				   for choice =
				   (or (and res (not (equal res ""))
					    (ignore-errors
					     (parse-integer res)))
				       -1)
				   when (and (>= choice 0)
					     (< choice (length kb-type-specs)))
				   return (first (nth choice kb-type-specs)))))
			(let ((kb-specs
			       (call-procedure
				'get-pretty-kbs-of-type-proc :kb meta-kb
				:arguments (list kb-type))))
			  (let ((kb (case (length kb-specs)
				      (0 (format t "~%There are no KBs.  ~
                                             Please try a different KB type.")
					 nil)
				      (1 (format t "~%There is only one KB of ~
                                                      this type: ~S~%"
					   (second (first kb-specs)))
					 (first (first kb-specs)))
				      (otherwise
				       (format *query-io* "~&Pick a KB: ")
				       (loop for spec in kb-specs
					     for pname = (second spec)
					     for count from 0
					     do (format *query-io*
						 "~&~2d   ~A" count pname))
				       (loop for res =
					     (prompt-and-read-frame-name
					      "Choose" 0)
					     for choice =
					     (or (and res (not (equal res ""))
						      (ignore-errors
						       (parse-integer res)))
						 -1)
					     when
					     (and (>= choice 0)
						  (< choice (length kb-specs)))
					     return
					     (first (nth choice kb-specs)))))))
			    (when kb
			      (unwind-protect
				   (okbc-listener :kb kb)
				(when connection
				  (close-connection connection :error-p nil
						    :force-p t))))))))))))))))
