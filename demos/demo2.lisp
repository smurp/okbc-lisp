(in-package :demos)

(defparameter *frame-name* nil)
(defparameter *slot-name* nil)
(defparameter *frame* nil)
(defparameter *slot* nil)

(defun get-frame-and-slot (kb)
  (cond ((and (> (length (string *frame-name*)) 0)
	      (> (length (string  *slot-name*)) 0))
	 (multiple-value-bind (frames substring)
	   (get-frames-matching *frame-name* :kb kb :wildcards-allowed-p t)
	   ;; The first value in "frames" is a list of the matching frames.
	   (if (/= (length frames) 1)
	       ;; We expect this to have length 1.  0 would mean no matching
	       ;; frames, and >1 would mean we're not unique.
	       (progn (format t "~&~S does not uniquely identify a frame.  ~%~
		       Matches: ~S"
			*frame-name* frames)
		      ;; We're barfing out, so null out the frame, and reset the
		      ;; *frame-name* string to be the longest unique substring
		      ;; that matches frames.
		      (setq *frame* nil)
		      (setq *frame-name* substring))
	       (setq *frame* (first frames))))
	 ;; Do exactly the same for the slot name that we did for the frame name
	 (multiple-value-bind (slots substring)
	   (get-frames-matching *slot-name* :kb kb :wildcards-allowed-p t)
	   (if (/= (length slots) 1)
	       (progn (format t "~&~S does not uniquely identify a slot.  ~%~
			       Matches: ~S"
			*slot-name* slots)
		      (setq *slot* nil)
		      (setq *slot-name* substring))
	       (setq *slot* (first slots)))))
	(t (format t "You must supply both a frame and a slot!"))))


(defun demo2-get-slot-values (kb)
  ;; the instance variables frame and slot should now contain frame handles
  ;; for frames and slots on the server side.
  (if (and *frame* *slot*)
      ;; If we don't actually have a frame and a slot, then barf out
      ;; (else clause)
      (multiple-value-bind (values)
	;; Actually get the slot values for the slot in the frame.
	(get-slot-values *frame* *slot* :kb kb
			 :inference-level :all-inferable
			 :slot-type :own
			 :number-of-values :all
			 :value-selector :known-true)
	(format t "~&values = ~S~%" values)
	;; The values may well be non-trivial things like FrameHandles.
	;; For example, we might get back something like:
	;; ([FrameHandle ONTOLINGUA::FRAME-ONTOLOGY:82416488])
	;; These don't print out very nicely, so let's ask the OKBC server
	;; to turn the values into a string that we can print out.
	(let ((res-string (value-as-string
			   values :kb kb :purpose :user-interface
			   :pretty-p t)))
	  ;; res-string is now the printed representation of the values list.
	  ;; The particular string you get will depend on the actual slot
	  ;; values, but is the slot values list was the list with one frame
	  ;; handle like in the example above, the value of res-string would
	  ;; be something like "(Individual-Thing)",
	  ;; where Individual-Thing is the value of the superclass-of
	  ;; slot in the frame called thing.
	  (format t "~&res-string = \"~A\"" res-string)
	  (format t "~&(value-as-string res-string) = ~S~%" res-string)
	  res-string))
      (format t "You must supply both a frame and a slot!")))

(defun run-demo (kb-name kb-type connection)
  ;; This is the kb-type of a kb.
  (let ((proto (get-kb-type (intern kb-type "OK-BACK")
			    :connection connection)))
    ;; Now try to find the KB on the server.  It really should 
    ;; be there!
    (let ((kb (find-kb-of-type
	       kb-name :kb-type proto :connection connection)))
      ;; Oops, the KB wan't there.  Something terrible must 
      ;; have happened.
      (when (not kb) (error "Couldn't find KB ~S" kb-name))
      ;; Debug print.
      (format t "~&KB is ~S" kb)
      ;; Now prompt for the frame and slot names.
      (setq *frame-name* (prompt-and-read-frame-name "Frame" *frame-name*))
      (setq  *slot-name* (prompt-and-read-frame-name  "Slot"  *slot-name*))
      ;; Given the frame and slot names, try to find unambiguous frame objects
      ;; for these names.
      (get-frame-and-slot kb)
      ;; If we've got a frame and a slot, go and get the slot values and 
      ;; print them.
      (when (and *frame* *slot*)
	(demo2-get-slot-values kb)))))

(defun run-demo-against-ontolingua (connection)
  ;; This is the name of the Frame ontology.
  (let ((kb-name (ok-back:intern-quasi-symbol "FRAME-ONTOLOGY" "ONTOLINGUA"))
	(kb-type "ABSTRACT-ONTOLOGY-KB"))
    (when (not *frame-name*) (setq *frame-name* "THING"))
    (when (not  *slot-name*) (setq *slot-name*  "SUPERCLASS-OF"))
    (run-demo kb-name kb-type connection)))

(defun run-demo-against-taxa-kb (connection)
  ;; This is the name of the Frame ontology.
  (let ((kb-name (ok-back:intern-quasi-symbol "TAXA" "OKBC-TEST"))
	(kb-type "ABSTRACT-TUPLE-KB-KB"))
    (when (not *frame-name*) (setq *frame-name* "BILL"))
    (when (not  *slot-name*) (setq  *slot-name* "FOODS"))
    (run-demo kb-name kb-type connection)))

(defun demo2 (&key okbchost port help
		   #+ksl-okbc user-id
		   #+ksl-okbc password
		   #+ksl-okbc taxa
		   #+ksl-okbc ontolingua)
  (cond (help
	 (format t "~%(demo2 &rest option*)")
	 (format t "~%where options include:")
	 (format t "~%    :okbchost <hostname>: the host to connect to")
	 (format t "~%    :port <port number> : the port to connect to")
	 #+ksl-okbc
	 (format t "~%    :taxa t             : run against the TAXA test kb")
	 #+ksl-okbc
	 (format t "~%    :ontolingua  t      : run against the frame ontology")
	 (format t "~%                  If you pick Ontolingua:")
	 (format t "~%    :user-id <id>       : your KSL user id")
	 (format t "~%    :password <pwd>     : your KSL password"))
	(t (let ((ontolingua-p
		  #+ksl-okbc
		   (cond (ontolingua t)
			 (taxa nil)
			 (t (error "You must supply either :taxa or ~
                                   :ontolingua.  Try :help")))
		   #-ksl-okbc
		   nil)
		 
		 (user-id  #+ksl-okbc user-id  #-ksl-okbc nil)
		 (password #+ksl-okbc password #-ksl-okbc nil))
	     (let ((host (or okbchost "ontolingua.stanford.edu"))
		   (port (or port 5915)))
	       (let ((connection
		      (get-demo-connection
		       host port user-id password ontolingua-p)))
		 (unwind-protect
		      (loop do
			    (if ontolingua-p
				(run-demo-against-ontolingua connection)
				(run-demo-against-taxa-kb connection)))
		   (when connection
		     (close-connection connection :error-p nil
				       :force-p t)))))))))
