(in-package :demos)

;=============================================================================
;; Code to handle opening connections to an OKBV server, and finding
;; a KB on that server.

;; Start get-connection-for-kb-summary
(defun get-connection-for-kb-summary ()
  (let ((connection-type
	 (menu-choose "Pick a connection type:"
		      '((ok-back:local-connection "Local connection")
			(ok-back:simple-network-connection
			 "Simple network connection")
			(ksl-okbc:ksl-network-connection
			 "KSL network connection")))))
    (ecase connection-type
      (ok-back:local-connection (local-connection))
      (ok-back:simple-network-connection
       (let ((host (prompt-and-read-string "Host"))
	     (port (prompt-and-read-integer "Port")))
	 (establish-connection connection-type
			       :initargs (list :host host :port port))))
      (ksl-okbc:ksl-network-connection
       (get-ksl-connection connection-type)))))
;; End get-connection-for-kb-summary

;; Start get-ksl-connection
(defun get-ksl-connection (connection-type)
  (let ((host (prompt-and-read-string "Host"))
	(port (prompt-and-read-integer "Port"))
	(user-id (prompt-and-read-string "User ID" "Alien")))
    (let ((password (if (equal user-id "Alien")
			""
			(prompt-and-read-string "Password"))))
      (let ((sessions
	     (ksl-okbc:active-sessions host port user-id password)))
	(multiple-value-bind (key session-id)
	  (let ((session-id
		 (cond ((string-equal :alien user-id)
			(first (first sessions)))
		       (sessions
			(menu-choose
			 "Select session to open:"
			 (cons (list nil "Create a new session")
			       (loop for (session-id group description)
				     in sessions
				     collect
				     (list session-id
					   (format nil "~A owned by ~A"
					     description group))))))
		       (t nil))))
	    (if session-id
		(ksl-okbc:login-user-and-connect-to-session
		 host port user-id password session-id)
		(let ((groups (ksl-okbc:get-groups host port user-id
						   password)))
		  (let ((group (menu-choose
				"Select a group to own a new session."
				(loop for g in groups
				      collect
				      (list g (princ-to-string g)))))
			(description (prompt-and-read-string
				      "Session description"))
			(duration
			 (prompt-and-read-integer
			  "Session duration in hours")))
		    (ksl-okbc:login-user-and-create-session
		     host port user-id password group description
		     duration)))))
	  (let ((connection
		 (okbc:establish-connection
		  connection-type
		  :initargs (list :host host
				  :port port
				  :user-id user-id
				  :password password
				  :session-id session-id
				  :key key
				  :kb-library :a))))
	    (setf (ksl-okbc::connection-method connection)
		  :connect-using-http-initially)
	    connection))))))
;; End get-ksl-connection

;; Start get-kb-type-for-kb-summary
(defun get-kb-type-for-kb-summary (connection)
  (let ((kb-types (get-kb-types :connection connection)))
    (menu-choose "Pick a KB type"
		 (loop for type in kb-types
		       collect
		       (list type (frs-name :kb-type type
					    :connection connection))))))
;; End get-kb-type-for-kb-summary

;; Start get-kb-for-kb-summary
(defun get-kb-for-kb-summary (connection)
  (loop do
	(let ((kb-type (get-kb-type-for-kb-summary connection))
	      (meta-kb (meta-kb :connection connection)))
	  (let ((kbs (get-kbs-of-type :kb-type kb-type
				      :connection connection)))
	    (if kbs
		(return
		  (menu-choose
		   "Pick a KB"
		   (loop for kb in kbs
			 collect
			 (list kb (get-frame-pretty-name kb :kb meta-kb)))))
		(format *query-io*
		        "~&Sorry, there are no KBs for KB type ~A.  ~
                         Please try some other KB type."
		  (frs-name :kb-type kb-type :connection connection)))))))
;; End get-kb-for-kb-summary

;; Start find-and-summarize-kb
(defun find-and-summarize-kb ()
  (let ((connection nil))
    (unwind-protect
	 (progn (setq connection (get-connection-for-kb-summary))
		(let ((kb (get-kb-for-kb-summary connection))
		      (inference-level
		       (menu-choose "Inference level"
				    '((:direct "Direct")
				      (:taxonomic "Taxonomic")
				      (:all-inferable "All inferable"))))
		      (version-switch
		       (menu-choose
			"Pick a summary method"
			'((:simple "Simple")
			  (:details "Using get-frame-details")
			  (:filtered "Filtered")
			  (:filtered-on-server
			   "Filtered on the server"))))
		      (just-frames-in-this-kb-p
		       (y-or-n-p "Tabulate only frames in this KB? "))
		      (path (prompt-and-read-string "Output file")))
		  (with-open-file (stream path :direction :output)
		    (htmlify-kb-summary stream kb inference-level
					version-switch "L"
					just-frames-in-this-kb-p))))
      (when connection (close-connection connection)))))
;; End find-and-summarize-kb

;=============================================================================
;; HTML support stuff for the KB summarizer.

;; Start html-support
(defvar *html-replacements-table*
  (let ((table (make-array 256 :initial-element nil)))
    (loop for (char mapping)
	  in '((#\< "&lt;") (#\> "&gt;") (#\" "&quot;") (#\& "&amp;"))
	  do (setf (aref table (char-code char)) mapping))
    table))

(defun format-html-string
    (stream string &optional (from 0 supplied-p) (to (length string)))
  (if stream
      (loop for index from from below to
	    for x = (aref string index)
	    for entry = (aref *html-replacements-table* (char-code x))
	    do (if entry
		   (write-string entry stream)
		   (write-char x stream)))
      (with-output-to-string (str)
	(if supplied-p
	    (format-html-string str string from to)
	    (format-html-string str string)))))

(defun format-html (stream format-string &rest l)
  "Format HTML to the stream *html-standard-output*"
  (let ((string (apply #'format nil format-string l)))
    (format-html-string stream string)))

(defmacro with-italics ((stream) &body body)
  `(let ((stream ,stream))
    (unwind-protect (progn (format stream "~&<I>") ,@body)
      (format stream "~&</I>"))))

(defmacro with-table ((stream &rest args) &body body)
  `(let ((stream ,stream))
    (unwind-protect
	 (progn (format stream "~&<TABLE~{ ~A~}>" (list ,@args)) ,@body)
      (format stream "~&</TABLE>"))))

(defmacro with-table-row ((stream) &body body)
  `(let ((stream ,stream))
    (unwind-protect (progn (format stream "<TR>") ,@body)
      (format stream "</TR>"))))

(eval-when (compile load eval)
  (defun table-cell-internal (stream body tag)
    `(let ((stream ,stream))
      (unwind-protect (progn (format stream "<~A valign=top>" ,tag) ,@body)
	(format stream "</~A>" ,tag)))))

(defmacro with-table-header-cell ((stream) &body body)
  (table-cell-internal stream body :TH))

(defmacro with-table-cell ((stream) &body body)
  (table-cell-internal stream body :TD))
;; End html-support

;=============================================================================
;; The KB summarizer

;; Start htmlify-kb-summary
(defun htmlify-kb-summary
    (stream kb inference-level version-switch link-tag
	    &optional (just-frames-in-this-kb-p t))
  (assert (kb-p kb))
  (assert (member inference-level '(:direct :taxonomic :all-inferable)))
  (ecase version-switch
    (:simple (tabulate-kb-frames-simple stream kb inference-level
					just-frames-in-this-kb-p link-tag))
    (:details (tabulate-kb-frames-details stream kb inference-level
					  just-frames-in-this-kb-p link-tag))
    (:filtered (tabulate-kb-frames-filtered stream kb inference-level
					    just-frames-in-this-kb-p link-tag))
    (:filtered-on-server (tabulate-kb-frames-filtered-on-server
			  stream kb inference-level just-frames-in-this-kb-p
			  link-tag))))
;; End htmlify-kb-summary

;; Start tabulate-kb-frames-simple
(defun tabulate-kb-frames-simple
    (stream kb inference-level just-frames-in-this-kb-p link-tag)
  (with-table (stream :border=1)
    (print-table-column-headers stream)
    (let ((frames-e
	   (enumerate-kb-frames :kb kb :kb-local-only-p
				just-frames-in-this-kb-p))
	  (link-table (make-hash-table)))
      (prefetch frames-e)
      (while (has-more frames-e)
        (let ((frame (next frames-e)))
	  (tabulate-frame-simple
	   stream frame kb inference-level just-frames-in-this-kb-p
	   link-table link-tag nil)))
      (free frames-e))))
;; End tabulate-kb-frames-simple

;; Start print-table-column-headers
(defun print-table-column-headers (stream)
  (with-table-row (stream)
    (with-table-header-cell (stream) (format stream "Frame"))
    (with-table-header-cell (stream) (format stream "Type"))
    (with-table-header-cell (stream) (format stream "Own slots"))
    (with-table-header-cell (stream) (format stream "Template slots"))))
;; End print-table-column-headers

;; Start maybe-allocate-link-name
(defun maybe-allocate-link-name (frame kb just-frames-in-this-kb-p link-table
				       frame-must-be-there-to-link-p)
  (if (frame-in-kb-p frame :kb kb :kb-local-only-p just-frames-in-this-kb-p)
      (or (gethash frame link-table)
	  (and (not frame-must-be-there-to-link-p)
	       (let ((index (hash-table-count link-table)))
		 (setf (gethash frame link-table) index)
		 index)))
      nil))
;; End maybe-allocate-link-name

;; Start tabulate-frame-simple
(defun tabulate-frame-simple
    (stream frame kb inference-level just-frames-in-this-kb-p link-table
	    link-tag frame-must-be-there-to-link-p)
  (let ((link-name
	 (maybe-allocate-link-name
	  frame kb just-frames-in-this-kb-p link-table
	  frame-must-be-there-to-link-p))
	(frame-type (get-frame-type frame :kb kb))
	(own-slots-e
	 (enumerate-frame-slots frame :kb kb :slot-type :own
				:inference-level
				inference-level)))
    (let ((template-slots-e
	   (if (eq :class frame-type)
	       (enumerate-frame-slots
		frame :kb kb :slot-type :template
		:inference-level inference-level)
	       nil)))
      (with-table-row (stream)
	(with-table-cell (stream)
	  (format stream "<A name=\"~A~D\">" link-tag link-name)
	  (format-html stream "~A"
		       (value-as-string frame :kb kb))
	  (format stream "</A>"))
	(with-table-cell (stream)
	  (print-value-maybe-with-link
	   stream frame-type kb just-frames-in-this-kb-p
	   link-table link-tag frame-must-be-there-to-link-p))
	(with-table-cell (stream)
	  (prefetch own-slots-e)
	  (tabulate-slots-in-frame-simple
	   stream frame own-slots-e :own kb
	   inference-level just-frames-in-this-kb-p link-table link-tag
	   frame-must-be-there-to-link-p)
	  (free own-slots-e))
	(when template-slots-e
	  (with-table-cell (stream)
	    (prefetch template-slots-e)
	    (tabulate-slots-in-frame-simple
	     stream frame template-slots-e :template kb
	     inference-level just-frames-in-this-kb-p link-table link-tag
	     frame-must-be-there-to-link-p)
	    (free template-slots-e)))))))
;; End tabulate-frame-simple

;; Start print-value-maybe-with-link
(defun print-value-maybe-with-link
    (stream value kb just-frames-in-this-kb-p link-table link-tag
	    frame-must-be-there-to-link-p)
  (multiple-value-bind
      (string location-list) (value-as-string value :kb kb)
      (let ((index 0))
	(loop while location-list
	      for (start end frame) = (pop location-list)
	      do (let ((link (maybe-allocate-link-name
			      frame kb just-frames-in-this-kb-p link-table
			      frame-must-be-there-to-link-p)))
		   (format-html stream "~A" (subseq string index start))
		   (cond (link (format stream "<A href=\"#~A~D\">"
				 link-tag link)
			       (format-html stream "~A"
					    (subseq string start end))
			       (format stream "</A>"))
			 (t (format-html stream "~A"
					 (subseq string start end))))
		   (setq index end)))
	(format-html stream "~A" (subseq string index)))))
;; End print-value-maybe-with-link

;; Start slot-or-facet-table-header-row
(defun slot-or-facet-table-header-row (stream type-string)
  (with-table-row (stream)
    (with-table-header-cell (stream) (format stream type-string))
    (with-table-header-cell (stream) (format stream "Values"))
    (with-table-header-cell (stream) (format stream "DValues"))))
;; End slot-or-facet-table-header-row

;; Start tabulate-slots-in-frame-simple
(defun tabulate-slots-in-frame-simple
    (stream frame slots-e slot-type kb inference-level
	    just-frames-in-this-kb-p link-table link-tag
	    frame-must-be-there-to-link-p)
  (if (has-more slots-e)
      (with-table (stream :border=1)
	(slot-or-facet-table-header-row stream "Slot")
	(loop while (has-more slots-e)
	      for slot = (next slots-e)
	      for values-e = (enumerate-slot-values
			      frame slot :kb kb :slot-type slot-type
			      :inference-level inference-level
			      :value-selector :known-true)
	      for default-values-e = (enumerate-slot-values
				      frame slot :kb kb :slot-type slot-type
				      :inference-level inference-level
				      :value-selector :default-only)
	      do
	      (with-table-row (stream)
		(with-table-cell (stream)
		  (print-value-maybe-with-link
		   stream slot kb just-frames-in-this-kb-p link-table
		   link-tag frame-must-be-there-to-link-p))
		(with-table-cell (stream)
		  (prefetch values-e)
		  (loop while (has-more values-e)
			for value = (next values-e)
			for firstp = t then nil
			when (not firstp) do (format stream ", ")
			do (print-value-maybe-with-link
			    stream value kb just-frames-in-this-kb-p
			    link-table link-tag
			    frame-must-be-there-to-link-p))
		  (free values-e))
		(with-table-cell (stream)
		  (with-italics (stream)
		    (prefetch default-values-e)
		    (loop while (has-more default-values-e)
			  for value = (next default-values-e)
			  for firstp = t then nil
			  when (not firstp) do (format stream ", ")
			  do (print-value-maybe-with-link
			      stream value kb just-frames-in-this-kb-p
			      link-table link-tag
			      frame-must-be-there-to-link-p))
		    (free default-values-e))))
	      (tabulate-facets-in-slot-simple
	       stream frame slot slot-type kb inference-level
	       just-frames-in-this-kb-p link-table link-tag
	       frame-must-be-there-to-link-p)))
      (with-italics (stream) (format stream "None"))))
;; End tabulate-slots-in-frame-simple

;; Start tabulate-facets-in-slot-simple
(defun tabulate-facets-in-slot-simple
    (stream frame slot slot-type kb inference-level just-frames-in-this-kb-p
	    link-table link-tag frame-must-be-there-to-link-p)
  (let ((facets-e (enumerate-slot-facets frame slot :kb kb :slot-type slot-type
					 :inference-level inference-level)))
    (when (has-more facets-e)
      (with-table-row (stream)
	(with-table-cell (stream));; Empty cell to tab over
	(with-table-cell (stream)
	  (with-table (stream :border=1)
	    (slot-or-facet-table-header-row stream "Facet")
	    (prefetch facets-e)
	    (loop while (has-more facets-e)
		  for facet = (next facets-e)
		  for facet-values-e
		  = (enumerate-facet-values
		     frame slot facet :kb kb :slot-type slot-type
		     :inference-level inference-level
		     :value-selector :known-true)
		  for default-facet-values-e
		  = (enumerate-facet-values
		     frame slot facet :kb kb :slot-type slot-type
		     :inference-level inference-level
		     :value-selector :default-only)
		  do (with-table-row (stream)
		       (with-table-cell (stream)
			 (print-value-maybe-with-link
			  stream facet kb just-frames-in-this-kb-p
			  link-table link-tag frame-must-be-there-to-link-p))
		       (with-table-cell (stream)
			 (prefetch facet-values-e)
			 (loop while (has-more facet-values-e)
			       for value = (next facet-values-e)
			       for firstp = t then nil
			       when (not firstp) do (format stream ", ")
			       do (print-value-maybe-with-link
				   stream value kb
				   just-frames-in-this-kb-p link-table
				   link-tag frame-must-be-there-to-link-p)))
		       (with-table-cell (stream)
			 (with-italics (stream)
			   (prefetch default-facet-values-e)
			   (loop while (has-more default-facet-values-e)
				 for value = (next default-facet-values-e)
				 for firstp = t then nil
				 when (not firstp) do (format stream ", ")
				 do (print-value-maybe-with-link
				     stream value kb just-frames-in-this-kb-p
				     link-table link-tag
				     frame-must-be-there-to-link-p))
			   (free default-facet-values-e)))))))))
    (free facets-e)))
;; End tabulate-facets-in-slot-simple

;=============================================================================
;; Code to handle summarizing a KB by calling get_frame_details.

;; Start tabulate-kb-frames-details
(defun tabulate-kb-frames-details
    (stream kb inference-level just-frames-in-this-kb-p link-tag)
  (with-table (stream :border=1)
    (print-table-column-headers stream)
    (let ((frames-e
	   (enumerate-kb-frames :kb kb :kb-local-only-p
				just-frames-in-this-kb-p))
	  (link-table (make-hash-table)))
      (prefetch frames-e)
      (while (has-more frames-e)
	(let ((frame (next frames-e)))
	  (tabulate-frame-details
	   stream frame kb inference-level just-frames-in-this-kb-p
	   link-table link-tag nil)))
      (free frames-e))))
;; End tabulate-kb-frames-details

;; Start tabulate-frame-details
(defun tabulate-frame-details
    (stream frame kb inference-level just-frames-in-this-kb-p link-table
	    link-tag frame-must-be-there-to-link-p)
  (let ((details (get-frame-details
		  frame :kb kb :inference-level inference-level))
	(link-name
	 (maybe-allocate-link-name
	  frame kb just-frames-in-this-kb-p link-table
	  frame-must-be-there-to-link-p)))
    (let ((frame-type (getf details :frame-type))
	  (own-slots-e
	   (enumerate-list (getf details :own-slots))))
      (let ((template-slots-e
	     (if (eq :class frame-type)
		 (enumerate-list (getf details :template-slots))
		 nil)))
	(with-table-row (stream)
	  (with-table-cell (stream)
	    (format stream "<A name=\"~A~D\">" link-tag link-name)
	    (format-html stream "~A"
			 (value-as-string frame :kb kb))
	    (format stream "</A>"))
	  (with-table-cell (stream)
	    (print-value-maybe-with-link
	     stream frame-type kb just-frames-in-this-kb-p
	     link-table link-tag frame-must-be-there-to-link-p))
	  (with-table-cell (stream)
	    (prefetch own-slots-e)
	    (tabulate-slots-in-frame-details
	     stream own-slots-e :own details kb
	     just-frames-in-this-kb-p link-table link-tag
	     frame-must-be-there-to-link-p)
	    (free own-slots-e))
	  (when template-slots-e
	    (with-table-cell (stream)
	      (prefetch template-slots-e)
	      (tabulate-slots-in-frame-details
	       stream template-slots-e :template details kb
	       just-frames-in-this-kb-p link-table link-tag
	       frame-must-be-there-to-link-p)
	      (free template-slots-e))))))))
;; End tabulate-frame-details

;; Start tabulate-slots-in-frame-details
(defun tabulate-slots-in-frame-details
    (stream slots-e slot-type details kb just-frames-in-this-kb-p link-table
	    link-tag frame-must-be-there-to-link-p)
  (if (has-more slots-e)
      (with-table (stream :border=1)
	(slot-or-facet-table-header-row stream "Slot")
	(loop while (has-more slots-e)
	      for (slot . values) = (next slots-e)
	      for values-e = (enumerate-list values)
	      for default-values = nil
	      do
	      (with-table-row (stream)
		(with-table-cell (stream)
		  (print-value-maybe-with-link
		   stream slot kb just-frames-in-this-kb-p link-table
		   link-tag frame-must-be-there-to-link-p))
		(with-table-cell (stream)
		  (prefetch values-e)
		  (loop with firstp = t
			while (has-more values-e)
			for value = (next values-e)
			when (not firstp) do (format stream ", ")
			do (cond ((and (consp value)
				       (eq :default (first value)))
				  (push (second value) default-values))
				 (t (print-value-maybe-with-link
				     stream value kb just-frames-in-this-kb-p
				     link-table link-tag
				     frame-must-be-there-to-link-p)
				    (setq firstp nil))))
		  (free values-e))
		(print-out-default-values
		 stream default-values kb just-frames-in-this-kb-p
		 link-table link-tag frame-must-be-there-to-link-p))
	      (tabulate-facets-in-slot-details
	       stream slot slot-type details kb just-frames-in-this-kb-p
	       link-table link-tag frame-must-be-there-to-link-p)))
      (with-italics (stream) (format stream "None"))))
;; End tabulate-slots-in-frame-details

;; Start print-out-default-values
(defun print-out-default-values
    (stream default-values kb just-frames-in-this-kb-p link-table link-tag
	    frame-must-be-there-to-link-p)
  (with-table-cell (stream)
    (let ((default-values-e (enumerate-list default-values)))
      (with-italics (stream)
	(prefetch default-values-e)
	(loop while (has-more default-values-e)
	      for value = (next default-values-e)
	      for firstp = t then nil
	      when (not firstp) do (format stream ", ")
	      do (print-value-maybe-with-link
		  stream value kb just-frames-in-this-kb-p
		  link-table link-tag frame-must-be-there-to-link-p))
	(free default-values-e)))))
;; End print-out-default-values

;; Start tabulate-facets-in-slot-details
(defun tabulate-facets-in-slot-details
    (stream slot slot-type details kb just-frames-in-this-kb-p link-table
	    link-tag frame-must-be-there-to-link-p)
  (let ((facets-e (enumerate-list
		   (rest (assoc slot (getf details
					   (if (eq slot-type :own)
					       :own-facets
					       :template-facets)))))))
    (when (has-more facets-e)
      (with-table-row (stream)
	(with-table-cell (stream));; Empty cell to tab over
	(with-table-cell (stream)
	  (with-table (stream :border=1)
	    (slot-or-facet-table-header-row stream "Facet")
	    (prefetch facets-e)
	    (loop while (has-more facets-e)
		  for (facet . facet-values) = (next facets-e)
		  for facet-values-e
		  = (enumerate-list facet-values)
		  for default-values = nil
		  do (with-table-row (stream)
		       (with-table-cell (stream)
			 (print-value-maybe-with-link
			  stream facet kb just-frames-in-this-kb-p
			  link-table link-tag frame-must-be-there-to-link-p))
		       (with-table-cell (stream)
			 (prefetch facet-values-e)
			 (loop with firstp = t
			       while (has-more facet-values-e)
			       for value = (next facet-values-e)
			       when (not firstp) do (format stream ", ")
			       do (cond ((and (consp value)
					      (eq :default (first value)))
					 (push (second value) default-values))
					(t (print-value-maybe-with-link
					    stream value kb
					    just-frames-in-this-kb-p
					    link-table link-tag
					    frame-must-be-there-to-link-p)
					   (setq firstp nil))))
			 (free facet-values-e))
		       (print-out-default-values
			stream default-values kb just-frames-in-this-kb-p
			link-table link-tag frame-must-be-there-to-link-p)))
	    (free facets-e)))))))
;; End tabulate-facets-in-slot-details

;=============================================================================
;; Code to summarize a filtered subset of the frames in a KB by running
;; the filter on the client side.

;; Start tabulate-kb-frames-filtered
(defun tabulate-kb-frames-filtered
    (stream kb inference-level just-frames-in-this-kb-p link-tag)
  (with-table (stream :border=1)
    (print-table-column-headers stream)
    (let ((frames (get-filtered-frames kb inference-level
				       just-frames-in-this-kb-p))
	  (link-table (make-hash-table)))
      (preallocate-links-for-frames
       frames kb just-frames-in-this-kb-p link-table)
      (let ((frames-e (enumerate-list frames)))
	(prefetch frames-e)
	(while (has-more frames-e)
	  (let ((frame (next frames-e)))
	    (tabulate-frame-details
	     stream frame kb inference-level just-frames-in-this-kb-p
	     link-table link-tag t)))
	(free frames-e)))))
;; End tabulate-kb-frames-filtered

;; Start preallocate-links-for-frames
(defun preallocate-links-for-frames
    (frames kb just-frames-in-this-kb-p link-table)
  (let ((frames-e (enumerate-list frames)))
    (prefetch frames-e)
    (while (has-more frames-e)
      (let ((frame (next frames-e)))
	(maybe-allocate-link-name
	 frame kb just-frames-in-this-kb-p link-table nil)))
    (free frames-e)))
;; End preallocate-links-for-frames

;; Start get-filtered-frames
(defun get-filtered-frames (kb inference-level just-frames-in-this-kb-p)
  (let ((frames-e (enumerate-kb-frames :kb kb :kb-local-only-p
				       just-frames-in-this-kb-p))
	(result nil))
    (prefetch frames-e)
    (while (has-more frames-e)
       (let ((frame (next frames-e)))
	 (let ((slots-e (enumerate-frame-slots
			 frame :kb kb :inference-level inference-level
			 :slot-type :own))
	       (facet-found-p nil))
	   (prefetch slots-e)
	   (while (and (has-more slots-e) (not facet-found-p))
	     (if (get-slot-facets frame (next slots-e) :kb kb
				  :inference-level inference-level
				  :slot-type :own)
		 (setq facet-found-p t)
		 nil))
	   (free slots-e)
	   (if facet-found-p
	       (push frame result)
	       (let ((slots-e (enumerate-frame-slots frame :kb kb
			         :inference-level inference-level
			         :slot-type :template))
		     (facet-found-p nil))
		 (prefetch slots-e)
		 (while (and (has-more slots-e) (not facet-found-p))
		   (if (get-slot-facets frame (next slots-e) :kb kb
					:inference-level inference-level
					:slot-type :template)
		       (setq facet-found-p t)
		       nil))
		 (free slots-e)
		 (if facet-found-p (push frame result) nil))))))
    (free frames-e)
    result))
;; End get-filtered-frames

;=============================================================================
;; Code to summarize a filtered subset of the frames in a KB by running
;; the filter on the server side.

;; Start tabulate-kb-frames-filtered-on-server
(defun tabulate-kb-frames-filtered-on-server
    (stream kb inference-level just-frames-in-this-kb-p link-tag)
  (with-table (stream :border=1)
    (print-table-column-headers stream)
    (let ((frames (get-filtered-frames-on-server
		   kb inference-level just-frames-in-this-kb-p))
	  (link-table (make-hash-table)))
      (preallocate-links-for-frames
       frames kb just-frames-in-this-kb-p link-table)
      (let ((frames-e (enumerate-list frames)))
	(prefetch frames-e)
	(while (has-more frames-e)
	  (let ((frame (next frames-e)))
	    (tabulate-frame-details
	     stream frame kb inference-level just-frames-in-this-kb-p
	     link-table link-tag t)))
	(free frames-e)))))
;; End tabulate-kb-frames-filtered-on-server

;; Start get-filtered-frames-on-server
(defun get-filtered-frames-on-server
    (kb inference-level just-frames-in-this-kb-p)
  (let ((procedure
	 (create-procedure
	  :kb kb
	  :arguments "(kb inference-level just-frames-in-this-kb-p)"
	  :body
	  "(let ((frames-e (enumerate-kb-frames :kb kb :kb-local-only-p
						just-frames-in-this-kb-p))
		 (result nil))
	     (prefetch frames-e)
	     (while (has-more frames-e)
	       (let ((frame (next frames-e)))
		 (let ((slots-e (enumerate-frame-slots
				 frame :kb kb
                                 :inference-level inference-level
                                 :slot-type :own))
		       (facet-found-p nil))
		   (prefetch slots-e)
		   (while (and (has-more slots-e) (not facet-found-p))
		     (if (get-slot-facets
			  frame (next slots-e) :kb kb
			  :inference-level inference-level
			  :slot-type :own)
			 (setq facet-found-p t)
			 nil))
		   (free slots-e)
		   (if facet-found-p
		       (push frame result)
		       (let ((slots-e (enumerate-frame-slots
				       frame :kb kb
                                       :inference-level inference-level
                                       :slot-type :template))
			     (facet-found-p nil))
			 (prefetch slots-e)
			 (while (and (has-more slots-e)
                                     (not facet-found-p))
			   (if (get-slot-facets
				frame (next slots-e) :kb kb
				:inference-level inference-level
				:slot-type :template)
			       (setq facet-found-p t)
			       nil))
			 (free slots-e)
			 (if facet-found-p
			     (push frame result)
			     nil))))))
	     (free frames-e)
	     result)")))
    (register-procedure 'get-filtered-frames procedure :kb kb)
    (call-procedure 'get-filtered-frames :kb kb
		    :arguments (list kb inference-level
				     just-frames-in-this-kb-p))))
;; End get-filtered-frames-on-server

;=============================================================================
;; Simple support for TTY-based menus and prompting from the user.

;; Start menu-choose
(defun menu-choose (title alist &optional (default (first (first alist))))
  (loop do
	(format *query-io* "~&~A" title)
	(loop for i from 0
	      for spec in alist
	      for printed-representation = (second spec)
	      do (format *query-io* "~&  ~3D ~A" i printed-representation))
	(format *query-io* "~&Choose [default ~A]: "
	  (second (assoc default alist)))
	(let ((line (read-line *query-io*)))
	  (if (equal line "")
	      (return default)
	      (let ((choice (ignore-errors (parse-integer line))))
		(if (and (integerp choice) (>= choice 0)
			 (< choice (length alist)))
		    (return (first (nth choice alist)))
		    (format *query-io*
		     "~&!! Selection should be in the range [0...~D]"
		      (- (length alist) 1))))))))
;; End menu-choose

;; Start prompt-and-read-string
(defun prompt-and-read-string (label &optional (default nil))
  (loop do
	(if default
	    (format *query-io* "~&~A [default ~A]: " label default)
	    (format *query-io* "~&~A: " label))
	(let ((result (read-line *query-io*)))
	  (if (equal result "")
	      (if default
		  (return default)
		  (format *query-io* "~&!! Please enter a string."))
	      (return result)))))
;; End prompt-and-read-string

;; Start prompt-and-read-integer
(defun prompt-and-read-integer (label)
  (loop do
	(format *query-io* "~&~A: " label)
	(let ((result (read *query-io*)))
	  (cond ((integerp result) (return result))
		(t (format *query-io* "~&!! Please enter an integer."))))))
;; End prompt-and-read-integer

;=============================================================================

#| Text to insert in the paper in the right place.

;; Start enumerator-example
(let ((e (enumerate-slot-values frame slot :kb kb)))
  (prefetch e)
  (while (has-more(e))
    (let ((value (next e)))
      .....)) ;; do something with the slot value.
  (free e))
;; End enumerator-example

;; Start default-selection
(cond ((and (consp value) (eq :default (first value)))
       (push (second value) default-values))
      (t (print-value-maybe-with-link stream value kb just-frames-in-this-kb-p
				      link-table link-tag
				      frame-must-be-there-to-link-p)
	 (setq first-p nil)))
;; End default-selection

|#

