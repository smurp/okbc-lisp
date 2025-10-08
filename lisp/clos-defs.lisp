(in-package :ok-kernel)

(defpackage frame-names (:use))

(defvar *frame-names-package* (find-package :frame-names))

;==============================================================================

(defokbcclass ok-back:frame-name-interning-mixin (ok-back:okbc-kb-mixin)
  ((frame-name-mapping-table :accessor frame-name-mapping-table
			     :initform (make-hash-table :test #'eq))
   (name-to-frame-mapping-table :accessor name-to-frame-mapping-table
				:initform (make-hash-table :test #'eq)))
  (:documentation "A mixin class of OKBC kb knows how to allocate frame names
   lazily for any objects of which we ask the name.  If the object's name is
   ever asked for, the object gets interned under a gensym name in the KB."))

(defokbcgeneric mark-to-require-rehash (thing)
  (:documentation "Some Lisp implementations have constraints about the use of
   statically consed objects when they are used as keys in hash tables.
   When such hash tables are disk saved out, they may have to be rehashed
   at system startup time.  This generic function will traverse data
   structures so as to make sure that the right hash tables get rehashed."))

(defokbcgeneric mark-trie-require-rehash (trie)
  (:documentation "Some Lisp implementations have constraints about the use of
   statically consed objects when they are used as keys in hash tables.
   When such hash tables are disk saved out, they may have to be rehashed
   at system startup time.  This generic function will traverse tries
   so as to make sure that the right hash tables get rehashed."))

(defmethod mark-to-require-rehash :after
     ((kb ok-back:frame-name-interning-mixin))
  (when (and (slot-boundp kb 'frame-name-mapping-table)
	     (hash-table-p (frame-name-mapping-table kb)))
    (mark-to-require-rehash (frame-name-mapping-table kb))))

(defokbcclass ok-back:clos-only-okbc-mixin
    (ok-back:frames-have-clos-slots-as-okbc-slots-mixin)
  ()
  (:documentation "A mixin class of OKBC kb that views all CLOS standard-object
   instances and all defstruct structure-object instances as frames.  This
   is a subclass of <code>frame-name-interning-mixin</code>, from which it
   gets the ability to look inside CLOS and defstruct objects, but if you
   mix this class in, the only sorts of slots that will be found will be the
   CLOS/defstruct ones.  This mixin cannot sensibly be mixed into a KB class
   that wants to find frames, slots or facets elsewhere."))

;==============================================================================

(defokbcclass ok-back:abstract-clos-kb-kb () ())

(defokbcclass ok-back:clos-kb (ok-back:abstract-clos-kb-kb
			       ok-back:handle-number-of-values-mixin
			       ok-back:clos-only-okbc-mixin
			       ok-back:standard-defaults-kb)
  ()
  (:documentation "A class of OKBC kb that views all CLOS standard-object
   instances and all defstruct structure-object instances as frames.  The
   respective CLOS or defstruct slots appear as OKBC slots.  Note that this
   KB class is useful for looking inside random CLOS objects with OKBC tools,
   but it is not in itself a compliant OKBC KB.  You can't expect everything
   to work."))

(defokbcclass ok-back:abstract-instance-recording-clos-kb-kb () ())

(defokbcclass ok-back:instance-recording-clos-kb
    (ok-back:abstract-instance-recording-clos-kb-kb
     ok-back:clos-only-okbc-mixin)
  ((recorded-instances :accessor recorded-instances :initform nil :initarg
		       :recorded-instances))
  (:documentation "A subclass of <code>clos-kb</code> that keeps a pointer to
   instances."))

;==============================================================================

(defnetwork-okbc-kb ok-back:clos-kb (caching-mixin))

