(in-package :OK-kernel)

;;; Define the KB class.  This gets used by expansions to
;;; OKBC iterator macros, so we need to define this up-front.

;; SMP: I added this variable, and rebind it any time a KB argument is given.
;; This is so that we know what KB we are referencing when we fault from the
;; database.
(defvar **kb** nil)

(defvar *unique-kb-ids* 0)
(defvar *name-to-procedure-table*
  (make-hash-table :test #'equal))

(defun allocate-unique-kb-id ()
  (without-scheduling
   (incf *unique-kb-ids*)
   *unique-kb-ids*))

(defokbcclass ok-back:okbc-kb-mixin
    ()
  ()
  (:documentation "An abstract superclass of OKBC implementation-supplied
   mixin classes.  This class (or really subclasses of it) are used in
   determining OKBC compliance."))

(defokbcclass ok-back:kb ()
  ((ok-back:name :accessor ok-back:name :initarg :name)
   (ok-back:connection :accessor ok-back:connection :initarg :connection
		       :initform (okbc:local-connection))
   (ok-back:unique-id :accessor ok-back:unique-id
		      :initform (allocate-unique-kb-id))
   (ok-back:kb-has-been-modified-p
    :accessor ok-back:kb-has-been-modified-p
    :initform nil)
   (name-to-procedure-table
    :accessor name-to-procedure-table
    :initform *name-to-procedure-table*)
   (plist :accessor plist :initform nil :initarg :plist))
  (:documentation "The abstract superclass of all standard-object OKBC Kbs.<P>

   The Lisp OKBC implementation provides two parallel graphs of KB
   implementation for back end implementors who want to implement their KBs
   either as CLOS classes or defstructs.  If you choose the CLOS implementation
   (and the abstract superclass <code>kb</code>), then you can use all of the
   mixins provided by the OKBC Lisp implementation.  If you choose to use
   defstruct as your implementation substrate, you must use
   <code>structure-kb</code> (transitively) to implement your KB.  Because of
   the lack of multiple inheritance in defstruct only a subset of the options
   available in the CLOS case are available.<P>

   The KB classes <code>kb</code> and <code>structure-kb</code> provide
   default implementations for operations that are general across all KBs
   (including <code>standard-defaults-kb</code> and
   <code>tell&ask-defaults-kb</code>."))

(defdoc ok-back:plist (function)
  "An accessor for a property list on KBs.")

(defdoc ok-back:kb-has-been-modified-p (function)
  "An accessor that determines whether a KB has been modified or not.  This
   is set by side-effecting OKBC operations and read by
   <code>okbc:kb-modified-p</code>.")

(defdoc ok-back:unique-id (function)
  "Returns the unique ID for a KB.  KBs have a numerical unique ID used by the
   network transport layer and to match up KBs when loading them from files.")

(defnetwork-okbc-kb ok-back:kb ())

(defokbcclass ok-back:standard-defaults-kb (ok-back:kb)
  ()
  (:documentation "A class of KB that provides default implementations for a
   number of operations.  Broadly speaking, the default implementations
   expect the KB to be largely object-oriented in feel, and the operations that
   are considered primitive are such operations as
   <code>get-class-instances</code>, <code>get-frame-slots</code> and
   <code>get-slot-values-in-detail</code>.  This defaulting scheme is in
   contrast to the defaults provided by <code>tell&ask-defaults-kb</code>."))

(defnetwork-okbc-kb ok-back:standard-defaults-kb ())

(defokbcclass ok-back:tell&ask-defaults-kb (ok-back:kb)
  ((ok-back:inference-level-for-tell&ask-defaults
    :accessor inference-level-for-tell&ask-defaults
    :initform :taxonomic
    :initarg :inference-level-for-tell&ask-defaults)
   (ok-back:timeout-for-tell&ask-defaults
    :accessor timeout-for-tell&ask-defaults
    :initform nil
    :initarg :timeout-for-tell&ask-defaults))
  (:documentation "A class of KB that provides default implementations for a
   number of operations.  Broadly speaking, the default implementations
   expect the KB to be largely sentential in feel, and the operations that
   are considered primitive are such operations as
   <code>tell</code>, <code>ask</code> and
   <code>get-frame-sentences</code>.  This defaulting scheme is in
   contrast to the defaults provided by <code>standard-defaults-kb</code>."))

(defdoc ok-back:inference-level-for-tell&ask-defaults (function)
  "A method on tell&ask KBs that delivers the inference level to use when the
   tell&ask middle end executes a default that doesn't take an
   <code>inference-level</code> argument.  For example, the operation
   <code>class-p</code> has the following tell&ask default:<PRE>
   (first (ask-internal `(:class ,thing) kb t
		        (inference-level-for-tell&ask-defaults kb) 1
		        t nil (timeout-for-tell&ask-defaults kb)
                        :known-true kb-local-only-p))</PRE>")

(defdoc ok-back:timeout-for-tell&ask-defaults (function)
  "A method on tell&ask KBs that delivers the timeout to use when the
   tell&ask middle end executes a default that doesn't take an
   <code>inference-level</code> argument.  For example, the operation
   <code>class-p</code> has the following tell&ask default:<PRE>
   (first (ask-internal `(:class ,thing) kb t
		        (inference-level-for-tell&ask-defaults kb) 1
		        t nil (timeout-for-tell&ask-defaults kb)
                        :known-true kb-local-only-p))</PRE>")

(defnetwork-okbc-kb ok-back:tell&ask-defaults-kb ())

(pushnew 'ok-back:kb-network-kb *abstract-kb-class-names*)

(defdoc ok-back:kb-network-kb (type)
  "The abstract KB class for all network KBs.")

(defmethod ok-back:concrete-kb-class-from-abstract-kb-class-name
    ((name (eql 'ok-back:abstract-kb-kb)))
  (find-class 'ok-back:kb))

(defokbcclass ok-back::sri-kb-slots-mixin ()
  ((ok-back::id :accessor ok-back::kb-id :initarg :id);; Perk
   ;; Can be :LIVE or :OPEN
   (ok-back::state :accessor ok-back::kb-state :initarg :state :initform :LIVE)
   (ok-back::filename :accessor ok-back::kb-filename :initarg :filename
		      :initform nil)
   ;; If strings naming frames, slots, etc for this KB are interned,
   ;; the package slot tells us what package to intern them in.
   (ok-back::package :accessor ok-back::kb-package :initarg :package
		     :initform *package*)))

(defokbcclass ok-back:connection ()
  ((ok-back:notification-callback-function
    :accessor ok-back:notification-callback-function
    :initarg :notification-callback-function
    :initform 'ok-back:default-notification-callback-function)
   (open-p :accessor open-p :initform nil :initarg :open-p)))

(defdoc ok-back:notification-callback-function (function)
  "The <code>notification-callback-function</code> of a <code>connection</code>
   is a function of <code>(arg &optional (stream *trace-output*))</code>
   that is called by the OKBC implementation (particularly the network
   transport layer) in order to pass warnings and notifications back to the
   client.  Applications can register their own ways of handling notifications,
   perhaps by dribbling into a special window, by overriding generic function
   or slot on the connection.")

;; Do it this way because of franz bug.
(defdoc ok-back:connection (function)
  "Returns the <code>connection</code> associated with the
   <code>kb</code>.")

(defdoc ok-back:connection (type)
  "The abstract superclass of all connections known to OKBC.
   Interesting subclasses are <code>local-connection</code> and
   <code>network-connection</code>.  Back end implementors who need to
   impose their own multithreading or authentication model will need to
   define their own <code>connection</code> classes.<P>

   The <code>notification-callback-function</code> is a function of
   <code>(arg &optional (stream *trace-output*))</code> that is called
   by the OKBC implementation (particularly the network transport layer)
   in order to pass warnings and notifications back to the client.
   Applications can register their own ways of handling notifications,
   perhaps by dribbling into a special window, by overriding this
   function.")

(defdoc ok-back:open-p (function)
  "A predicate on connections that is true if the connection is open.")

(defmethod okbc-connection-p ((instance ok-back:connection)) t)
(defmethod okbc-connection-p ((thing t)) nil)

(defokbcclass ok-back:local-connection (ok-back:connection)
  ()
  (:documentation "The CLOS class used to implement the local
   <code>connection</code> for OKBC.  Calls to
   <code>okbc:local-connection</code> will always return an instance of this
   class."))

(defokbcgeneric ok-back:local-connection-p (thing)
  (:documentation "A predicate that is true only of
   <code>local-connection</code>s."))

(defmethod ok-back:local-connection-p ((thing t)) nil)
(defmethod ok-back:local-connection-p ((thing ok-back:local-connection)) t)
(defmethod open-p ((thing ok-back:local-connection)) t)

(defokbcclass ok-back:okbc-forwarding-mixin (ok-back:okbc-kb-mixin)
  ((ok-back:target-kb :accessor ok-back:target-kb :initarg :target-kb))
  (:documentation "Mixing this class into a class of OKBC kbs will make all
                   not explicitly defined OKBCops forward to the KB which is
                   the value of the <code>target-kb</code> slot."))

(defdoc ok-back:target-kb (function)
  "The slot on KBs of type <code>ok-back:okbc-forwarding-mixin</code> used to
   point to the real KB that has been wrapped by the forwarding KB.")

(defokbcclass ok-back:okbc-side-effects-cause-error-mixin
    (ok-back:okbc-kb-mixin)
  ()
  (:documentation "Mix this into a class of OKBC KBs to make it signal an error
                   if you ever attempt to perform a side-effect on the KB that
                   you have not explicitly supported by specializing the
                   side-effecting OKBCop."))

(defokbcclass ok-back:handle-number-of-values-mixin (ok-back:okbc-kb-mixin)
  ()
  (:documentation "A mixin that provides <code>:around</code> wrapper methods
   for all OKBC operations that take a <code>number-of-values</code> argument.
   These wrappers are specialized on <code>integer</code> for the
   <code>number-of-values</code> argument, so only get invoked if the
   application is trying to restrict the number of values.  The set of
   values returned is trimmed according to the constraint and the
   <code>more-status</code> shows the right thing.  This mixin is useful for
   back end implementations that do not have a way of limiting the number of
   values returned by the operations.  No performance improvement can
   be derived from the use of this class, since all values are computed,
   but compliance with respect to the <code>number-of-values</code> argument
   is ensured."))

(defokbcclass ok-back:default-inheritance-mixin (ok-back:okbc-kb-mixin)
  ()
  (:documentation "A mixin class for OKBC KBs that provides default
   implementations of the OKBC knowledge model's inheritance axioms.  Mixing
   in this class will give a complete implementation of methods for the
   inference levels <code>:taxonomic</code>, and <code>:all-inferable</code>
   for all of the operations requiring inheritance.  The back end implementor
   need only define methods for these oprtations <code>:eql</code> specialized
   on the inference-level <code>:direct</code> to achieve compliance.  See
   also <code>define-default-inheritance-methods</code>."))

(defokbcclass ok-back:caching-mixin (ok-back:okbc-kb-mixin)
  ((ok-cache:cache :accessor ok-cache:cache
	  :initform
	  (tries:new-root-hybrid-trie :okbc-cache nil)
	  :initarg :cache)
   (ok-cache:timestamp :accessor ok-cache:timestamp :initform nil)
   (ok-cache:allow-caching-p :accessor ok-cache:allow-caching-p :initform t
		    :initarg :allow-caching-p)
   (ok-cache:caching-policy :accessor ok-cache:caching-policy
			    :initform :defensive
			    :initarg :caching-policy))
  (:documentation "A mixin KB class that provides a cache wrapper for OKBC
   operations.  This class is useful when the underlying KB implementation is
   slow, inefficient, or for which <code>default-inheritance-mixin</code> is
   being used.<P>

   Calls to all side-effect free back-end operations are cached against the
   arguments to those calls in a <code>trie</code> held in the
   <code>cache</code> slot.  Caching can be enabled or disabled for the KB
   using the <code>allow-caching-p</code> slot, and caching can be globally
   disabled using <code>*allow-okbc-caching-p*</code>.<P>

   What causes a cache flush is controlled by the <code>caching-policy</code>
   slot.  If the value of this slot is <code>:defensive</code> (the default)
   then the cache will be flushed before any side-effecting operation, and
   will be disabled during the dynamic extent of the side-effect.
   If <code>caching-policy</code> has the value <code>:agressive</code>, then
   caching is permitted at all times, and the cache is only flushed either by
   explicit calls to <code>ok-cache:flush-cache</code>, or by calls to
   <code>ok-cache:register-side-effect</code>."))

(defdoc ok-cache:timestamp (function)
  "An accessor to the timestamp of the last cache flush of a KB, which is
   probably an instance of <code>caching-mixin</code> or
   <code>caching-structure-kb</code>.")

(defdoc ok-cache:caching-policy (function)
  "An accessor to the caching policy of a KB, which is probably an instance of
   <code>caching-mixin</code> or <code>caching-structure-kb</code>.  See
   <code>caching-mixin</code> for an explanation of legal values of the
   caching policy.")

(defdoc ok-cache:allow-caching-p (function)
  "An accessor to a flag on caching KBs (see <code>caching-mixin</code> and
   <code>caching-structure-kb</code> that determine whether caching of OKBC
   calls is to be allowed.")

(defdoc ok-cache:cache (function)
  "An accessor on caching KBs that returns the cache structure used
   in caching.  See <code>caching-mixin</code> and
   <code>caching-structure-kb</code>.")

(defokbcgeneric ok-cache:flush-cache (kb)
  (:documentation "Flushes the cache on <code>kb</code> if applicable."))

(defmethod ok-cache:flush-cache ((kb t))
  ;; Stub method.  Do nothing for non caching KBs.
  nil)

(defmethod ok-cache:flush-cache ((kb ok-back:caching-mixin))
  (when (boundp 'ok-cache:*ephemeral-cache*)
    (setq ok-cache:*ephemeral-cache*
	  (tries:new-root-hybrid-trie :okbc-cache nil)))
  (setf (ok-cache:cache kb) (tries:new-root-hybrid-trie :okbc-cache nil))
  (setf (ok-cache:timestamp kb) (get-universal-time)))

(defokbcclass ok-back:network-kb (ok-back:kb)
  ()
  (:documentation "The abstract superclass of all network KBs.  These are the
   KBs that are instantiated on the client side as a result of a KB being
   shipped from a server."))

(defokbcclass ok-back:network-coercion-mixin (ok-back:okbc-kb-mixin)
  ()
  (:documentation "This mixin provides all of the necessary automatic coercions
   that would have been provided by source code level coercions only in the
   back end.  It class must be mixed into any KB that is defined that expects
   the <code>:OKBC-Frame-Coercion</code> to be used.  The reason for this is
   that the network layer communicated by means of the back end API.  Because
   a server cannot make any assumptions about which coercions will have been
   performed at the client, a more defensive policy of coercions is necessary
   than can be assumed when dealing with a tightly coupled KB.."))

(defstruct ok-back:abstract-kb-locator
  (name nil)
  (kb-type nil))

(defdoc ok-back:abstract-kb-locator (structure)
  "The abstract superclass structure class for KB locators.  it is not required
   that KB locator classes be subclasses of this class, but making it so will
   allow the reuse of more OKBC-provided code.  An
   <code>abstract-kb-locator</code> contains a name for the KB denoted and a
   KB-type name.  This allows multiple locators of the same name for KBs of
   different types.")

(defmethod print-object ((instance ok-back:abstract-kb-locator) (stream t))
  (print-unreadable-object
   (instance stream :type t :identity t)
   (ignore-errors (prin1 (abstract-kb-locator-name instance) stream))))

(defokbcgeneric ok-back:name (thing)
  (:documentation "An accessor that returns the name of its argument whenever
    possible, or NIL otherwise."))

(defmethod name ((kb ok-back:abstract-kb-locator))
  (abstract-kb-locator-name kb))

(defmethod (setf name) (new-value (kb ok-back:abstract-kb-locator))
  (setf (abstract-kb-locator-name kb) new-value))

(defokbcgeneric kb-type (kb-locator)
  (:documentation "An accessor for KB locators that returns the kb-type of the
   KB denoted by the locator."))

(defmethod kb-type ((kb-locator ok-back:abstract-kb-locator))
  (abstract-kb-locator-kb-type kb-locator))

(defmethod (setf kb-type) (new-value (kb-locator ok-back:abstract-kb-locator))
  (setf (abstract-kb-locator-kb-type kb-locator) new-value))

;; Locator for KBs that stores kbs in a file, and need only
;; the filename information in the locator (in addition to the
;; kb name and kb type)

(defstruct (ok-back:file-kb-locator (:include abstract-kb-locator))
           (pathname nil))

(defdoc ok-back:file-kb-locator (structure)
  "A simple class of KB locator used by OKBC back ends that store KBs
   in files.  The slot <code>file-kb-locator</code> stores the actual
   pathname of the file.  This KB locator class can be fruitfully used in
   conjunction with <code>file-mixin</code>")

(defdoc ok-back:make-file-kb-locator (function)
  "The constructor for <code>file-kb-locator</code>.")  

(defdoc ok-back:file-kb-locator-pathname (function)
  "The accessor to the slot in a <code>file-kb-locator</code> that stores the
   actual pathname of the locator.  You should never side-effect this slot -
   create a new locator instead.")  

(defokbcclass ok-back:file-mixin (ok-back:okbc-kb-mixin)
  ()
  (:documentation
   "File-mixin should be used when defining a KB class that supports
    a KB locator that is a subtype of <code>file-kb-locator</code>.
    Default methods specialized on <code>file-kb-locator</code> are provided
    for <code>open-kb</code>, <code>close-kb</code>, <code>expunge-kb</code>,
    <code>save-kb-as</code>, and <code>create-kb-locator</code> on the
    assumption that the KBs can be opened simply by using the Lisp
    <code>load</code> function on the file specified by <code>pathname</code>.
    Any KRSs that require more specific processing of KBs that are stored in
    files should further specialize the <code>file-kb-locator</code> to
    something like <code>KRS-file-kb-locator</code> and provide
    their own methods for KB operations.  While defining KB classes, they
    should still use <code>file-mixin</code> because for a given KB-type
    it specifies that KBs are stored in a file.<P>

    See also <code>load-kb-from-file</code>."))

(defstruct ok-back:enumerator
  (associated-kb (okbc:current-kb))
  (id (allocate-enumerator-id))
  (freed nil))

(defdoc ok-back:enumerator (structure)
  "The abstract superclass of all enumerators in OKBC.  OKBC provides two
   subclasses that are instantiated by code in the OKBC kernel:
   <code>exhaustive-enumerator</code> and <code>network-enumerator</code>.
   A back end author who wants to make an enumerator class for a specific back
   end (such as for a KB that supports database cursors), should subclass
   this class.<P>

   All enumerators are created as the result of an enumeration over some
   OKBC call associated with a particular KB (except for
   <code>enumerate-list</code>).  This KB is stored in the
   <code>associated-kb</code> slot.  The <code>ID</code> slot is used by the
   network layer,and the <code>freed</code> slot is set to true when
   <code>free</code> is called on the enumerator.")
  
(defmethod print-object ((instance ok-back:enumerator) (stream t))
  (print-unreadable-object
   (instance stream :type t :identity t)
   (ignore-errors (format stream "ID=~D for ~A" (enumerator-id instance)
			  (name (enumerator-associated-kb instance))))))

(defstruct (ok-back:exhaustive-enumerator (:include ok-back:enumerator))
  all-elements)

(defdoc ok-back:exhaustive-enumerator (structure)
  "A simple class of enumerator used by the OKBC kernel to implement all of
   the default implementations of the enumerator operations.  The enumerator
   is \"exhaustive\" in the sense that it fetches the exhaustive set of all
   the values it could possibly return, and then caches them locally in the
   <code>all-elements</code>, dispensing them on demand.")

(defmethod print-object ((instance ok-back:exhaustive-enumerator) (stream t))
  (print-unreadable-object
   (instance stream :type t :identity t)
   (ignore-errors (format stream "ID=~D for ~A: ~D remaining elements"
		    (enumerator-id instance)
		    (name (enumerator-associated-kb instance))
		    (length (exhaustive-enumerator-all-elements instance))))))

(defstruct (ok-back:network-enumerator (:include ok-back:enumerator))
  (local-elements nil)
  (number-of-local-elements 0)
  (remote-exhausted-p nil)
  (ok-back:connection nil)
  (last-prefetch-increment nil)
  (creating-args nil))

(defmethod ok-back:connection ((conn ok-back:network-enumerator))
  (network-enumerator-connection conn))

(defdoc ok-back:network-enumerator (structure)
  "The class of enumerators used to represent enumerators received from some
   OKBC server over the network.  A local cache of elements is preserved
   on the client side, and new values are fetched in chunks determined
   by the <code>last-prefetch-increment</code> slot, which heuristically
   fetches in chunks the same size as the size specified by the user in the
   last call to <code>prefetch</code>.")

(defstruct ok-back:structure-kb
  (name :name)
   ;; Can be :LIVE or :OPEN
  (ok-back:connection (okbc:local-connection))
  (unique-id (allocate-unique-kb-id))
  (name-to-procedure-table *name-to-procedure-table*)
  (ok-back:kb-has-been-modified-p nil)
  (plist nil))

(defdoc ok-back:structure-kb (structure)
  "The structure-class counterpart KB class to the class <code>kb</code>.")

(defmethod name ((kb ok-back:structure-kb))
  (structure-kb-name kb))

(defmethod (setf name) (new-value (kb ok-back:structure-kb))
  (setf (structure-kb-name kb) new-value))

(defmethod plist ((kb ok-back:structure-kb))
  (structure-kb-plist kb))

(defmethod (setf plist) (new-value (kb ok-back:structure-kb))
  (setf (structure-kb-plist kb) new-value))

(defmethod ok-back:kb-has-been-modified-p ((kb ok-back:structure-kb))
  (structure-kb-kb-has-been-modified-p kb))

(defmethod (setf ok-back:kb-has-been-modified-p)
    (new-value (kb ok-back:structure-kb))
  (setf (structure-kb-kb-has-been-modified-p kb) new-value))

(defmethod ok-back:connection ((kb ok-back:structure-kb))
  (structure-kb-connection kb))

(defmethod (setf ok-back:connection) (new-value (kb ok-back:structure-kb))
  (setf (structure-kb-connection kb) new-value))

(defmethod unique-id ((kb ok-back:structure-kb))
  (structure-kb-unique-id kb))

(defmethod name-to-procedure-table ((kb ok-back:structure-kb))
  (structure-kb-name-to-procedure-table kb))

(defmethod (setf name-to-procedure-table) (new-value (kb ok-back:structure-kb))
  (setf (structure-kb-name-to-procedure-table kb) new-value))

(defstruct (ok-back:tell&ask-defaults-structure-kb
	     (:include ok-back:structure-kb))
  (ok-back:inference-level-for-tell&ask-defaults :taxonomic)
  (ok-back:timeout-for-tell&ask-defaults nil))

(defdoc ok-back:tell&ask-defaults-structure-kb (type)
  "This is the defstruct analogue of the <code>tell&ask-defaults-kb</code>
   kb class.")

(defmethod ok-back:inference-level-for-tell&ask-defaults
    ((x ok-back:tell&ask-defaults-structure-kb))
  (tell&ask-defaults-structure-kb-inference-level-for-tell&ask-defaults x))

(defmethod (setf ok-back:inference-level-for-tell&ask-defaults)
    ((value t) (x ok-back:tell&ask-defaults-structure-kb))
  (setf (tell&ask-defaults-structure-kb-inference-level-for-tell&ask-defaults
	 x)
	value))

(defmethod ok-back:timeout-for-tell&ask-defaults
    ((x ok-back:tell&ask-defaults-structure-kb))
  (tell&ask-defaults-structure-kb-timeout-for-tell&ask-defaults x))

(defmethod (setf ok-back:timeout-for-tell&ask-defaults)
    ((value t) (x ok-back:tell&ask-defaults-structure-kb))
  (setf (tell&ask-defaults-structure-kb-timeout-for-tell&ask-defaults x)
	value))

(defstruct (ok-back:file-tell&ask-defaults-structure-kb 
	     (:include ok-back:tell&ask-defaults-structure-kb)))

(defdoc ok-back:file-tell&ask-defaults-structure-kb (structure)
  "A defstruct <code>KB</code> class that knows about saving itself to files.
   This class is the <code>structure-class</code> equivalent of a KB class
   built on <code>file-mixin</code>, <code>tell&ask-defaults-kb</code>,
   and <code>kb</code>.")

(defstruct (ok-back:caching-structure-kb (:include ok-back:structure-kb))
   (cache (tries:new-root-hybrid-trie :okbc-cache nil))
   (ok-cache:timestamp nil)
   (allow-caching-p t)
   (caching-policy :defensive))

(defdoc ok-back:caching-structure-kb (structure)
  "A defstruct <code>KB</code> class that is the <code>structure-class</code>
   equivalent of a KB class built on <code>caching-mixin</code>,
   and <code>kb</code>.")

(defmethod ok-cache:cache ((kb ok-back:caching-structure-kb))
  (caching-structure-kb-cache kb))

(defmethod (setf ok-cache:cache) (new-value (kb ok-back:caching-structure-kb))
  (setf (caching-structure-kb-cache kb) new-value))

(defmethod ok-cache:caching-policy ((instance ok-back:caching-structure-kb))
  (caching-structure-kb-caching-policy instance))

(defmethod (setf ok-cache:caching-policy)
    ((new-value t) (instance ok-back:caching-structure-kb))
  (setf (caching-structure-kb-caching-policy instance) new-value))

(defmethod ok-cache:flush-cache ((kb ok-back:caching-structure-kb))
  (when (boundp 'ok-cache:*ephemeral-cache*)
    (setq ok-cache:*ephemeral-cache*
	  (tries:new-root-hybrid-trie :okbc-cache nil)))
  (setf (ok-cache:cache kb) (tries:new-root-hybrid-trie :okbc-cache nil))
  (setf (ok-cache:timestamp kb) (get-universal-time)))

(defmethod ok-cache:allow-caching-p ((instance ok-back:caching-structure-kb))
  (caching-structure-kb-allow-caching-p instance))

(defmethod (setf ok-cache:allow-caching-p)
    ((new-value t) (instance ok-back:caching-structure-kb))
  (setf (caching-structure-kb-allow-caching-p instance) new-value))

(defmethod ok-cache:timestamp ((kb ok-back:caching-structure-kb))
  (caching-structure-kb-timestamp kb))

(defmethod (setf ok-cache:timestamp)
 (new-value (kb ok-back:caching-structure-kb))
  (setf (caching-structure-kb-timestamp kb) new-value))

(defstruct (ok-back:network-structure-kb
	     (:include ok-back:caching-structure-kb)))

(defdoc ok-back:network-structure-kb (structure)
  "The structure-class equivalent of <code>network-kb</code>.")

(defstruct (ok-back:default-inheritance-structure-kb
	       (:include ok-back:caching-structure-kb)))

(defdoc ok-back:default-inheritance-structure-kb (structure)
  "A defstruct <code>KB</code> class that is the <code>structure-class</code>
   equivalent of a KB class built on <code>default-inheritance-mixin</code>
   <code>caching-mixin</code>, and <code>kb</code>.")

(defstruct (ok-back:file-structure-kb
	     (:include ok-back:default-inheritance-structure-kb)))

(defdoc ok-back:file-structure-kb (structure)
  "A defstruct <code>KB</code> class that knows about saving itself to files.
   This class is the <code>structure-class</code> equivalent of a KB class
   built on <code>file-mixin</code>, <code>default-inheritance-mixin</code>
   <code>caching-mixin</code>, and <code>kb</code>.")

(defstruct (ok-back:procedure (:predicate is-a-procedure-p))
  name
  arguments
  expression
  environment
  function-object
  interpreted-wrt-kb
  as-sexpressions-p
  arguments-string
  expression-string
  environment-string)

(defdoc ok-back:procedure (structure)
  "The data structure used to represent OKBC procedure objects.")

(defmethod okbc-procedure-p ((thing t)) nil)
(defmethod okbc-procedure-p ((thing ok-back:procedure)) t)

(defmethod funcall-test
    ((testfn ok-back:procedure) x y kb (kb-local-only-p t))
  (ok-back:call-procedure-internal testfn kb (list x y)))

;==============================================================================

(defconstant ok-back:*undefined-value* '__undefined__
  "A magic value used in <code>abstract-handle</code>s to indicate that it is
   not known within the current implementation what real-world object is
   denoted by the handle.")

(defstruct ok-back:abstract-handle
  id
  kb-id
  (thing ok-back:*undefined-value*)
  (fast-hash-key nil))

(defdoc ok-back:abstract-handle (structure)
  "The abstract superclass structure class of all \"handle\" objects used
   by the OKBC implementation (e.g., <code>frame-handle</code> and
   <code>remote-value</code>).  Handles are uniquely identified by a pair
   of fixnums, the ID and the KB-ID.  A slot called THING provides a back
   pointer to the real object denoted by the handle (this is never the case
   for handles received by clients from network-based servers).<P>

   Note that there is nothing magical about the KB-ID slot.  The fact that
   a handle object contains the kb-id of a particular KB in the slot does
   <i>not</i> necessarily mean that the object resides in the KB.<P>

   A special KB-ID of -1 is used to denote handles for OKBC defined handles,
   such as for the OKBC standard names.")

(defvar *initial-sxhash-value* 19009)

#+Lucid
(eval-when (compile load eval)
  ;; A bit of lucid-specific magic.  The lucid::set-%symbol-sxhash form
  ;; is defined as a compiler macro that only exists when we are in the
  ;; production compiler, but we still want things to work when we're using
  ;; the development compiler.  Thus, we eval the form and compile it with
  ;; production compiler switched on by binding.  Note that just having
  ;; the declaration in the function dooesn't do the trick to force it
  ;; into production mode for this one function.
  (progn (eval '(defun set-%symbol-sxhash (symbol value)
		 (declare (optimize (speed 3) (safety 0)
			   (compilation-speed 0) (space 0)))
		 (lucid::set-%symbol-sxhash symbol value)
		 symbol))
	 (let ((lucid:*use-sfc* nil))
	   (compile 'set-%symbol-sxhash))))

(defmethod fast-hash-key ((instance ok-back:abstract-handle))
  (abstract-handle-fast-hash-key instance))

(defmethod (setf fast-hash-key) (new-value (instance ok-back:abstract-handle))
  (setf (abstract-handle-fast-hash-key instance) new-value))

(defmethod initialize-fast-hash-key ((instance ok-back:abstract-handle))
  #+Lucid
  (let ((sym (make-symbol "")))
    (setf (fast-hash-key instance) sym)
    (set-%symbol-sxhash sym *initial-sxhash-value*)
    (setq *initial-sxhash-value*
	  (lucid::find-hash-prime (+ 1 *initial-sxhash-value*) 1))
    ;; Install a back pointer.  Note:  this is not a memory leak because
    ;; the symbol is uninterned.
    (setf (symbol-value sym) instance)
    sym)
  #-Lucid
  (flet ((find-hash-prime (given offset)
	   (+ given offset)))
    ;; This is a cludge.  We'd really like to find a better way to
    ;; get a good hash prime.
    (setf (fast-hash-key instance) *initial-sxhash-value*)
    (setq *initial-sxhash-value*
	  (find-hash-prime (+ 1 *initial-sxhash-value*) 1)))
  instance)

;; Note:  We have an even number of slots here.  This is because the memory
;; allocation rounds up to an even word boundary.
(defstruct (ok-back:frame-handle (:include ok-back:abstract-handle))
  (frame-type nil)
  (plist nil))

(defdoc ok-back:frame-handle (structure)
  "The structure class used to implement KRS-independent frame handles.
   If you are implementing a back end for a system that has no obvious
   notion of a frame handle, and you feel inclined to create your own
   class of frame handle, you may choose to use this class.  Doing so
   will save duplication by the network transport layer.")

(defdoc ok-back:frame-handle-frame-type (function)
  "An accessor to read the FRAME-TYPE slot of a KRS-independent frame handle.
   This is likely to be used by back ends that keep a cached version of the
   frame type here.")

(defdoc ok-back:frame-handle-p (function)
  "A predicate that is true of KRS independent frame handles.")

(defdoc ok-back:frame-handle-plist (function)
  "An accessor to read the PLIST slot of a KRS-independent frame handle.
   This is likely to be used by back ends that keep a cached version of the
   frame types and want to store other interesting stuff here.")

(defdoc ok-back:frame-handle-thing (function)
  "An accessor to read the THING slot of a KRS-independent frame handle.
   This is unlikely to be used by back ends.  The THING slot contains
   either the frame that is denoted by the <code>frame-handle</code>,
   or <code>*undefined-value*</code>.  This slot will always contain
   <code>*undefined-value*</code> for frame handles on a client that were
   fetched from a server.")

(defdoc ok-back:frame-handle-id (function)
  "An accessor to read the ID of a KRS-independent frame handle.  This is
   unlikely to be used by back ends, but may be useful, for example, if
   a back end wants to use <code>frame-handle</code> instances to represent
   in-core frames for frames that actually live in a database.  The
   <code>frame-handle-id</code> of a <code>frame-handle</code> is guaranteed
   to be a fixnum.  It may be convenient to preserve a correspondence between
   such a number and a database ID.")

(defdoc ok-back:frame-handle-kb-id (function)
  "An accessor to read the KB ID of a KRS-independent frame handle.  This is
   unlikely to be used by back ends, but may be useful, for example, if
   a back end wants to use <code>frame-handle</code> instances to represent
   in-core frames for frames that actually live in a database.  The
   <code>frame-handle-kb-id</code> of a <code>frame-handle</code> is guaranteed
   to be a fixnum.  It may be convenient to preserve a correspondence between
   such a number and a database ID along with the
   <code>frame-handle-id</code>.")

(defstruct (ok-back:remote-value (:include ok-back:abstract-handle)))

(defdoc ok-back:remote-value (structure)
  "The structure class used to implement remote value pointers in the
   network layer.  A subclass of <code>abstract-handle</code>.")

(defstruct ok-back:quasi-symbol
  ok-back:name
  package)

(defdoc ok-back:quasi-symbol (structure)
  "In OKBC, care is taken not to pollute the package system when talking to
   remote KBs.  In general, remote KBs and clients will have a completely
   different package architecture.  It is undesirable to create packages on
   the client side to match the server's notion of packages (or vice versa)
   because of the complications of package inclusion and memory leakage.
   Because of these problems, the OKBC implementation provides a class of
   <code>quasi-symbol</code>s.  <code>Quasi-symbol</code>s aer interned in
   the same way as real symbols, but they have their own packages
   (<code>quasi-package</code>s), so the package system is not polluted.
   This class implements <code>quasi-symbol</code>s in the obvious way.<P>

   Back end implementations are required to accept quasi-symbols as reasonable
   data structres, such as as names for frames, and they must be able to
   load and save them.  Back end implementors will probably want to
   specialize <code>print-quasi-symbol-in-kb</code> so as to be able to
   save <code>quasi-symbol</code>s, and possibly
   <code>quasi-symbol-reader</code> as a readtable macro character reader
   function to read them in.")

(defdoc ok-back:quasi-symbol-name (function)
  "The <code>quasi-symbol</code> analogue of <code>symbol-name</code>.")

(defdoc ok-back:quasi-symbol-package (function)
  "The <code>quasi-symbol</code> analogue of <code>symbol-package</code>.")

(defun quasi-symbol-reader (stream char arg)
  "A simple readtable macro character reader function for reading in and
   interning <code>quasi-symbol</code>s written out in the form:
   <code>#Qppp|nnn</code>, where <code>ppp</code> is the name of a
   <code>quasi-package</code>, and <code>nnn</code> is the name of the
   <code>quasi-symbol</code>."
  (declare (ignore char arg))
  (let ((package-name (read stream t nil t)))
    (assert (char= #\| (read-char stream)))
    (let ((symbol-name (read stream t nil t)))
      (intern-quasi-symbol symbol-name package-name))))

(defmethod name ((instance ok-back:quasi-symbol))
  (ok-back:quasi-symbol-name instance))

(defmethod print-object ((instance ok-back:quasi-symbol) (stream t))
  (declare (special *current-kb-for-io-syntax*))
  (if *current-kb-for-io-syntax*
      (ok-back:print-quasi-symbol-in-kb instance *current-kb-for-io-syntax*
					stream)
      (if *print-readably*
	  (call-next-method)
	  (format stream "Q|~A::~A"
	    (name (ok-back:quasi-symbol-package instance)) (name instance)))))

(defokbcgeneric ok-back:print-quasi-symbol-in-kb (instance kb stream)
  (:documentation "Used to print a <code>quasi-symbol</code> with respect to
   a particular KB.  Since the KB may have defined its own IO syntax
   and/or reader macro for <code>quasi-symbols</code> this method can be
   specialized on a per-kb basis.  This generic function is invoked if
   <code>*current-kb-for-io-syntax*</code> is non-null.  A back end supplied
   method for this generic function should be sensitive to the
   <code>*current-kb-for-io-syntax*</code>."))

(defmethod ok-back:print-quasi-symbol-in-kb (instance (kb t) stream)
  (if *print-readably*
      (error "Cannot write quasi-symbol readably")
      (format stream "Q|~A::~A"
	(name (ok-back:quasi-symbol-package instance)) (name instance))))

(defstruct quasi-package
  ok-back:name
  (symbol-table (make-hash-table :test #'equal)))

(defmethod name ((instance quasi-package))
  (quasi-package-name instance))

(defmethod print-object ((instance quasi-package) (stream t))
  (print-unreadable-object (instance stream :type t :identity t)
    (princ (quasi-package-name instance) stream)))

;; Moved here because of a CLOS bogosity in Franz that was causing forward
;; reference classes not to get resolved.  This should minimise the
;; constraints put on defsystems.
(defokbcclass ok-back:frames-have-clos-slots-as-okbc-slots-mixin
    (ok-back:okbc-kb-mixin)
  ()
  (:documentation "A mixin class of OKBC kb that confers on the KB the ability
   to view all CLOS standard-object instances and all defstruct
   structure-object instances as frames.  CLOS and defstruct slots
   respectively appear as OKBC slots."))

