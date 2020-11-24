;;; -*- Package: Nuprl; Syntax: Common-lisp; Base: 10. -*-

;;; Contains the functions which convert the abstract syntax tree into the
;;; desired form.  Each variable reference is turned into a reference of a
;;; descriptor.  In processing, we fill in the various fields of the descriptors.

(in-package "NUPRL")

(defun convert (exp)
  ;; Convert the given expression, and return it.
  (case (node-kind exp)
    ((mk-boolconst mk-intconst mk-fail mk-termconst mk-tokconst mk-empty)
      exp )
    (mk-failwith
     (convert-list-in-place (cdr exp))
     exp)
    (mk-var
     (let ((desc (lookup-name (second exp))))
       (when (is-internal-function desc)
	 (setf (function-all-uses-full-appl desc) nil))
       (make-var :desc desc)))
    (mk-dupl
     (convert-list-in-place (cdr exp))
     exp)
    (mk-list
     (convert-list-in-place (cdr exp))
     (make-ml-list :list (cdr exp)))
    (mk-straint (convert (second exp)))
    (mk-appn (convert-appn exp))
    (mk-binop
     (case (second exp)
       (|%&| (make-and :left (convert (third exp)) :right (convert (fourth exp))))
       (|%or| (make-or :left (convert (third exp)) :right (convert (fourth exp))))
       (otherwise (convert-appn
	    `(mk-appn (mk-appn (mk-var ,(second exp)) ,(third exp)) ,(fourth exp))))))
    (mk-unop
     (convert-appn `(mk-appn (mk-var ,(second exp)) ,(third exp))))
    (mk-assign
     (setf (second exp) (conv-vs-in-current-env (second exp)))
     (setf (third exp) (convert (third exp)))
     exp)
    (mk-seq
      (convert-list-in-place (second exp))
      (setf (third exp) (convert (third exp)))
      exp )
    (mk-test (convert-test exp))
    (mk-trap (convert-trap exp))
    (mk-abstr (convert-abstr exp))
    (mk-in (convert-in exp))
    (mk-ina (convert-in exp))
    (mk-ind (convert (third exp)))
    ((mk-let mk-letrec mk-letref mk-abstype mk-absrectype)
     (convert-decl exp))))

(defun convert-list-in-place (l)
  ;; Replace every member of the list l with its conversion.
  (hack-list #'convert l))

(defun convert-arms-in-place (arms)
  (mapc #'convert-test-exp-in-place (first arms))
  (when (cdr arms)
    (convert-test-exp-in-place (second arms))))

(defun convert-test-exp-in-place (test-exp)
  (convert-list-in-place (cdr test-exp)))

(defun convert-appn (exp)
  ;; Collect the arguments of the application.
  (do ((exp (strip-straints (second exp)) (strip-straints (second exp)))
       (args (ncons (convert (third exp))) (cons (convert (third exp)) args)))
      ((neq (node-kind exp) 'mk-appn)
       (make-appn
	 :fun (if (neq (node-kind exp) 'mk-var)
		 (convert exp)
		 ;; This has to be a special case as convert unconditionally bashes
		 ;; the all-uses-full-appl field.
		 (let ((desc (lookup-name (second exp))))
		   (when (and (is-internal-function desc)
			      (< (length args) (function-arity desc)))
		     (setf (function-all-uses-full-appl desc) nil))
		   (make-var :desc desc)))
	 :args args))))

(defvar *conversion-env* nil)

(defmacro with-extended-env (descs &body body)
  `(let ((*conversion-env* (cons ,descs *conversion-env*)))
     ,@body))

(defun lookup-name (id)
  (flet ((lookup-local ()
	   (block lookup-local
	     (dolist (descs *conversion-env*)
	       (let ((result (assoc id descs)))
		 (when result (return-from lookup-local result))))))
	 (lookup-global ()
	   (declare (special global%env))
	   (assoc id global%env))
	 (lookup-primitive ()
	   (cond ((eql id '|nil|)
		  '#.(make-value :id '|nil| :name nil))
		 ((eql id lastvalname)
		  '#.(make-value :id '|it| :name '%it))
		 ((get id 'mldescriptor)))))
    (cond ((lookup-local))
	  ((lookup-global))
	  ((lookup-primitive))
	  (t (syserror `(lookup-name ,id))))))

(defun strip-straints (exp)
  ;; Return exp with all top level type constraints stripped off.
  (do ((e exp (second e)))
      ((neq (node-kind e) 'mk-straint) e)))

(defun walk-varstruct (varstruct f)
  #+symbolics (declare (sys:downward-funarg f))
  (labels ((walk-vs (vs)
	     (case (node-kind vs)
	       (mk-var
		(funcall f vs))
	       (mk-dupl
		(walk-vs (pair-left vs))
		(walk-vs (pair-right vs)))
	       (mk-binop
		(walk-vs (binop-left vs))
		(walk-vs (binop-right vs)))
	       (mk-list
		(dolist (l (ml-list-list vs))
		  (walk-vs l))))))
    (walk-vs varstruct)))

(defun descs-of-varstructs (varstructs)
  (let ((descriptors nil))
    (dolist (varstruct varstructs)
      (walk-varstruct
	varstruct (prllambda (vs) (push (var-desc vs) descriptors))))
    descriptors))

(defun convert-arms (arms)
  (mapcar
    (prllambda (arm)
      (make-arm
	:kind (first arm)
	:test (convert (second arm))
	:exp (convert (cddr arm))))
    arms))

(defun convert-else (else)
  (make-else
    :kind (first else)
    :exp (convert (cdr else))))

(defun convert-test (exp)
  (make-test
    :conditional (convert-arms (second exp))
    :else (if (not (null (cddr exp)))
	     (convert-else (third exp))
	     '(EMPTY nil))))

(defun convert-trap (exp)
  (let ((binding-id nil)
	(else-exp (fourth exp)))
    (setf else-exp
	  (cond ((null else-exp)
		 '(EMPTY nil))
		((symbolp (first else-exp))
		 (convert-else else-exp))
		(t
		 (setf binding-id (cdr (first else-exp)))
		 (setf (first else-exp) (car (first else-exp)))
		 (with-extended-env (list (make-value :id binding-id :name binding-id))
		   (convert-else else-exp)))))
    (make-trap
      :exp (convert (second exp))
      :conditional (convert-arms (third exp))
      :else else-exp
      :else-binding-id binding-id)))

(defun convert-abstr (exp)
  ;; Collect the parameter list for the abstraction, then produce the converted
  ;; abstraction form.  The parameter list is reversed.  This is necessitated by
  ;; the runtime closure environment format.
  (do ((params (ncons (convert-varstruct (second exp)))
	       (cons (convert-varstruct (second exp)) params))
       (exp (strip-straints (third exp)) (strip-straints (third exp))))
      ((neq (node-kind exp) 'mk-abstr)
       (with-extended-env (descs-of-varstructs params)
	 (make-abstr :body (convert exp) :params params)))))


(defun convert-top-level-of-abstr (exp)
  ;; Process only the parameters of the abstraction.  This is necessary for
  ;; implementing recursion.  The order of the collected parameters is the
  ;; reverse of that in which they are processed.
  (do ((params (ncons (convert-varstruct (second exp)))
	       (cons (convert-varstruct (second exp)) params))
       (exp (strip-straints (third exp)) (strip-straints (third exp))))
      ((neq (node-kind exp) 'mk-abstr)
       (make-abstr :body exp :params params))))

(defun convert-body-of-abstr (abstr)
  ;; Convert the body of the given abstraction in an environment given
  ;; by the descs field of the abstraction.  Used in implementing recursion.
  (with-extended-env (descs-of-varstructs  (abstr-params abstr))
    (setf (abstr-body abstr) (convert (abstr-body abstr)))
    abstr))
  
(defun convert-in (exp)
  ;; Convert the body of the in expression in an environment in which the
  ;; names defined in the declaration of the in expression are available.
  (let ((decl (convert-decl (second exp))))
    (with-extended-env (descs-of-varstructs (decl-varstructs decl))
      (make-in :decl decl :body (convert (third exp))))))

(defun convert-decl (decl)
  (setf decl (strip-straints decl))
  (case (node-kind decl)
    ((mk-abstype mk-absrectype)
     (with-extended-env (mk-isomorphism-descriptors (second decl))
       (convert-decl (third decl))))
    (otherwise
     (multiple-value-bind (varstructs values)
	 (multiple-value-call
	   (case (node-kind decl)
	     (mk-let #'process-let)
	     (mk-letrec #'process-letrec)
	     (mk-letref #'process-letref))
	   (chop-vs-and-value (second decl) (third decl)))
       (make-decl :kind (node-kind decl) :varstructs varstructs :values values)))))

(defun mk-isomorphism-descriptors (type-defs)
  ;; Returns a list of descriptors for the absract type isomorphisms for the
  ;; types defined in type-defs.
  (mapcan
    (prllambda (type-def)
      (list*
	(mk-isom-desc (concat '|abs_| (first type-def)))
	(mk-isom-desc (concat '|rep_| (first type-def)))
	nil))
    type-defs))

(defun process-let (varstructs values)
  ;; Convert each of the varstructs and values.
  (dolists ((vs varstructs)
	    (val values))
	   ((conv-varstructs nil)
	    (conv-values nil))
	   (values (nreverse conv-varstructs) (nreverse conv-values))
    (let ((cvs (convert-varstruct vs))
	  (cval (convert val)))
      (when (and (eql (node-kind cval) 'mk-abstr)
		 (eql (node-kind cvs) 'mk-var))
	;; The function value is to be associated with a name.  Replace the
	;; descriptor with a function descriptor.
	(let ((fdesc (mk-function-desc
		       (desc-id (var-desc cvs))
		       (length (abstr-params cval)))))
	  (setf (var-desc cvs) fdesc)))
      (push cvs conv-varstructs)
      (push cval conv-values))))

(defun process-letrec (varstructs values)
  ;; We make two passes over the arguments.  In the first pass, we
  ;; define the descriptors for each varstruct .  In the second pass we
  ;; convert each of the value components in an environment in which the
  ;; descriptors are visible.
  (multiple-value-bind (nvarstructs nvalues)
      (letrec-define-descriptors varstructs values)
    (with-extended-env (descs-of-varstructs nvarstructs)
      (letrec-convert-values nvalues)
      (values nvarstructs nvalues))))

(defun letrec-define-descriptors (varstructs values)
  (dolists ((vs varstructs)
	    (val values))
	   ((conv-varstructs nil)
	    (conv-values nil))
	   (values conv-varstructs conv-values)
    (let ((id (find-id-for-abstr-match vs))
	  (top (convert-top-level-of-abstr val)))
      (when id
	(push top conv-values)
	(push (make-var
		:desc (mk-function-desc id (length (abstr-params top))))
	      conv-varstructs)))))

(defun letrec-convert-values (values)
  (hack-list
    (prllambda (val) (if (eql (node-kind val) 'mk-abstr) (convert-body-of-abstr val)))
    values))

(defun process-letref (varstructs values)
  (hack-list (prllambda (vs) (convert-varstruct vs)) varstructs)
  (hack-list #'convert values)
  (values varstructs values))

(defun general-varstruct-converter (varstruct var-action)
  #+symbolics (declare (sys:downward-funarg var-action))
  (labels ((conv-vs (vs)
	     (case (node-kind vs)
	       (mk-empty vs)
	       (mk-var
		(setf (var-desc vs)
		      (funcall var-action (second vs)))
		vs)
	       (mk-straint (conv-vs (second vs)))
	       (mk-dupl (conv-varstructs (cdr vs)) vs)
	       (mk-binop (conv-varstructs (cddr vs)) vs)
	       (mk-list
		(conv-varstructs (cdr vs))
		(make-ml-list :list (cdr vs)))
	       (otherwise (syserror (cons vs '(bad varstruct))))))
	   (conv-varstructs (varstructs)
	     (hack-list #'conv-vs varstructs)))
    (conv-vs varstruct)))

(defun convert-varstruct (varstruct)
  (general-varstruct-converter
    varstruct
    #'mk-value-desc))

(defun conv-vs-in-current-env (varstruct)
  (general-varstruct-converter
    varstruct
    #'lookup-name))

(defun find-id-for-abstr-match (vs)
  ;; The unconverted varstruct vs is known to match a function value, and thus
  ;; must either define an identifier or be the empty varstruct.  In the first case
  ;; return the identifier, and in the second return nil.
  (setf vs (strip-straints vs))
  (case (node-kind vs)
    (mk-empty nil)
    (mk-var (second vs))
    (otherwise (syserror (cons vs '(bad varstruct for abstraction))))))

(defun chop-vs-and-value (vs val)
  ;; Returns as values a list of varstructs and a list of values.  Each corresponding
  ;; varstruct and value are subtrees of vs and val, and occur in corresponding positions
  ;; in vs and val.  The order of the elements of the result lists is the order in which
  ;; they occur in an in-order traversal of vs.  The arguments may be unconverted.
  (let ((vs-result nil)
	(val-result nil))
    (labels ((chop (vs val)
	       (setf val (strip-straints val))
	       (setf vs (strip-straints vs))
	       (case (node-kind vs)
		 ((mk-empty mk-var) (add-pair vs val))
		 (mk-dupl
		  (if (eql (node-kind val) 'mk-dupl)
		      (mapc #'chop (cdr vs) (cdr val))
		      (add-pair vs val)))
		 (mk-binop
		  (cond ((eql (node-kind val) 'mk-binop)
			 (mapc #'chop (cddr vs) (cddr val)))
			((and (eql (second vs) '|.|)
			      (eql (node-kind val) 'mk-list)
			      (not (null (cdr val))))
			 (chop (third vs) (second val))
			 (chop (fourth vs) (cons 'mk-list (cddr val))))
			(t (add-pair vs val))))
		 (mk-list
		  (let ((lval (canonicalize-list val)))
		    (if (and (neq lval 'non-list)
			     (= (length (cdr vs)) (length lval)))
			(mapc #'chop (cdr vs) lval)
			(add-pair vs val))))
		 (otherwise (syserror (cons vs '(bad varstruct))))))
	     (add-pair (vs val)
	       (push vs vs-result)
	       (push val val-result)))
      (chop vs val)
      (values (nreverse vs-result) (nreverse val-result)))))


;;; This function won't compile in some versions of Franz lisp.  
;;; (defun canonicalize-list (l) 'non-list) will do in its place
;;; (although it's not the best solution).
(defun canonicalize-list (l)
  ;; If the expression l represents a list whose top level structure is known,
  ;; return the list.  Otherwise return the atom 'non-list.
  (block canonical-list
    (labels ((can-list (l)
	       (case (node-kind l)
		 (mk-straint (can-list (second l)))
		 (mk-list (cdr l))
		 (mk-binop
		  (if (eql (second l) '|.|)
		      (if (is-nil (fourth l))
			  (ncons (third l))
			  (cons (third l) (can-list (fourth l))))
		      (return-from canonical-list 'non-list)))
		 (otherwise (return-from canonical-list 'non-list))))
	     (is-nil (v)
	       (case (node-kind v)
		 (mk-straint (is-nil (second v)))
		 (mk-list (null (cdr v)))
		 (mk-var (eql (second v) '|nil|))
		 (otherwise nil))))
      (can-list l))))
