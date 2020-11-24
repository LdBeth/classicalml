;;; -*- Syntax: Common-lisp; Base: 10.; Package: Nuprl; -*-

(in-package "NUPRL")


;;; Provides the translation from ML abstract syntax to Lisp.

(defvar *do-tail-recursion* t
  "A flag controlling the attempts to do tail recursion optimization.")
(defvar *functions-being-defined* nil
  "A list of the functions for which tail recursive applications can be optimized.")

(defmacro without-tail-recursion (&body body)
  ;; A macro to be wrapped around any calls to tre in which tail recursion
  ;; optimization should not be attempted.
  `(let ((*do-tail-recursion* nil)) ,@body))

(defvar *function-was-defined* nil
  "This flag is set whenever a function is defined during the translation.")

(defun tran (e)
  ;; The top level entry to the translation process.  Convert the expression tree
  ;; and handle the expressions which can only occur at the top level.
  (let ((e (convert e))
	(*do-tail-recursion* t))
    (when e
      (case (node-kind e)
	(mk-letref
	 (tran-top-level-letref (decl-varstructs e) (decl-values e)))
	(mk-letrec
	 (tran-top-level-letrec (decl-varstructs e) (decl-values e)))
	(mk-let
	 (tran-top-level-let (decl-varstructs e) (decl-values e)))
	(otherwise
	 (tre e)
	 ;; This results in calls to the compiler during proof expansion.
         ;; There doesn't seem to be any advantage to keeping it.
	 #| (let* ((*function-was-defined* nil)
		   (val-code (tre e)))
	      (if *function-was-defined*
		  (progn
		    ;; We wrap a dummy function definition around the code so that the
		    ;; internal function definitions get compiled.
		    (push `(defun %val () ,val-code) %compfns)
		    '(%val))
		  val-code))|#)))))

(defun tre (e)
  ;; The main ML to Lisp translation function.  Given a converted ML abstract
  ;; syntax tree it returns the corresponding lisp code.  
  (case (node-kind e)
    ((mk-boolconst mk-intconst)
     (const-value e))
    ((mk-termconst mk-tokconst)
     (qeval (const-value e)))
    (mk-empty nil)
    (mk-fail
     `(breakout evaluation 'fail))
    (mk-failwith
     (without-tail-recursion
      `(breakout evaluation ,(tre (failwith-exp e)))))
    (mk-var
     (name-for-desc (var-desc e)))
    (mk-and
     `(and ,(tre (and-left e)) ,(tre (and-right e))))
    (mk-or
     `(or ,(tre (or-left e)) ,(tre (or-right e))))
    (mk-dupl
     (without-tail-recursion
       (testeval `(cons ,(tre (pair-left e)) ,(tre (pair-right e))))))
    (mk-list
     (without-tail-recursion
       (testeval `(list ,@(mapcar #'tre (ml-list-list e))))))
    (mk-appn
     (tran-appn
       (appn-fun e)
       (without-tail-recursion
	 (mapcar #'tre (appn-args e)))))
    (mk-abstr
     (tran-abstr (abstr-body e) (abstr-params e)))
    (mk-assign
     (tran-assign (assign-varstruct e) (assign-value e)))
    (mk-seq
     `(progn
	,@(without-tail-recursion (mapcar #'tre (seq-for-effect e)))
	,(tre (seq-value e))))
    (mk-test
     (tran-test (test-conditional e) (test-else e)))
    (mk-trap
     (tran-trap (trap-exp e) (trap-conditional e) (trap-else e) (trap-else-binding-id e)))
    (mk-in
     (tran-in (in-decl e) (in-body e)))
    (otherwise (syserror `(bad exp kind in tre ,(node-kind e))))))

(defun testeval (e)
  (if (is-constant e)
      (qeval (eval e))
      e))

(defun is-constant (e)
  (if (atom e)
      (or (numberp e) (member e '(t nil)))
      (case (car e)
	(quote t)
	((cons list) (forall #'is-constant (cdr e)))
	(otherwise nil))))

(defmacro fail-match ()
  `(breakout evaluation 'match))

(defvar *temp-names-for-matching* nil
  "A list of names for holding temporaries during varstruct matching.")

(defun build-matching-code (varstructs names-for-varstructs)
  ;; Constructs code which performs varstruct matching.  Given a list of
  ;; varstructs and a list of names for the values corresponding to
  ;; those varstructs it returns as values a lisp form which performs
  ;; the matching and a list of the names which are given values by this
  ;; code.  The code will modify the values of the names for which non
  ;; trivial matching must be performed.
  #+symbolics (declare (values matching-code names-defined-by-matching))
  (let ((matching-code-list nil)
	(temp-names-avail *temp-names-for-matching*)
	(names-defined-by-matching nil)
	(temp-names-used nil))
    (labels ((save-exp (exp)
	       (push exp matching-code-list))
	     (new-name ()
	       (let ((name
		       (if (not (null temp-names-avail))
			   (pop temp-names-avail)
			   (let ((name (gen-temp-name "match-")))
			     (push name *temp-names-for-matching*)
			     name))))
		 (when (not (member name temp-names-used))
		   (push name temp-names-used))
		 name))
	     (return-name (name)
	       (push name temp-names-avail))
	     (match-var (val vs)
	       (push (name-for-desc (var-desc vs)) names-defined-by-matching)
	       (save-exp `(setq ,(name-for-desc (var-desc vs)) ,val)))
	     (match-pair (val vs left-sel right-sel)
	       (save-exp `(unless (consp ,val) (fail-match)))
	       (let ((left (funcall left-sel vs)))
		 (if (eql (node-kind left) 'mk-var)
		     (match-var `(car ,val) left)
		     (let ((temp (new-name)))
		       (save-exp `(setq ,temp (car ,val)))
		       (match temp left)
		       (return-name temp))))
	       (let ((right (funcall right-sel vs)))
		 (if (eql (node-kind right) 'mk-var)
		     (match-var `(cdr ,val) right)
		     (progn
		       (save-exp `(setq ,val (cdr ,val)))
		       (match val right)))))
	     (match-list (val vs)
	       (let ((temp nil))
		 (when (some (prllambda (vs) (neq (node-kind vs) 'mk-var)) (ml-list-list vs))
		   (setq temp (new-name)))
		 (dolist (vs (ml-list-list vs))
		   (save-exp `(unless (consp ,val) (fail-match)))
		   (if (eql (node-kind vs) 'mk-var)
		       (progn
			 (match-var `(car ,val) vs)
			 (save-exp `(setq ,val (cdr ,val))))
		       (progn
			  (save-exp `(setq ,temp (car ,val)))
			  (save-exp `(setq ,val (cdr ,val)))
			  (match temp vs))))
		 (when temp (return-name temp))
		 (save-exp `(unless (null ,val) (fail-match)))))
	     (match (val vs)
	       (case (node-kind vs)
		 (mk-var (match-var val vs))
		 (mk-dupl (match-pair val vs #'pair-left #'pair-right))
		 (mk-binop (match-pair val vs #'binop-left #'binop-right))
		 (mk-list (match-list val vs)))))
      (dolists ((vs varstructs) (name names-for-varstructs))
	       () ()
	(when (not (eql (node-kind vs) 'mk-var))
	  (match name vs)))
      (values
	(if (null temp-names-used)
	    (if (<= (length matching-code-list) 1)
		(nreverse matching-code-list)
		`(progn ,@(nreverse matching-code-list)))
	    `(let ,temp-names-used
	       ,@(nreverse matching-code-list)))
	names-defined-by-matching))))


(defun top-level-names-of-varstructs (varstructs)
  (mapcar
    (prllambda (vs)
      (if (eql (node-kind vs) 'mk-var)
	  (name-for-desc (var-desc vs))
	  (gen-temp-name "vs-")))
    varstructs))

(defun process-function-declarations (varstructs values)
  ;; Given lists of varstructs and values, return lists of the names of functions
  ;; defined, the expression trees for the function values and the varstructs of
  ;; the functions.
  #+symbolics (declare (values function-names function-values function-varstructs))
  (dolists ((vs varstructs) (val values))
	   ((function-names nil) (fvalues nil) (function-varstructs nil))
	   (values function-names fvalues function-varstructs)
    (when (and (eql (node-kind vs) 'mk-var)
	       (eql (node-kind val) 'mk-abstr))
      (push (name-for-desc (var-desc vs)) function-names)
      (push val fvalues)
      (push vs function-varstructs))))

(defun build-closure (desc)
  ;; Given a function descriptor return a form which builds the closure for the
  ;; function.
  `(setq ,(name-for-desc desc)
	 (make-closure
	   #',(name-for-function desc)
	   ,(function-arity desc))))

(defun build-needed-closures (varstructs)
  ;; Given a list of varstructs for functions, return a list of forms which
  ;; define the closures for the functions.
  (let ((needed-closures nil))
    (dolist (vs varstructs)
      (let ((desc (var-desc vs)))
	(when (not (function-all-uses-full-appl desc))
	  (push (build-closure desc) needed-closures))))
    needed-closures))

(defun is-value-value (val)
  (neq (node-kind val) 'mk-abstr))

(defun is-value-varstruct (vs)
  (not (and (eql (node-kind vs) 'mk-var)
	    (is-ml-function (var-desc vs)))))

(defun build-body (varstructs names body &optional prolog)
  (multiple-value-bind (matching-code internal-names)
      (build-matching-code varstructs names)
    (if (null internal-names)
	(if (null matching-code)
	    (if (null prolog)
		body
		`(progn ,@prolog ,body))
	    `(progn ,@prolog ,matching-code ,body))
	`(let ,internal-names
	   ,@prolog
	   ,matching-code
	   ,body))))

(defun tran-appn (fun args)
  ;; Performs the translation for an application.  A small complication arises
  ;; in that arguments must be evaluated left to right, but the runtime system
  ;; prefers to see them in the reverse order (to avoid the need for reversal of
  ;; lists at runtime).  Thus the need for reverse-args below.
  (labels ((tran-known-function (function closure arity args)
	     (let ((l (length args)))
	       (cond ((= l arity)
		      (gen-direct-call function args))
		     ((< l arity)
		      (gen-direct-closure closure args))
		     (t (gen-call
			  (gen-direct-call function (subseq args 0 arity))
			  (nthcdr arity args))))))
	   (gen-call (closure args)
	     (reverse-args args (prllambda (names) `(ap ,closure ,@names))))
	   (gen-direct-call (function args)
	     (reverse-args args (prllambda (names) `(,function ,@names))))
	   (gen-direct-closure (closure args)
	     (reverse-args args (prllambda (names) `(update-closure ,closure ,@names))))
	   (reverse-args (args expander)
	     (if (= (length args) 1)
		 (funcall expander args)
		 (let* ((names (mapcar #'(lambda (x) (gensym)) args))
			(bindings (mapcar #'(lambda (n a) `(,n ,a)) names args)))
		   `(let* ,bindings
		      ,(funcall expander (nreverse names))))))
	   (make-tail-recursive-call (desc args)
	     (setf (function-tail-recursion-happened desc) t)
	     `(progn
		,(dolists ((p (function-params desc)) (a (nreverse args)))
			  ((code-list nil))
			  `(psetq ,@code-list)
		   (when (neq p a) (push a code-list) (push p code-list)))
		(go ,(name-for-desc desc)))))
    (case (node-kind fun)
      (mk-var
       (let ((desc (var-desc fun)))
	 (cond ((is-function desc)
		(if (and *do-tail-recursion*
			 (member desc *functions-being-defined*)
			 (= (length args) (function-arity desc)))
		    (make-tail-recursive-call desc args)
		    (tran-known-function
		      (name-for-function desc)
		      (name-for-desc desc)
		      (function-arity desc)
		      args)))
	       ((is-isom desc) (car args))
	       (t (gen-call (name-for-desc desc) args)))))
      (mk-abstr
       (let* ((abstr (tre fun))
	      ;; The translation of an abstraction is of the form
	      ;;  (make-closure (function (lambda args body)) arity)
	      ;; We pick out the function and arity pieces.
	      (func (second abstr))
	      (arity (third abstr)))
	 (tran-known-function (second func) abstr arity args)))
      (otherwise
       (gen-call (tre fun) args)))))

(defun tran-function-value (f desc &optional recursive?)                        
  ;; Translate a named function.  Returns a function definition form acceptable
  ;; to flet or labels.  If recursive? is true, this function is recursive and
  ;; tail recursive calls will be optimized.
  (setf *function-was-defined* t)
  (let* ((params (abstr-params f))
	 (names (top-level-names-of-varstructs params))
	 (body (if recursive?
		   (progn
		     (setf (function-params desc) names)
		     (let ((*functions-being-defined*
			     (cons desc *functions-being-defined*)))
		       (tre (abstr-body f))))
		   (tre (abstr-body f)))))
    (if (and recursive? (function-tail-recursion-happened desc))
	`(,(name-for-desc desc) ,names
	  (prog nil ,(name-for-desc desc)
		(return ,(build-body params names body))))
	`(,(name-for-desc desc) ,names ,(build-body params names body)))))

(defun tran-abstr (body params)
  ;; Performs the translation for an abstraction.  Returns a form which
  ;; builds an ML closure.
  (setf *function-was-defined* t)
  (let ((names (top-level-names-of-varstructs params)))
    `(make-closure
      #'(lambda ,names
	  ,(build-body params names (tre body)))
       ,(length params))))

(defun tran-in (decl body)
  ;; Performs the translation for a local declaration.
  (funcall
    (case (node-kind decl)
      (mk-let #'tran-let)
      (mk-letrec #'tran-letrec)
      (mk-letref #'tran-letref))
    (decl-varstructs decl)
    (decl-values decl)
    body))

(defun tran-letrec (varstructs values body)
  ;; Performs the translation for a set of mutually recursively defined
  ;; functions. 
  (multiple-value-bind (names values varstructs)
      (process-function-declarations varstructs values)
    `(let ,names
       ;; The closure variables for these functions must be bound before
       ;; the functions are declared so that recursive references to
       ;; closures in the bodies of the functions have the right lexical scope.
       (labels ,(mapcar
		  (prllambda (val vs) (tran-function-value val (var-desc vs) t))
		  values varstructs)
	 ,@(build-needed-closures varstructs)
	 ,(tre body)))))

(defun tran-let (varstructs values body)
  ;; Performs the translation for a set of local value declarations.
  (if (not (some (prllambda (x) (eql (node-kind x) 'mk-abstr)) values))
      (tran-let-body varstructs values body)
      (multiple-value-bind (function-names function-values function-varstructs)
	  (process-function-declarations varstructs values)
	(let ((value-varstructs
		(delete-if-not #'is-value-varstruct varstructs))
	      (values
		(delete-if-not #'is-value-value values)))
	  (when (not (null values))
	    ;; If there are any values we rename the lisp functions.  Consider
	    ;; the following ml code:
	    ;;   let f = \x.body and v = f a in ...
	    ;; Our translation scheme produces code of the form
	    ;;   (flet ((f (x) translated body))
	    ;;     (let ((f (make-closure #'f (arity f)))
	    ;;           (v (f translated a)))))
	    ;;              ^^^^^^^^^^^^^^^^
	    ;; The indicated form is incorrect as the wrong f is being used.
	    ;; The renaming here solves the problem.  A more precise solution
	    ;; can be found at the cost of some complexity.  See the definition
	    ;; of find-conflicts below (commented out).
	    (dolist (vs function-varstructs)
	      (setf (function-fname (var-desc vs))
		    (gen-temp-name (name-for-desc (var-desc vs))))))
	  `(flet ,(mapcar
		    (prllambda (val vs) (tran-function-value val (var-desc vs)))
		    function-values function-varstructs)
	     ,(tran-let-body value-varstructs values body function-names
			     (build-needed-closures function-varstructs)))))))

(defun tran-let-body (varstructs values body &optional aux-names prolog)
  ;; Produces code which binds the names defined in the varstructs to
  ;; their appropriate values and evaluates body in that environment.
  ;; Aux-names should be a list of names which must be bound at the same
  ;; lexical level as the names in the varstructs.  Prolog should be a
  ;; list of forms which need to be evaluated after all the names at
  ;; this lexical level are bound.
  (let ((names (top-level-names-of-varstructs varstructs)))
    `(let ,(nconc
	     (without-tail-recursion
	       (mapcar (prllambda (name val) `(,name ,(tre val))) names values))
	     aux-names)
       ,(build-body varstructs names (tre body) prolog))))


(defun tran-letref (varstructs values body)
  ;; Performs the translation for a set of local reference declarations.
  ;; In this implementation, values and references are handled the same
  ;; way.
  (tran-let-body varstructs values body))

(defun tran-top-level-let (varstructs values)
  (multiple-value-bind (ignore function-values function-varstructs)
      (process-function-declarations varstructs values)
    (let ((value-varstructs
	    (delete-if-not #'is-value-varstruct varstructs))
	  (values
	    (delete-if-not #'is-value-value values)))
      (tran-top-level-decl
	value-varstructs values function-varstructs function-values))))

(defun tran-top-level-letrec (varstructs values)
  (tran-top-level-decl nil nil varstructs values))

(defun tran-top-level-letref (varstructs values)
  (tran-top-level-decl varstructs values nil nil))

(defun tran-top-level-decl (value-varstructs value-values
			    function-varstructs function-values)
  (let ((code-list nil))
    ;; Rename the descriptors.
    (let ((descriptors nil))
      (flet ((rename-and-collect-descriptors (vs)
	       (let ((desc (var-desc vs)))
		 (let ((name (gen-external-name (desc-id desc))))
		   (when (eql (desc-kind desc) 'FUNCTION)
		     (setf (function-fname desc) name)
		     (setf (desc-name desc) name)
		     ;; Build the global version of the descriptor to be
		     ;; returned. 
		     (setf desc
			   (make-ml-function
			     :id (desc-id desc)
			     :arity (function-arity desc))))
		   (setf (desc-name desc) name))
		 (push desc descriptors))))
	(dolist (v value-varstructs)
	  (walk-varstruct v #'rename-and-collect-descriptors))
	(dolist (v function-varstructs)
	  (walk-varstruct v #'rename-and-collect-descriptors)))
      (push `',descriptors code-list))
    ;; Process the functions.
    (dolists ((vs function-varstructs)
	      (fval function-values))
	     () ()
      (push (cons 'defun (tran-function-value fval (var-desc vs) t)) %compfns))
    ;; Process the values.
    (dolists ((vs value-varstructs)
	      (val value-values))
	     ((psetq-list nil)
	      ; (val-counter 0) ---not needed because of later commenting-out
             )
	     (when (not (null psetq-list))
	       (push `(psetq ,@psetq-list) code-list))
      (let* ((*function-was-defined* nil)
	     (valcode (without-tail-recursion (tre val))))
	#| ; see the note in tran.
	(when *function-was-defined*
	  (let ((val-func-name
		  (intern (format nil "%val~D" val-counter))))
	    (incf val-counter)
	    (push `(defun ,val-func-name () ,valcode) %compfns)
	    (setf valcode `(,val-func-name))))
        |#
	(push valcode psetq-list)
	(if (eql (node-kind vs) 'mk-var)
	    (push (name-for-desc (var-desc vs)) psetq-list)
	    (let ((name (gen-temp-name "value-")))
	      (push name psetq-list)
	      (push (build-matching-code (ncons vs) (ncons name)) code-list)))))
    `(progn ,@code-list)))
	   
;;; The following code isn't used any more but is left for reference.  It is what
;;; is referred to as "some complexity" in the comment in process-let.
;;;
;(defun find-conflicts (function-names values)
;  ;; Returns a list of those function-names which are fully applied in any of
;  ;; the value expressions.
;  (let ((in-contention-sym (gensym)))
;    (labels ((scan-exp (exp)
;	       (selectq (node-kind exp)
;		 ((mk-boolconst mk-intconst mk-termconst mk-tokconst mk-empty mk-var mk-fail)
;		  nil)
;		 (mk-failwith (scan-exp (failwith-exp exp)))
;		 (mk-dupl (scan-exp (pair-left exp)) (scan-exp (pair-right exp)))
;		 (mk-list (mapc #'scan-exp (ml-list-list exp)))
;		 (mk-appn
;		  (let ((fun (appn-fun exp)))
;		    (if (eql (node-kind fun) 'mk-var)
;			(let ((desc (var-desc fun)))
;			  (if (and (eql (desc-kind desc) 'FUNCTION)
;				   (get (desc-id desc) in-contention-sym)
;				   (= (length (appn-args exp)) (function-arity desc)))
;			      (setf (get (desc-id desc) 'has-conflict) t)))
;			(scan-exp fun)))
;		  (mapc #'scan-exp (appn-args exp)))
;		 (mk-abstr
;		  (let ((shadowed-vars (scan-varstructs (abstr-params exp))))
;		    #| Done implicitly by scan-varstructs |
;		    (dolist (v shadowed-vars) (setf (get v in-contention-sym) nil)) ||#
;		    (scan-exp (abstr-body exp))
;		    (dolist (v shadowed-vars) (setf (get v in-contention-sym) t))))
;		 (mk-assign (scan-exp (assign-value exp)))
;		 (mk-seq (mapc #'scan-exp (seq-for-effect exp)) (scan-exp (seq-value exp)))
;		 (mk-test
;		  (mapc (prllambda (arm) (scan-exp (arm-test arm)) (scan-exp (arm-exp arm)))
;			(test-conditional exp))
;		  (scan-exp (else-exp (test-else exp))))
;		 (mk-trap
;		  (scan-exp (trap-exp exp))
;		  (mapc (prllambda (arm) (scan-exp (arm-test arm)) (scan-exp (arm-exp arm)))
;			(trap-conditional exp))
;                 ;; The type system ensures that we don't have to worry about
;                 ;; the else-binding-id. 
;                 (scan-exp (else-exp (trap-else exp)))
;		 (mk-in
;		  (let ((varstructs (decl-vs-list (in-decl exp)))
;			(values (decl-val-list (in-decl exp)))
;			(body (in-body exp)))
;		    (selectq (node-kind (in-decl exp))
;		      ((mk-let mk-letref)
;		       (mapc #'scan-exp values)
;		       (let ((shadowed-vars (scan-varstructs varstructs)))
;			 #| Done implicitly by scan-varstructs |
;			 (dolist (v shadowed-vars) (setf (get v in-contention-sym) nil)) ||#
;			 (scan-exp body)
;			 (dolist (v shadowed-vars) (setf (get v in-contention-sym) t))))
;		      (mk-letrec
;		       (let ((shadowed-vars (scan-varstructs varstructs)))
;			 #| Done implicitly by scan-varstructs |
;			 (dolist (v shadowed-vars) (setf (get v in-contention-sym) nil)) ||#
;			 (mapc #'scan-exp values)
;			 (scan-exp body)
;			 (dolist (v shadowed-vars) (setf (get v in-contention-sym) t)))))))))
;	     (scan-varstructs (varstructs)
;	       (let ((shadowed nil))
;		 (labels ((scan-varstruct (vs)
;			    (selectq (node-kind vs)
;			      (mk-var
;			       (when (get (desc-id (var-desc vs)) in-contention-sym)
;				 (setf (get (desc-id (var-desc vs)) in-contention-sym) nil)
;				 (push (desc-id (var-desc vs)) shadowed)))
;			      (mk-dupl
;			       (scan-varstruct (pair-left vs))
;			       (scan-varstruct (pair-right vs)))
;			      (mk-binop
;			       (scan-varstruct (binop-left vs))
;			       (scan-varstruct (binop-right vs)))
;			      (mk-list
;			       (mapc #'scan-varstruct (ml-list-list vs))))))
;		   (mapc #'scan-varstruct varstructs)
;		   shadowed))))
;      ;;; The body of find-conflicts.
;      (mapc (prllambda (name)
;	       (setf (get name in-contention-sym) nil)
;	       (setf (get name 'had-conflict) nil))
;	    function-names)
;      (mapc #'scan-exp values)
;      ;; Remove the in-contention-sym properties to keep property lists small.
;      (mapc (prllambda (name) (remprop name in-contention-sym)) function-names)
;      (let ((conflicting-names nil))
;	(mapc (prllambda (name) (when (get name 'has-conflict) (push name conflicting-names)))
;	      function-names)
;	conflicting-names))))

(defun tran-assign (varstruct value)
  ;; Performs the translation for an assignment.
  (without-tail-recursion
    (if (eql (node-kind varstruct) 'mk-var)
	`(setq ,(name-for-desc (var-desc varstruct)) ,(tre value))
	(let ((matching-code (build-matching-code (ncons '%assign-value) (ncons varstruct))))
	  `(let  ((%assign-value ,(tre value)))
	     ;; The following prog1 must be used as the matching code
	     ;; changes the value associated with %assign-value.
	     (prog1 %assign-value ,matching-code))))))

(defun general-test-translator (conditional test-translator
			        else else-value-translator default-exp)
  ;; Translates a general conditional.  Conditional is a list of
  ;; arms.  Else is an else expression.  The behavior of this function is
  ;; specialized by the test-translator and else-value-translator arguments,
  ;; which are both expected to be functions.  Test-translator is invoked to
  ;; translate the test of each arm of the conditional and else-value-translator
  ;; is invoked to translate the default value of else.  The values returned are
  ;; the cond form and an indication of whether any of the arms or the else
  ;; expression required iteration.  If iteration is required the caller is
  ;; expected to wrap the cond form with a tagbody defining the tag '%again.
  ;; Default-exp is the default value of the cond body if no explicit
  ;; else clause is given.
  #+symbolics
  (declare (sys:downward-funarg test-translator else-value-translator)
	   (values cond-code tag-needed))

  (let ((code-list nil)
	(tag-needed nil))
    (labels ((tran-arm (arm)
	       (let ((arm-code nil))
		 (if (eql (node-kind arm) 'ONCE)
		     (push (tre (arm-exp arm)) arm-code)
		     (progn
		       (push '(go %again) arm-code)
		       (setq tag-needed t)
		       (without-tail-recursion
			 (push (tre (arm-exp arm)) arm-code))))
		 (without-tail-recursion
		   (push (funcall test-translator (arm-test arm)) arm-code))
		 arm-code))
	     (tran-else (else)
	       (let ((else-code nil))
		 (case (node-kind else)
		   (ONCE
		     (push (funcall else-value-translator (else-exp else)) else-code))
		   (ITER
		     (progn
		       (push '(go %again) else-code)
		       (setq tag-needed t)
		       (without-tail-recursion
			 (push (funcall else-value-translator (else-exp else)) else-code))))
		   (EMPTY
		     (push default-exp else-code)))
		 (push 't else-code)
		 else-code)))
      (dolist (arm conditional)
	(push (tran-arm arm) code-list))
      (push (tran-else else) code-list)
      (values `(cond ,@(nreverse code-list)) tag-needed))))

(defun tran-test (conditional else)
  ;; Translates a conditinal.
  (multiple-value-bind (code tag-needed)
      (general-test-translator conditional #'tre else #'tre nil)
    (if tag-needed
	`(block nil (tagbody %again (return ,code)))
	code)))

(defun tran-trap (exp conditional else binding-id)
  ;; Translates a failure trapping form.
    (flet ((tran-list-membership (exp)
	     `(member %trap-value ,(tre exp)))
	   (tran-else-value (exp)
	     ;; Given the abstract syntax for an expression of an else
	     ;; expression produces the code which evaluates exp in the
	     ;; appropriate environment.
	     (if binding-id
		 `(let ((,binding-id %trap-value)) ,(tre exp))
		 (tre exp))))
      (multiple-value-bind (code tag-needed)
	  (general-test-translator
	    conditional #'tran-list-membership
	    else #'tran-else-value
	    '(breakout evaluation %trap-value))
	(without-tail-recursion
	  (setf code `(trap ,(tre exp) ,code)))
	(if tag-needed
	    `(block nil (tagbody %again (return ,code)))
	    code))))

(defmacro trap (code-for-exp code-for-trap-handler)
  `(multiple-value-bind (%trap-value %was-thrown)
       (catch 'evaluation ,code-for-exp)
     (if (neq %was-thrown %breakout-tag)
	 %trap-value
	 ,code-for-trap-handler)))
