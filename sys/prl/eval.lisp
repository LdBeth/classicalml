;;; -*- Package: Nuprl; Syntax: Common-lisp; Base: 10. -*-


;;;************************************************************************
;;;                                                                       *
;;;                Nuprl Proof Development System                         *
;;;                ------------------------------                         *
;;;                                                                       *
;;;   Developed by the Nuprl group, Department of Computer Science,       *
;;;   Cornell University, Ithaca NY.  See the release notes for a list    *
;;;   of the members of the group.                                        *
;;;                                                                       *
;;;   Permission is granted to use and modify Nuprl provided this notice  *
;;;   is retained in derived works.                                       *
;;;                                                                       *
;;;                                                                       *
;;;************************************************************************



(in-package "NUPRL")


;--      EVAL
;-- 
;-- The nuprl evaluator.
;-- 

;-- To handle funargs we have to close up terms over their free vars.
(deftuple eval-closure
    term                        ;-- A term
    env                         ;-- Contains values of free vars of term
)

(constant eval-empty-env nil)   ;-- environments are lists of dotted pairs


(defun eval-init ()
    (for
        (i in '( 
                 (MINUS            eval-minus)
                 (ADD              eval-binary)
                 (SUB              eval-binary)
                 (MUL              eval-binary)
                 (DIV              eval-binary)
                 (MOD              eval-binary)
                 (ATOMEQ           eval-atomeq)
                 (INTEQ            eval-inteq)
                 (INTLESS          eval-intless)
                 (IND              eval-ind)
                 (LIST-IND         eval-list-ind)
		 (REC-IND          eval-rec-ind)
                 (DECIDE           eval-decide)
                 (SPREAD           eval-spread)
                 (APPLY            eval-apply)
                 (VAR              eval-var)
		 (REC-IND          eval-rec-ind)
		 (DOM              eval-dom)
		 (APPLY-PARTIAL    eval-apply-partial)
                 (TERM-OF-THEOREM  eval-term-of-theorem)
		 (SIMPLE-REC-IND   eval-simple-rec-ind)
                 (INCOMPLETE       eval-incomplete)
               )
        )
        (do (setf (get (car i) 'prl-evaluator) (cadr i)))
    )
    (for (i in
             '(UNIVERSE VOID ANY ATOM TOKEN INT POS-NUMBER
               LIST NIL CONS UNION INL INR PRODUCT PAIR
               FUNCTION LAMBDA QUOTIENT SET FIX OBJECT
               EQUAL AXIOM LESS BOUND-ID-TERM SIMPLE-REC)
         )
        (do (setf (get i 'prl-evaluator) 'null-evaluation))
    )
    (for
        (i in '( (ADD    prl-add)
                 (SUB    prl-sub)
                 (MUL    prl-mul)
                 (DIV    prl-div)
                 (MOD    prl-mod)
               )
        )
        (do (setf (get (car i) 'numeric-evaluator) (cadr i)))
    )
    (ev-subst-init)
    nil
)

;;; If *top-level-mode-p* is T (default is T), then the evaluator
;;; (iterated-eval) runs in the usual way (as documented in the book,
;;; except that evaluation proceeds recursively on immediate subterms of
;;; canonical terms whose outermost constructor never has binding
;;; occurrences --- the function eval works in the original way).
;;; Otherwise, it runs in a way which accomodates terms with free
;;; variables.  Specifically, there are two differences.  First, in the
;;; evaluation of a non-canonical term t, if the principal argument does
;;; not evaluate to the appropriate canonical form, then, instead of an
;;; error being signalled, t is returned.  Evaluating a term_of term
;;; where the named term does not exist still causes an error.  Second,
;;; the evaluator is recursively called on the subterms of *any*
;;; evaluated term whose outermost term constructor does not have
;;; binding variables (i.e., whose name is on the list
;;; terms-with-no-binding-ids).  An implementation note: a top-level
;;; closure that cannot be further evaluated must be processed using the
;;; usual substitution function, instead of the one the top-level mode
;;; uses which takes advantage of the fact that capture cannot occur.
(defvar *top-level-mode-p* t)

;;; If *top-level-mode-p* is NIL, then some term_of terms are expanded
;;; during evaluation and some are not.  Specifically, if
;;; *exceptions-are-constant-p* is T, then term_of(name) does *not* get
;;; expanded exactly when name is on the list *excepted-thms*; if it is
;;; NIL, then term_of(name) gets expanded exactly when name is on the
;;; list *excepted-thms*.
(defvar *excepted-thms* ())
(defvar *exceptions-are-constant-p* t)

;;; For memoizing the lookups of extractions from theorems.
(defvar *ext-memos* nil)
(defun initialize-ext-memos () (setf *ext-memos* nil))

;--
;-- eval-term (term:term) : term
;-- 
;-- Evaluates a term and returns the resulting term.
;--
(defun eval-term (term)
    (initialize-ext-memos)
    (catch 'process-err
	   (cond (*top-level-mode-p*
		  (subst-for-free-vars (teval term eval-empty-env)))
		 (t
		  (generalized-subst-for-free-vars (teval term eval-empty-env))))))



(defun iterated-eval (term env)
  (initialize-ext-memos)
  (let* ((closure (teval term env))
	 (term (term-of-eval-closure closure))
	 (k (kind-of-term term)))
    (if (or (member k terms-with-no-binding-ids)
	    (and (member k '(PRODUCT FUNCTION SET QUOTIENT))
		 (null (third term))))
	(map-on-subterms
	  #'(lambda (x) (iterated-eval x (env-of-eval-closure closure)))
	  term)
	(let ((subd-term
		(if *top-level-mode-p*
		    (subst-for-free-vars closure)
		    (generalized-subst-for-free-vars closure))))
	  (if (member k '(PRODUCT FUNCTION SET QUOTIENT))
	      ;; continue evaluation on left type.
	      (let ((x (copy-list subd-term)))
		(setf (fourth x) (iterated-eval (fourth subd-term) eval-empty-env))
		(setf (ttree-of-term x) nil)
		x)
	      subd-term))))) 


;(defun iterated-eval (term env)
;    (let* ((closure (teval term env)))
;	(cond ((member (kind-of-term (term-of-eval-closure closure)) terms-with-no-binding-ids)
;	       (map-on-subterms
;		 #'(lambda (x) (iterated-eval x (env-of-eval-closure closure)))
;		 (term-of-eval-closure closure)))
;	      (*top-level-mode-p* (subst-for-free-vars closure))
;	      (t (generalized-subst-for-free-vars closure)))))


;-- 
;-- teval (term:term, env:environment) : eval-closure
;-- 
;-- Evaluates a term in an environment, and returns the eval-closure of the
;-- resulting term over its free vars.
;-- 
(defun teval (term env)
    (funcall
        (evaluation-fcn (kind-of-term term))
        term
        env
    )
)

;-- 
;-- evaluation-fcn (kind: term-type) : function
;-- 
;-- Given the kind of a term, returns the function which evaluates that kind
;-- of term.
;-- 
(defun evaluation-fcn (kind)
    (Plet (fcn (get kind 'prl-evaluator))
        (Pif fcn --> fcn
         || t   --> (eval-err "Bad term kind " kind)
         fi)
    )
)

;-- 
;-- null-evaluation (term:term, env) : eval-closure
;-- 
;-- The "identity" evaluation.
;--
(defun null-evaluation (term env)
    (eval-closure term env)
)

;-- 
;-- eval-apply (term : apply-term, env) : eval-closure
;-- 
;-- Evaluates an application.
;-- 
(defun eval-apply (term env)
    (Plet (cfunc (teval (function-of-apply-term term) env))
        (Plet (func (term-of-eval-closure cfunc))
            (Pif (is-lambda func) -->
                (teval
                    (term-of-lambda-term func)
                    (eval-update
                        (bound-id-of-lambda-term func)
                        (arg-of-apply-term term)
                        env
                        (env-of-eval-closure cfunc)
                    )
                )
             || *top-level-mode-p* -->
                (eval-err "Expecting lambda term but got " (kind-of-term func))
	     || t -->
	        (eval-closure term env)
             fi)
        )
    )
)

;-- 
;-- eval-spread (term : spread-term, env) : eval-closure
;-- 
;-- Evaluates a spread term.
;-- 
(defun eval-spread (term env)
    (Plet (cpair (teval (value-of-spread-term term) env))
        (Plet (val (term-of-eval-closure cpair))
            (Pif (is-pair val) -->
                (teval
                    (term-of-bound-id-term
                        (term-of-spread-term term)
                    )
                    (update-for-spread
                        (bound-ids-of-bound-id-term
                            (term-of-spread-term term)
                        )
                        (leftterm-of-pair-term val)
                        (rightterm-of-pair-term val)
                        (env-of-eval-closure cpair)
                        env
                    )
                )
             || *top-level-mode-p* -->
                (eval-err "Expecting pair term but got " (kind-of-term val))
	     || t -->
	        (eval-closure term env)
	     fi)
        )
    )
)


(defun update-for-spread (ids leftterm rightterm term-env env)
    (eval-update
        (first-bound-id ids)
        leftterm
        term-env
        (eval-update
            (second-bound-id ids)
            rightterm
            term-env
            env
        )
    )
)

;-- 
;-- eval-decide (term, env) : eval-closure
;-- 
;-- Evaluate a decide term.
;-- 
(defun eval-decide (term env)
    (Plet (cunion (teval (value-of-decide-term term) env))
        (Plet (union (term-of-eval-closure cunion))
            (Pif (is-injection union) -->
                (eval-arm-of-decide
                    (term-of-injection-term union)
                    (env-of-eval-closure cunion)
                    (Pif (eql (kind-of-term union) 'INL) -->
                        (leftterm-of-decide-term term)
                     || t -->
                        (rightterm-of-decide-term term)
                     fi)
                    env
                )
             || *top-level-mode-p* -->
                (eval-err "Expecting injection term but got " (kind-of-term union))
	     || t -->
	        (eval-closure term env)
             fi)
        )
    )
)

(defun eval-arm-of-decide (inj-term inj-env term env)
    (Plet (
             ids   (bound-ids-of-bound-id-term term)
             term  (term-of-bound-id-term term)
         )
        (teval
            term
            (eval-update
                (first-bound-id ids)
                inj-term
                inj-env
                env
            )
        )
    )
)
		
;-- 
;-- eval-ind (term : ind-term, env) : eval-closure
;-- 
;-- Evaluates ind terms.
;-- 
(defun eval-ind (term env)
    (Plet (cint (teval (value-of-ind-term term) env))
        (Pif (is-number (term-of-eval-closure cint)) -->
            (Plet (bound (val-of (term-of-eval-closure cint)))
                (Pif (zerop bound) -->
		    (teval (baseterm-of-ind-term term) env)
		 || t -->
		    (do-ind
		        (term-of-eval-closure cint)
		    	(Pif (< bound 0) -->  1
			 || t               --> -1
			 fi)
			(Pif (< bound 0) -->
			    (downterm-of-ind-term term)
			 || t -->
			    (upterm-of-ind-term term)
			 fi)
			term
			env
		    )
		 fi)
            )
         || *top-level-mode-p* -->
            (eval-err
                "Expecting int term but got "
                (kind-of-term (term-of-eval-closure cint))
            )
	 || t -->
            (eval-closure term env)
         fi)
    )
)

(defun do-ind (number increment subterm term env)
    (Plet (var-id    (first-bound-id (bound-ids-of-bound-id-term subterm))
	  ind-id    (second-bound-id (bound-ids-of-bound-id-term subterm))
	  ind-term  (term-of-bound-id-term subterm)
	  newterm   nil
	 )
	(<- newterm (copy-list term))
	(<- (Ttree-of-term newterm) nil)
	(<- (value-of-ind-term newterm) (mk-int-term (+ (val-of number) increment)))
	(teval
	    ind-term
	    (eval-update
	        var-id
		number
		eval-empty-env
		(eval-update
		    ind-id
		    newterm
		    env
		    env
		)
	    )
	)
    )
)

(defun eval-atomeq (term env)
    (Plet (leftterm-val  (term-of-eval-closure
                            (teval (leftterm-of-decision-term term) env)
                        )
          rightterm-val (term-of-eval-closure
                            (teval (rightterm-of-decision-term term) env)
                        )
          if-term   (if-term-of-decision-term term)
          else-term (else-term-of-decision-term term)
         )

        (Pif (not (eql (kind-of-term leftterm-val) 'TOKEN)) -->
            (cond (*top-level-mode-p*
		   (eval-err
		     "Expecting an Atom as the first term of an ATOM_EQ term but got"
		     (kind-of-term leftterm-val)))
		  (t (eval-closure term env)))

         || (not (eql (kind-of-term rightterm-val) 'TOKEN)) -->
            (cond (*top-level-mode-p*
		   (eval-err
		     "Expecting an Atom as the second term of an ATOM_EQ term but got"
		     (kind-of-term rightterm-val)))
		  (t (eval-closure term env)))

         || (equal (atom-of-token-term leftterm-val)
                   (atom-of-token-term rightterm-val)
            ) -->
            (teval if-term env)

         || t -->
            (teval else-term env)

         fi)

    )
)


(defun eval-inteq (term env)
    (Plet (leftterm-val  (term-of-eval-closure
                            (teval (leftterm-of-decision-term term) env)
                        )
          rightterm-val (term-of-eval-closure
                            (teval (rightterm-of-decision-term term) env)
                        )
          if-term   (if-term-of-decision-term term)
          else-term (else-term-of-decision-term term)
         )

        (Pif (not (is-number leftterm-val)) -->
            (cond (*top-level-mode-p*
		   (eval-err
		     "Expecting an Integer as the first term of an INT_EQ term but got"
		     (kind-of-term leftterm-val)))
		  (t (eval-closure term env)))

         || (not (is-number rightterm-val)) -->
            (cond (*top-level-mode-p*
		   (eval-err
		     "Expecting an Integer as the second term of an INT_EQ term but got"
		     (kind-of-term rightterm-val)))
		  (t (eval-closure term env)))

         || (equal (val-of leftterm-val)
                   (val-of rightterm-val)
            ) -->
            (teval if-term env)

         || t -->
            (teval else-term env)

         fi)

    )
)


(defun eval-intless (term env)
    (Plet (leftterm-val  (term-of-eval-closure
                            (teval (leftterm-of-decision-term term) env)
                        )
          rightterm-val (term-of-eval-closure
                            (teval (rightterm-of-decision-term term) env)
                        )
          if-term   (if-term-of-decision-term term)
          else-term (else-term-of-decision-term term)
         )

        (Pif (not (is-number leftterm-val)) -->
            (cond (*top-level-mode-p*
		   (eval-err
		     "Expecting an Integer as the first term of a LESS term but got"
		     (kind-of-term leftterm-val)))
		  (t (eval-closure term env)))

         || (not (is-number rightterm-val)) -->
            (cond (*top-level-mode-p*
		   (eval-err
		     "Expecting an Integer as the second term of a LESS term but got"
		     (kind-of-term rightterm-val)))
		  (t (eval-closure term env)))

         || (< (val-of leftterm-val)
                   (val-of rightterm-val)
            ) -->
            (teval if-term env)

         || t -->
            (teval else-term env)

         fi)

    )
)


(defun eval-minus (term env)
    (Plet (cval (teval (term-of-minus-term term) env))
        (Plet (val (term-of-eval-closure cval))
            (Pif (eql (kind-of-term val) 'MINUS) -->
                (eval-closure (term-of-minus-term val)
                              (env-of-eval-closure cval)
                )
             || (eql (kind-of-term val) 'POS-NUMBER) -->
                (eval-closure (minus-term 'MINUS nil val)
                              (env-of-eval-closure cval)
                )
             || *top-level-mode-p* -->
                (eval-err
                    "Expecting signed constant but got "
                    (kind-of-term val)
                )
	     || t -->
	        (eval-closure term env)
             fi)
        )
    )
)

(defun eval-binary (term env)
    (Plet (
             cleftval  (teval (leftterm-of-binary-term term) env)
             crightval (teval (rightterm-of-binary-term term) env)
         )
        (Plet (
                 leftval  (term-of-eval-closure cleftval)
                 rightval (term-of-eval-closure crightval)
             )
            (Pif (and (is-number leftval) (is-number rightval)) -->
                (eval-closure
                    (mk-int-term
                        (funcall
                            (get (kind-of-term term) 'numeric-evaluator)
                            (val-of leftval)
                            (val-of rightval)
                        )
                    )
                    env
                )
             || *top-level-mode-p* -->
                (eval-err "Non-numeric argument to binary term" nil)

	     || t -->
	        (eval-closure term env)
             fi)
        )
    )
)
                
;-- eval-list-ind (term : list-ind-term, env) : eval-closure
;-- 
;-- Evaluates list induction terms.
;-- 
(defun eval-list-ind (term env)
    (Plet (clist (teval (value-of-list-ind-term term) env))
        (Plet (list (term-of-eval-closure clist))
            (Pif (is-list list) -->
                (Pif (is-nil list) -->
		    (teval (baseterm-of-list-ind-term term) env)
		 || t -->
		    (do-list-ind
		        list
			(env-of-eval-closure clist)
			(upterm-of-list-ind-term term)
			term
			env
		    )
		 fi)
             || *top-level-mode-p* -->
                (eval-err "Expecting cons term but got " (kind-of-term list))
	     || t -->
	        (eval-closure term env)
             fi)
        )
    )
)


(defun do-list-ind (list list-env ind-term term env)
  (let* ((hd-id (first-bound-id (bound-ids-of-bound-id-term ind-term)))
	 (tl-id (second-bound-id (bound-ids-of-bound-id-term ind-term)))
	 (ind-id (third-bound-id (bound-ids-of-bound-id-term ind-term)))
	 (new-id (genvar))	 
	 (new-var (var-term 'VAR nil new-id))
	 (new-term (let ((x (copy-list term)))
		    (setf (Ttree-of-term x) nil
			  (value-of-list-ind-term x) new-var)
		    x))
	 (new-env (eval-update new-id (tail-of-cons-term list) list-env env)))
	 
    (teval
     (term-of-bound-id-term ind-term)
     (eval-update
      ind-id
      new-term
      new-env
      (eval-update
       hd-id
       (head-of-cons-term list)
       list-env
       (eval-update tl-id new-var new-env env))))))


;--
;-- rec-ind(t;h1,z1.d1; ...;hn,zn.dn;hi) => 
;--   di[t/zi,\z1.rec-ind(z1;...;h1)/h1, ... \zn.rec-ind(zn;...;hn)/hn]
;--
(defun eval-rec-ind (term env)
    (Plet (eterm     (term-of-rec-ind-term term)
	  id        (id-of-rec-ind-term term)
	  list-term (bound-id-list-term-of-rec-ind-term term)
	  selected-term nil
	  clos      nil
	 )
	 (<- clos (teval eterm env))
	 (<- selected-term
	     (nth
	       (position id (bound-ids-of-bound-id-list-term list-term))
	       (term-list-of-bound-id-list-term list-term)
	     )
	 )
	 (teval
	   (term-of-bound-id-term selected-term)
	   (rec-ind-update
	     (bound-ids-of-bound-id-list-term list-term)
	     (for (i in (term-list-of-bound-id-list-term list-term))
		  (save (bound-ids-of-bound-id-term i)))
	     list-term	  
	     (eval-update
	       (car (bound-ids-of-bound-id-term selected-term))
	       (term-of-eval-closure clos)
	       (env-of-eval-closure clos)
	       env
	     )
	   )
	 )
    )
)

(defun rec-ind-update (id-list1 id-list2 list-term env)
    (Pif (null id-list1) -->
	env
     || t -->
        (rec-ind-update
	  (cdr id-list1)
	  (cdr id-list2)
	  list-term
	  (eval-update
	    (car id-list1)
	    (lambda-term
	      'Lambda
	      nil
	      (car id-list2)
	      (rec-ind-term
	        'REC-IND
	        nil
	        (var-term 'VAR nil (car id-list2))
	        list-term
	        (car id-list1)
	      )
	    )
	    env
	    env
	  )
	)
     fi)
)

(defun eval-apply-partial(term env)
    (Plet (fterm         (function-of-apply-partial-term term)
	  arg           (arg-of-apply-partial-term term)
	  id            nil
	  list-term     nil
	  selected-term nil
	  clos          nil
	 )
	 (<- clos (teval fterm env))
	 (Pif (eql (kind-of-term (term-of-eval-closure clos)) 'FIX) -->
	     (<- id (id-of-fix-term (term-of-eval-closure clos)))
	     (<- list-term (bound-id-list-term-of-fix-term (term-of-eval-closure clos)))
	     (<- selected-term
	         (nth
	           (position id (bound-ids-of-bound-id-list-term list-term))
	           (term-list-of-bound-id-list-term list-term)
	         )
	     )
	     (teval
	       (term-of-bound-id-term selected-term)
	       (apply-partial-update
	         (bound-ids-of-bound-id-list-term list-term)
	         list-term	  
	         (eval-update
	           (car (bound-ids-of-bound-id-term selected-term))
	           arg
	           env
	           (env-of-eval-closure env)
	         )
	       )
	     )
	  || *top-level-mode-p* --> (eval-err
		    "Expecting fix term but got " (kind-of-term (term-of-eval-closure clos))) 
	  || t -->
	     (eval-closure term env)
	  fi)
    )
)

(defun apply-partial-update (id-list1  list-term env)
    (Pif (null id-list1) -->
	env
     || t -->
        (apply-partial-update
	  (cdr id-list1)
	  list-term
	  (eval-update
	    (car id-list1)
	      (fix-term
	        'FIX
	        nil
	        list-term
	        (car id-list1)
	      )
	    env
	    env
	  )
	)
     fi)
)

;;; rec-ind(e;h,z.d) => 
;;;   d [ e / z , 
;;;       \z.rec_ind(z;h,z.d) / h ]
(defun eval-simple-rec-ind (term env)
    (let* ((e (value-of-simple-rec-ind-term term))
	   (ids (bound-ids-of-bound-id-term (term-of-simple-rec-ind-term term)))
	   (ind-term (term-of-bound-id-term (term-of-simple-rec-ind-term term)))
	   (h (first ids))
	   (z (second ids))
	   (ind-fcn (lambda-term
		      'LAMBDA nil
		      z
		      (simple-rec-ind-term
			'SIMPLE-REC-IND
			nil
			(var-term 'VAR nil z)
			(term-of-simple-rec-ind-term term)))))
      (teval
        ind-term
	(eval-update
	  z
	  e
	  env
	  (eval-update h ind-fcn env env)))))







	    
;-- eval-var (term : var-term, env) : eval-closure
;-- 
;-- evaluates a variable reference
;-- 
(defun eval-var (term env)
    (let* ((x (eval-lookup (id-of-var-term term) env)))
      (or x (eval-closure term eval-empty-env))))



(defun theorem-ext (name)
  (let ((memo (cdr (assoc name *ext-memos*))))
    (unless (or memo
		(and (lib-member name)
		     (eql 'THM
			 (sel (object (library-object name))
			      kind))))
      (eval-err "term_of argument is not the name of a theorem: "
		name))
    (or memo
	(let ((res (evaluable-term-of-theorem name)))
	  (push (cons name res) *ext-memos*)
	  res))))

(defun eval-term-of-theorem (term env)
  (declare (ignore env))
  (let* ((name (name-of-term-of-theorem-term term))
	 (thm-term (theorem-ext name)))
    (Pif thm-term -->
	 (cond ((or *top-level-mode-p*
		    (and *exceptions-are-constant-p*
			 (not (member name *excepted-thms*)))
		    (and (not *exceptions-are-constant-p*)
			 (member name *excepted-thms*)))
		(teval thm-term eval-empty-env))
	       (t
		(eval-closure term eval-empty-env)))
         || t -->
	 (eval-err
	   "Bad theorem in term-of-theorem term: "
	   (name-of-term-of-theorem-term term))
         fi)
    )
  )


;-- eval-term-of-theorem (term: term, env) : eval-closure
;-- 
;(defun eval-term-of-theorem (term env)
;  (declare (ignore env))
;  (cond
;    ((or
;       (not (lib-member (name-of-term-of-theorem-term term)))
;       (not (eql 'THM
;		(sel (object (library-object (name-of-term-of-theorem-term term)))
;		     kind))))
;     (eval-err
;       "term_of argument is not the name of a theorem: "
;       (name-of-term-of-theorem-term term))))
;  (let* ((name (name-of-term-of-theorem-term term))
;	 (thm-term (evaluable-term-of-theorem name)))
;    (Pif thm-term -->
;	 (cond ((or *top-level-mode-p*
;		    (and *exceptions-are-constant-p*
;			 (not (member name *excepted-thms*)))
;		    (and (not *exceptions-are-constant-p*)
;			 (member name *excepted-thms*)))
;		(teval thm-term eval-empty-env))
;	       (t
;		(eval-closure term eval-empty-env)))
;         || t -->
;	 (eval-err
;	   "Bad theorem in term-of-theorem term: "
;	   (name-of-term-of-theorem-term term))
;         fi)
;    )
;  )

(defun eval-incomplete (term env)
  (declare (ignore term env))
  (eval-err "Attempt to evaluate an incomplete term" nil))

;-- Term type recognizers

(defun is-lambda (term)
    (eql (kind-of-term term) 'LAMBDA)
)

(defun is-pair (term)
    (eql (kind-of-term term) 'PAIR)
)

(defun is-injection (term)
    (or
        (eql (kind-of-term term) 'INL)
        (eql (kind-of-term term) 'INR)
    )
)

(defun is-list (term)
    (or (is-nil term) (is-cons term))
)

(defun is-nil (term)
    (eql (kind-of-term term) 'NIL)
)

(defun is-cons (term)
    (eql (kind-of-term term) 'CONS)
)

(defun is-number (term)
    (or
        (eql (kind-of-term term) 'POS-NUMBER)
        (and
            (eql (kind-of-term term) 'MINUS)
            (eql (kind-of-term (term-of-minus-term term)) 'POS-NUMBER)
        )
    )
)

;-- Functions for integer terms

(defun val-of (term)
    (Pif (eql (kind-of-term term) 'POS-NUMBER) -->
        (number-of-pos-number-term term)
     || t -->
        (*
            -1
            (number-of-pos-number-term
                (term-of-minus-term term)
            )
        )
     fi)
)

(defun mk-int-term (val)
    (Pif (< val 0) -->
        (minus-term
            'MINUS nil
            (mk-int-term (* -1 val))
        )
     || t -->
        (pos-number-term 'POS-NUMBER nil val)
     fi)
)

(defun prl-add (x y)
    (+ x y)
)

(defun prl-sub (x y)
    (- x y)
)
                            
(defun prl-mul (x y)
    (* x y)
)

(defun prl-div (x y)
    (Pif (zerop y) --> 0
     || t --> (truncate x y)
     fi)
)

(defun prl-mod (x y)
  (if (zerop y) 
      0
      (abs (rem x y))))

(defun first-bound-id (idlist) (car idlist))
(defun second-bound-id (idlist) (cadr idlist))
(defun third-bound-id (idlist) (caddr idlist))


;-- The environment handling functions.  An environment is a mapping from
;-- ids to eval-closures.  They are written to implement call-by-need.

;-- eval-update (id term term-env env) : environment
;-- 
;-- Returns an environment the same as env, except on identifier id, where
;-- it returns the value of term evaluated in the environment term-env.
;-- 
(defun eval-update (id term term-env env)
    (cons
        (cons
            id
            (cons nil (cons term term-env))
        )
        env
    )
)

;-- eval-lookup (id env) : eval-closure
;-- 
;-- Applies the environment env to the identifier id.
;-- 
(defun eval-lookup (id env)
    (Plet (val (assoc id env))
        (Pif val -->
            (Plet (value (cdr val))
                (Pif (null (car value)) -->
                    (setf (car value) t)
                    (setf (cdr value)
			  (cons (teval (cadr value) (cddr value))
				(cdr value)))
                 fi)
                (cadr value)
            )
         || *top-level-mode-p* -->
            (eval-err "Unbound variable " id)
	 || t -->
	    nil
         fi)
    )
)

#|
(defun eval-lookup (id env)
    (Plet (val (assoc id env))
        (Pif val -->
            (Plet (value (cdr val))
                (Pif (null (car value)) -->
                    (<- (car value) t)
                    (<- (cdr value) (teval (cadr value) (cddr value)))
                 fi)
                (cdr value)
            )
         || *top-level-mode-p* -->
            (eval-err "Unbound variable " id)
	 || t -->
	    nil
         fi)
    )
)
|#

;-- eval-lookup-quoted (id env) : eval-closure
;-- 
;-- Applies the environment env to the identifier id, leaving any unevaluated args
;-- unevaluated.
;-- 
(defun eval-lookup-quoted (id env)
    (Plet (val (assoc id env))
        (Pif val -->
            (Plet (value (cdr val))
                (Pif (null (car value)) -->
		    (eval-closure (cadr value) (cddr value))
		 || t -->
		    (eval-closure (caddr value) (cdddr value))
                 fi)
            )
         || *top-level-mode-p* -->
            (eval-err "Unbound variable " id)
	 || t -->
	    nil
         fi)
    )
)

#|
(defun eval-lookup-quoted (id env)
    (Plet (val (assoc id env))
        (Pif val -->
            (Plet (value (cdr val))
                (Pif (null (car value)) -->
		    (eval-closure (cadr value) (cddr value))
		 || t -->
		    (cdr value)
                 fi)
            )
         || *top-level-mode-p* -->
            (eval-err "Unbound variable " id)
	 || t -->
	    nil
         fi)
    )
)
|#

(defun eval-err (msg1 msg2)
    (throw 'process-err
           (list 'ERR
                 (implode
                     (append '#.(istring "Error in evaluation: ")
                         (istring msg1)
                         (istring msg2))))))


(global substitution-happened$)  ;-- this global variable is set to nil when
                                 ;-- substitution is begun on a term.  When
                                 ;-- a variable is found in the term that is
                                 ;-- replaced by a value in the environment,
                                 ;-- this variable is set to t.

(defun ev-subst-init ()
    (for
        (i in '( (UNIVERSE      null-substitution)
                 (VOID          null-substitution)
                 (ANY           subst-any)
                 (ATOM          null-substitution)
                 (TOKEN         null-substitution)
                 (INT           null-substitution)
                 (OBJECT        null-substitution)
                 (POS-NUMBER    null-substitution)
                 (MINUS         subst-minus)
                 (ADD           subst-binary)
                 (SUB           subst-binary)
                 (MUL           subst-binary)
                 (DIV           subst-binary)
                 (MOD           subst-binary)
                 (IND           subst-ind)
                 (LIST          subst-list)
                 (NIL           null-substitution)
                 (CONS          subst-cons)
                 (LIST-IND      subst-list-ind)
                 (UNION         subst-union)
                 (INL           subst-injection)
                 (INR           subst-injection)
                 (DECIDE        subst-decide)
                 (PRODUCT       subst-product)
                 (PAIR          subst-pair)
                 (SPREAD        subst-spread)
                 (FUNCTION      subst-function)
                 (LAMBDA        subst-lambda)
                 (APPLY         subst-apply)
                 (QUOTIENT      subst-quotient)
                 (SET           subst-set)
                 (EQUAL         subst-equal)
                 (AXIOM         null-substitution)
                 (LESS          subst-less)
                 (VAR           subst-var)
                 (BOUND-ID-TERM subst-bound-id)
		 (BOUND-ID-LIST subst-bound-id-list)
		 (APPLY-PARTIAL subst-apply-partial)
		 (RECURSIVE     subst-recursive)
		 (FIX           subst-fix)
		 (REC-IND       subst-rec-ind)
		 (PARFUNCTION   subst-parfunction)
		 (DOM           subst-dom)
                 (TERM-OF-THEOREM null-substitution)
                 (ATOMEQ        subst-decision)
                 (INTEQ         subst-decision)
                 (INTLESS       subst-decision)
		 (SIMPLE-REC    subst-simple-rec)
		 (SIMPLE-REC-IND subst-simple-rec-ind)
               )
        )
        (do (setf (get (car i) 'ev-subst-fcn) (cadr i)))
    )

    (<- substitution-happened$ nil)

)

 
(defun subst-for-free-vars (eval-closure)
    (ev-subst (term-of-eval-closure eval-closure)
              (env-of-eval-closure eval-closure)
              nil
    )
)


(defun generalized-subst-for-free-vars (closure)
  (let* ((term (term-of-eval-closure closure))
	 (env (env-of-eval-closure closure))
	 (substs
	   (remove-if
	     #'null
	     (mapcar #'(lambda (x)
			 (let* ((c (eval-lookup-quoted x env)))
			   (when c
			     (list x (generalized-subst-for-free-vars c)))))
		     (free-vars term)))))
    (cond ((null substs) term)
	  (t (substitute term substs)))))

(defun ev-subst (term env bound-ids)

    (Plet (prior-substitution-happened nil
          substituted-term            nil
         )

        (<- prior-substitution-happened substitution-happened$) 
        (<- substitution-happened$ nil)

        (<- substituted-term
            (funcall
                (substitution-fcn (kind-of-term term))
                term
                env
                bound-ids
            )
        )

        (Pif (not substitution-happened$) -->
            (<- substitution-happened$ prior-substitution-happened)
            (<- (Ttree-of-term substituted-term)
                (Ttree-of-term term)
            )
         fi)

        substituted-term

    )
)

(defun substitution-fcn (kind)
    (Plet (fcn (get kind 'ev-subst-fcn))
        (Pif fcn --> fcn
         || t --> (eval-err "Bad kind to substitution " kind)
         fi)
    )
)

(defun null-substitution (term env bound-ids)
  (declare (ignore env bound-ids))
  term)

(defun subst-bound-id (term env bound-ids)
    (bound-id-term
        'BOUND-ID-TERM nil
        (bound-ids-of-bound-id-term term)
        (ev-subst
            (term-of-bound-id-term term)
            env
            (append-bound-ids
                (bound-ids-of-bound-id-term term)
                bound-ids
            )
        )
    )
)

(defun subst-bound-id-list (term env bound-ids)
    (bound-id-list-term
        'BOUND-ID-LIST nil
        (bound-ids-of-bound-id-list-term term)
	(mapcar
	  #'(lambda (x) 
             (ev-subst
                x
                env
                (append-bound-ids
                    (bound-ids-of-bound-id-list-term term)
                    bound-ids
                )
            )
	  )
	  (term-list-of-bound-id-list-term term)
       )
    )
)

(defun subst-var (term env bound-ids)
    (Pif (null (member (id-of-var-term term) bound-ids)) -->
        (<- substitution-happened$ t)
        (subst-for-free-vars (eval-lookup-quoted (id-of-var-term term) env))
     || t -->
        term
     fi)
)

(defun subst-any (term env bound-ids)
    (any-term
        'ANY nil
        (ev-subst (term-of-any-term term) env bound-ids)
    )
)

(defun subst-minus (term env bound-ids)
    (minus-term
        'MINUS nil
        (ev-subst (term-of-minus-term term) env bound-ids)
    )
)

(defun subst-binary (term env bound-ids)
    (binary-term
        (kind-of-term term) nil
        (ev-subst (leftterm-of-binary-term term) env bound-ids)
        (ev-subst (rightterm-of-binary-term term) env bound-ids)
    )
)

(defun subst-ind (term env bound-ids)
    (ind-term
        'IND nil
        (ev-subst (value-of-ind-term term) env bound-ids)
        (ev-subst (downterm-of-ind-term term) env bound-ids)
        (ev-subst (baseterm-of-ind-term term) env bound-ids)
        (ev-subst (upterm-of-ind-term term) env bound-ids)
    )
)

(defun subst-list (term env bound-ids)
    (list-term
        'LIST nil
        (ev-subst (type-of-list-term term) env bound-ids)
    )
)

(defun subst-cons (term env bound-ids)
    (cons-term
        'CONS nil
        (ev-subst (head-of-cons-term term) env bound-ids)
        (ev-subst (tail-of-cons-term term) env bound-ids)
    )
)

(defun subst-list-ind (term env bound-ids)
    (list-ind-term
        'LIST-IND nil
        (ev-subst (value-of-list-ind-term term) env  bound-ids)
        (ev-subst (baseterm-of-list-ind-term term) env bound-ids)
        (ev-subst (upterm-of-list-ind-term term) env bound-ids)
    )
)

(defun subst-union (term env bound-ids)
    (union-term
        'UNION nil
        (ev-subst (lefttype-of-union-term term) env bound-ids)
        (ev-subst (righttype-of-union-term term) env bound-ids)
    )
)

(defun subst-injection (term env bound-ids)
    (injection-term
        (kind-of-term term) nil
        (ev-subst (term-of-injection-term term) env bound-ids)
    )
)

(defun subst-decide (term env bound-ids)
    (decide-term
        'DECIDE nil
        (ev-subst (value-of-decide-term term) env bound-ids)
        (ev-subst (leftterm-of-decide-term term) env bound-ids)
        (ev-subst (rightterm-of-decide-term term) env bound-ids)
    )
)

(defun subst-product (term env bound-ids)
    (product-term
        'PRODUCT nil
        (bound-id-of-product-term term)
        (ev-subst (lefttype-of-product-term term) env bound-ids)
        (ev-subst
            (righttype-of-product-term term)
            env
            (add-bound-id
                (bound-id-of-product-term term)
                bound-ids
            )
        )
    )
)

(defun subst-pair (term env bound-ids)
    (pair-term
        'PAIR nil
        (ev-subst (leftterm-of-pair-term term) env bound-ids)
        (ev-subst (rightterm-of-pair-term term) env bound-ids)
    )
)

(defun subst-spread (term env bound-ids)
    (spread-term
        'SPREAD nil
        (ev-subst (value-of-spread-term term) env bound-ids)
        (ev-subst (term-of-spread-term term) env bound-ids)
    )
)

(defun subst-function (term env bound-ids)
    (function-term
        'FUNCTION nil
        (bound-id-of-function-term term)
        (ev-subst (lefttype-of-function-term term) env bound-ids)
        (ev-subst
            (righttype-of-function-term term)
            env
            (add-bound-id
                (bound-id-of-function-term term)
                bound-ids
            )
        )
    )
)

(defun subst-parfunction (term env bound-ids)
    (parfunction-term
        'PARFUNCTION nil
        (bound-id-of-parfunction-term term)
        (ev-subst (lefttype-of-parfunction-term term) env bound-ids)
        (ev-subst
            (righttype-of-parfunction-term term)
            env
            (add-bound-id
                (bound-id-of-parfunction-term term)
                bound-ids
            )
        )
    )
)

(defun subst-lambda (term env bound-ids)
    (lambda-term
        'LAMBDA nil
        (bound-id-of-lambda-term term)
        (ev-subst
            (term-of-lambda-term term)
            env
            (add-bound-id
                (bound-id-of-lambda-term term)
                bound-ids
            )
        )
    )
)

(defun subst-apply (term env bound-ids)
    (apply-term
        'APPLY nil
        (ev-subst (function-of-apply-term term) env bound-ids)
        (ev-subst (arg-of-apply-term term) env bound-ids)
    )
)

(defun subst-apply-partial (term env bound-ids)
    (apply-partial-term
        'APPLY-PARTIAL nil
        (ev-subst (function-of-apply-partial-term term) env bound-ids)
        (ev-subst (arg-of-apply-partial-term term) env bound-ids)
    )
)

(defun subst-quotient (term env bound-ids)
    (quotient-term
        'QUOTIENT nil
        (bound-ids-of-quotient-term term)
        (ev-subst (lefttype-of-quotient-term term) env bound-ids)
        (ev-subst (righttype-of-quotient-term term)
                  env
                  (append-bound-ids
                      (bound-ids-of-quotient-term term)
                      bound-ids
                  )
        )
    )
)

(defun subst-set (term env bound-ids)
    (set-term
        'SET nil
        (bound-id-of-set-term term)
        (ev-subst (lefttype-of-set-term term) env bound-ids)
        (ev-subst
            (righttype-of-set-term term)
            env
            (add-bound-id
                (bound-id-of-set-term term)
                bound-ids
            )
        )
    )
)

(defun subst-recursive (term env bound-ids)
    (recursive-term
      'RECURSIVE nil
      (ev-subst (bound-id-list-term-of-recursive-term term) env bound-ids)
      (Pif (fix-term-of-recursive-term term) -->
	  (ev-subst (fix-term-of-recursive-term term) env bound-ids)
       || t --> nil
       fi)
      (id-of-recursive-term term)
      (ev-subst (term-of-recursive-term term) env bound-ids)
    )
)

(defun subst-fix (term env bound-ids)
    (fix-term
      'FIX nil
      (ev-subst (bound-id-list-term-of-fix-term term) env bound-ids)
      (id-of-fix-term term)
    )
)

(defun subst-rec-ind (term env bound-ids)
    (rec-ind-term
      'REC-IND nil
      (ev-subst (term-of-rec-ind-term term) env bound-ids)
      (ev-subst (bound-id-list-term-of-rec-ind-term term) env bound-ids)
      (id-of-rec-ind-term term)
    )
)

(defun subst-dom (term env bound-ids)
    (dom-term 'DOM nil (ev-subst (term-of-dom-term term) env bound-ids))
)


(defun subst-simple-rec (term env bound-ids)
    (simple-rec-term
      'SIMPLE-REC nil
      (bound-id-of-simple-rec-term term)
      (ev-subst
            (term-of-simple-rec-term term)
            env
            (add-bound-id
                (bound-id-of-simple-rec-term term)
                bound-ids))))


(defun subst-simple-rec-ind (term env bound-ids)
    (simple-rec-ind-term
        'SIMPLE-REC-IND nil
        (ev-subst (value-of-simple-rec-ind-term term) env bound-ids)
        (ev-subst (term-of-simple-rec-ind-term term) env bound-ids)))






(defun subst-equal (term env bound-ids)
    (equal-term
        'EQUAL nil
        (ev-subst (type-of-equal-term term) env bound-ids)
        (for (tm in (terms-of-equal-term term))
            (save (ev-subst tm env bound-ids))
        )
    )
)

(defun subst-less (term env bound-ids)
    (less-term
        'LESS nil
        (ev-subst (leftterm-of-less-term term) env bound-ids)
        (ev-subst (rightterm-of-less-term term) env bound-ids)
    )
)

(defun subst-decision (term env bound-ids)
    (decision-term
        (kind-of-term term)
        nil
        (ev-subst (leftterm-of-decision-term term) env bound-ids)
        (ev-subst (rightterm-of-decision-term term) env bound-ids)
        (ev-subst (if-term-of-decision-term term) env bound-ids)
        (ev-subst (else-term-of-decision-term term) env bound-ids)
    )
)

(defun append-bound-ids (list1 list2)
    (Pif (null list1) -->
        list2
     || t -->
        (cons
            (car list1)
            (append-bound-ids (cdr list1) list2)
        )
     fi)
)

(defun add-bound-id (id bound-ids)
    (cons id bound-ids)
)
