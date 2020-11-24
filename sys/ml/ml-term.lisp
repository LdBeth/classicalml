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


;-- ML primitive extensions making PRL the object language.
;-- The first part of the file is some modifictations to the
;-- type structure of ML so that PRL terms become recognizable
;-- objets in represtenation.  The second part is an implementation
;-- of the refine primitive.  Following this are primitive constructors
;-- and destructrs for the types of proof, term, and rule.

(declaim (special %val AUTO-TACTIC))

;-- TERM-TYPE-TOK is cons'd onto all ML objects of type term.  Because
;-- ML does not do any run time type checking, it is necessary to be able to
;-- distinguish the type of term from other types by looking at it so the
;-- a different equality predicate can be used on terms.  A list is used as
;-- the token because eq will equate any atoms with the same p-name, clearly
;-- an undesirable property.  

;;; The above describes an incorrect implementation that depended on all
;;; references to the value '(TERM-TYPE-TOK) of TERM-TYPE-TOK being eq.
;;; The value is now something which does not appear in any ML data, and
;;; equal is used for the comparison in is-term-type.

(defconstant TERM-TYPE-TOK '(TERM-TYPE-TOK . 0))

(defun ml-term (term)
  (cons TERM-TYPE-TOK term))

(defun prl-term (ml-term)
  (cdr ml-term))

(defun is-term-type (x)
  (and
    (consp x)
    (not (null x))
    (equal (car x) TERM-TYPE-TOK)))

                                                        
;-- Predicates on terms:  Return the type of the term.
;-- note that must convert to prl format of term before looking up type.
;-- Possible results are UNIVERSE, VOID, etc.

(defun ml-term-kind (term)
  (kind-of-term (prl-term term)))


(defmlfun (|term_kind| ml-adjusted-term-kind) (term)
	  (term -> tok)
  (case (ml-term-kind term)
    (POS-NUMBER 'NATURAL-NUMBER)
    (ADD 'ADDITION)
    (SUB 'SUBTRACTION)
    (MUL 'MULTIPLICATION)
    (DIV 'DIVISION)
    (MOD 'MODULO)
    (IND 'INTEGER-INDUCTION)
    (LIST-IND 'LIST-INDUCTION)
    (otherwise (ml-term-kind term))))

;-- 
;-- constructors for  terms.
;-- 

;-- Warning:  make sure there are no spaces in the token.

(defmlfun (|make_universe_term| ml-make-universe-term) (level)
	  (int -> term)
  (ml-term  (universe-term 'UNIVERSE nil (check-level level '|make_universe_term|))))

(dmlc |make_void_term| (ml-term (void-term 'VOID nil)) term)

(defmlfun (|make_any_term| ml-make-any-term) (term)
	  (term -> term)
  (ml-term (any-term 'ANY nil (prl-term term))))

(dmlc |make_atom_term| (ml-term (atom-term 'ATOM nil)) term)

(defmlfun (|make_token_term| ml-make-token-term) (atom)
	  (tok -> term)
  (ml-term (token-term 'TOKEN nil (istring atom))))
(dmlc |make_int_term| (ml-term (int-term 'INT nil)) term)

(defmlfun (|make_natural_number_term| ml-make-natural-number-term) (int)
	  (int -> term)
  (when (< int 0)
    (breakout evaluation '|make_natural_number_term: number must be a natural.|))
  (ml-term (pos-number-term 'POS-NUMBER nil int)))

(defmlfun (|make_minus_term| ml-make-minus-term) (term)
	  (term -> term)
  (ml-term (minus-term 'MINUS nil (prl-term term))))

(defmlfun (|make_binary_term| ml-make-binary-term) (binary left-term right-term)
	  (tok -> (term -> (term -> term)))
  (unless (member binary '(ADD SUB MUL DIV MOD))
    (breakout evaluation '|make_binary_term:  Term kind must be ADD,SUB,MUL,DIV, or MOD|))
  (ml-term (binary-term binary nil (prl-term left-term) (prl-term right-term))))

(defmlfun (|make_integer_induction_term| ml-make-integer-induction-term)
	  (value downterm baseterm upterm)
	  (term -> (term -> (term -> (term -> term))))
  (ml-term (ind-term 'IND nil
                     (prl-term value) 
                     (prl-term downterm)
                     (prl-term baseterm) 
                     (prl-term upterm))))

(defmlfun |make_list_term| (type)
	  (term -> term)
  (ml-term (list-term 'LIST nil (prl-term type))))
	  
(dmlc |make_nil_term| (ml-term (nil-term nil nil)) term)

(defmlfun (|make_cons_term| ml-make-cons-term) (head tail)
	  (term -> (term -> term))
  (ml-term (cons-term 'CONS nil (prl-term head) (prl-term tail))))

(defmlfun (|make_list_induction_term| ml-make-list-induction-term) (value baseterm upterm)
	  (term -> (term -> (term -> term)))
  (ml-term (list-ind-term 'LIST-IND nil
                          (prl-term value)
                          (prl-term baseterm)
                          (prl-term upterm))))

(defmlfun (|make_union_term| ml-make-union-term) (lefttype righttype)
	  (term -> (term -> term))
  (ml-term (union-term 'UNION nil (prl-term lefttype) (prl-term righttype))))

(defmlfun (|make_inl_term| ml-make-inl-term) (term)
	  (term -> term )
  (ml-term (injection-term 'INL nil (prl-term term))))

(defmlfun (|make_inr_term| ml-make-inr-term) (term)
	  (term -> term)
  (ml-term (injection-term 'INR nil (prl-term term))))

(defmlfun (|make_decide_term| ml-make-decide-term) (value leftterm rightterm)
	  (term -> (term -> (term -> term)))
  (ml-term (decide-term 'DECIDE nil
                        (prl-term value)
                        (prl-term leftterm)
                        (prl-term rightterm))))

(defmlfun (|make_product_term| ml-make-product-term) (bound-id lefttype righttype)
	  (tok -> (term -> (term -> term)))
  (ml-term (product-term 'PRODUCT  nil 
                         (prl-id bound-id)
                         (prl-term lefttype)
                         (prl-term righttype))))

(defmlfun (|make_pair_term| ml-make-pair-term) (leftterm rightterm)
	  (term -> (term -> term))
  (ml-term (pair-term 'PAIR nil  (prl-term leftterm) (prl-term rightterm))))

(defmlfun (|make_spread_term| ml-make-spread-term) (value term)
	  (term -> (term -> term))
  (ml-term (spread-term 'SPREAD nil (prl-term value) (prl-term term))))

(defmlfun (|make_function_term| ml-make-function-term) (bound-id lefttype righttype)
	  (tok -> (term -> (term -> term)))
  (ml-term (function-term 'FUNCTION nil
                          (prl-id bound-id) 
                          (prl-term lefttype)
                          (prl-term righttype))))

(defmlfun (|make_lambda_term| ml-make-lambda-term) (bound-id term)
	  (tok -> (term -> term))
  (ml-term (lambda-term 'LAMBDA nil (prl-id bound-id) (prl-term term))))

(defmlfun (|make_apply_term| ml-make-apply-term) (function arg)
	  (term -> (term -> term))
  (ml-term (apply-term 'APPLY nil (prl-term function) (prl-term arg))))

;--
;-- Partial function terms.
;--

(defmlfun (|make_partial_function_term| ml-make-partial-function-term)
	   (id lefttype righttype)
	   (tok -> (term -> (term -> term)))
   (ml-term (parfunction-term 'PARFUNCTION
			      nil id
			      (prl-term lefttype)
			      (prl-term righttype))))

(defmlfun (|make_fix_term| ml-make-fix-term) (bound-ids bound-id-terms sel-id)
	  ((tok list) -> ((term list) -> (tok -> term)))
  (let ((new-term 
	  (fix-term 'FIX nil
		    (bound-id-list-term 'BOUND-ID-LIST nil
					bound-ids
					(mapcar #'prl-term bound-id-terms))
		    sel-id)))
    (let ((message
	    (check-fix-or-rec-ind-term-constraints
	      (id-of-fix-term new-term)
	      (bound-ids-of-bound-id-list-term
		(bound-id-list-term-of-fix-term new-term))
	      (term-list-of-bound-id-list-term
		(bound-id-list-term-of-fix-term new-term))
	      '|fix|)))
      (unless (null message)
	(breakout evaluation message))
      (ml-term new-term))))


(defmlfun (|make_dom_term| ml-make-dom-term) (type)
	  (term -> term)
  (ml-term (dom-term 'DOM nil (prl-term type))))

(defmlfun (|make_apply_partial_function_term| ml-make-apply-partial-function-term)
	  (function arg) (term -> (term -> term))
  (ml-term
      (apply-partial-term
	'APPLY-PARTIAL nil
	(prl-term function)
	(prl-term arg))))

(defmlfun (|make_rec_term| ml-make-rec-term)
	  (bound-ids bound-id-terms fix-term rec-id arg-term)
	  ((tok list) -> ((term list) -> (term -> (tok -> (term -> term)))))
  (let ((new-term
	  (recursive-term
	    'RECURSIVE nil
	    (bound-id-list-term
	      'BOUND-ID-TERM-LIST nil
	      bound-ids
	      (mapcar #'prl-term bound-id-terms))
	    (prl-term fix-term)
	    rec-id
	    (prl-term arg-term))))
    (let ((err-msg
	    (check-constraints-on-rec-term
	      bound-ids
	      (term-list-of-bound-id-list-term
		(bound-id-list-term-of-recursive-term new-term))
	      (term-of-recursive-term new-term)
	      rec-id)))
      (unless (null err-msg)
	(breakout evaluation err-msg))
      (ml-term new-term))))


(defmlfun (|make_rec_without_fix_term| ml-make-rec-without-fix-term)
	  (bound-ids bound-id-terms  rec-id arg-term)
	  ((tok list) -> ((term list) -> (tok -> (term -> term))))
  (let ((new-term
	  (recursive-term
	    'RECURSIVE nil
	    (bound-id-list-term
	      'BOUND-ID-TERM-LIST nil
	      bound-ids
	      (mapcar #'prl-term bound-id-terms))
	    nil					;-- no fix term.
	    rec-id
	    (prl-term arg-term))))
    (let ((err-msg
	    (check-constraints-on-rec-term
	      bound-ids
	      (term-list-of-bound-id-list-term
		(bound-id-list-term-of-recursive-term new-term))
	      (term-of-recursive-term new-term)
	      rec-id)))
      (unless (null err-msg)
	(breakout evaluation err-msg))
      (ml-term new-term))))

(defmlfun (|make_simple_rec_term| ml-make-simple-rec-term) (id term)
	  (tok -> (term -> term))
  (when (null (prl-id id))
    (breakout evaluation '|make_simple_rec_term: id cannot be nil|))
  (ml-term (simple-rec-term
	     'SIMPLE-REC nil
	     id
	     (prl-term term))))

(defmlfun (|make_rec_ind_term| ml-make-rec-ind-term)
	  (term bound-ids bound-id-terms rec-ind-id)
	  (term -> ((tok list) -> ((term list) -> (tok -> term))))
  (let ((new-term 
	  (rec-ind-term
	    'REC-IND nil
	    (prl-term term)
	    (bound-id-list-term
	      'BOUND-ID-LIST nil
	      bound-ids
	      (mapcar #'prl-term bound-id-terms))
	    rec-ind-id)))
    (let ((message
	    (check-fix-or-rec-ind-term-constraints
	      (id-of-rec-ind-term new-term)
	      (bound-ids-of-bound-id-list-term	
		(bound-id-list-term-of-rec-ind-term new-term))
	      (term-list-of-bound-id-list-term 
		(bound-id-list-term-of-rec-ind-term new-term))
	      '|rec-ind|)))
      (when message
	(breakout evaluation message))
      (ml-term new-term))))

(defmlfun (|make_simple_rec_ind_term| ml-make-simple-rec-ind-term) (value term)
	  (term -> (term -> term))
  (when (not (and (eql (kind-of-term (prl-term term)) 'BOUND-ID-TERM)
		  (eql 2 (length (bound-ids-of-bound-id-term (prl-term term))))))
    (breakout evaluation '|make_simple_rec_ind: second arg. inappropriate.|))
  (ml-term (simple-rec-ind-term
	     'SIMPLE-REC-IND nil
	     (prl-term value)
	     (prl-term term))))

(defmlfun (|make_quotient_term| ml-make-quotient-term) (id1 id2 lefttype righttype)
	  (tok -> (tok -> (term -> (term -> term))))
  (unless (and (prl-id id1) (prl-id id2))
    (breakout evaluation '|make_quotient_term: ids must be non-null|))
  (ml-term (quotient-term
	     'QUOTIENT nil
	     (list id1 id2)
	     (prl-term lefttype)
	     (prl-term righttype))))

(defmlfun (|make_set_term| ml-make-set-term) (bound-id lefttype righttype)
	  (tok -> (term -> (term -> term)))
  (ml-term (set-term 'SET nil (prl-id bound-id) (prl-term lefttype) (prl-term righttype))))

(defmlfun (|make_equal_term| ml-make-equal-term) (term terms)
	  (term -> ((term list) -> term))
  (ml-term (equal-term 'EQUAL nil
                       (prl-term term)
                       (mapcar #'prl-term terms))))

(dmlc |make_axiom_term| (ml-term (axiom-term 'AXIOM nil)) term)

(defmlfun (|make_less_term| ml-make-less-term) (lefttype righttype)
	  (term -> (term -> term))
  (ml-term (less-term 'LESS nil (prl-term lefttype) (prl-term righttype))))

(defmlfun (|make_var_term| ml-make-var-term) (tok)
	  (tok -> term)
  (ml-term (var-term
	     'VAR nil  ;-- no ttree.
	     (implode (delete space (istring tok))))))

(defun ml-make-decision-term (kind leftterm rightterm if-term else-term)
  (unless (member kind '(ATOMEQ INTEQ INTLESS))
    (breakout evaluation '|make_decision_term: not atomeq, inteq, or intless|))
  (ml-term (decision-term
	     kind nil
	     (prl-term leftterm)
	     (prl-term rightterm)
	     (prl-term if-term)
	     (prl-term else-term))))

(defmlfun (|make_atomeq_term| ml-make-atomeq-term) (leftterm rightterm if-term else-term)
	  (term -> (term -> (term -> (term -> term))))
  (ml-make-decision-term 'ATOMEQ leftterm rightterm if-term else-term))

(defmlfun (|make_inteq_term| ml-make-inteq-term) (leftterm rightterm if-term else-term)
	  (term -> (term -> (term -> (term -> term))))
  (ml-make-decision-term 'INTEQ leftterm rightterm if-term else-term))

(defmlfun (|make_intless_term| ml-make-intless-term) (leftterm rightterm if-term else-term)
	  (term -> (term -> (term -> (term -> term))))
  (ml-make-decision-term 'INTLESS leftterm rightterm if-term else-term))

(defmlfun (|make_bound_id_term| ml-make-bound-id-term) (bound-ids term)
	  ((tok list ) -> (term -> term))
  (let ((ids (mapcar #'prl-id bound-ids)))
    ;; Make sure all the ids are distinct.
    (do ((ids (cdr ids) (cdr ids))
	 (id  (car ids) (car ids)))
	((null ids))
      (when (member id ids)
	(breakout evaluation '|bound identifiers must be distinct|)))
    (ml-term (bound-id-term 'BOUND-ID-TERM nil ids (prl-term term)))))




(defmlfun (|make_term_of_theorem_term| ml-make-term-of-theorem-term) (name)
	  (tok -> term)
  (ml-term (term-of-theorem-term 'TERM-OF-THEOREM nil name)))

(dmlc |make_object_term| (ml-term (object-term 'OBJECT nil)) term)


(defmlfun (|make_tagged_term| ml-make-tagged-term) (tag term)
	  (int -> (term -> term))
  (when (minusp tag)
    (breakout evaluation '|make-tagged-term: tag must be non-neg.|))
  (ml-term (tagged-term
	     'TAGGED nil
	     tag
	     (prl-term term))))

(dmlc |make_object_term| (ml-term (object-term 'OBJECT nil)) term)

(defmlfun (|is_object_term| ml-is-object-term) (term)
	  (term -> bool)
  (eql (kind-of-term (prl-term term)) 'OBJECT))

;-- 
;-- destructors on terms.
;-- 

;-- general destuctor pattern.  The arguments are an ml-term,
;-- a term kind (expressed as an atom), a destructor that operates
;-- on prl terms, and an error message (atom) to be printed out
;-- if the kind does not match.  None of the arguments should be 
;-- quoted. (term kind destuctor error-message) respectivly.
;-- remember that in defining macros, the first argument is the name of
;-- the macro.  Thus to get the first real argument, cadr is used.

(defmacro destruct (ml-term kind destructor message)
  `(if (eql (kind-of-term (prl-term ,ml-term)) ',kind)
      (,destructor (prl-term ,ml-term))
      (breakout evaluation ',message)))
        
(defmlfun (|destruct_universe| ml-destruct-universe) (term)
	  (term -> int)
  (destruct term UNIVERSE level-of-universe-term
	      |destruct_universe: Not a universe term|))

(defmlfun (|destruct_any| ml-destruct-any) (term)
	  (term -> term)
  (ml-term (destruct term ANY  term-of-any-term |destruct_any: Not an any term.|)))

(defmlfun (|destruct_token| ml-destruct-token) (term)
	  (term -> tok)
  (unless (eql (ml-term-kind term) 'TOKEN)
    (breakout evaluation '|destruct_token: Not a token term.|))
  (implode (atom-of-token-term (prl-term term))))

(defmlfun (|destruct_natural_number| ml-destruct-natural-number) (term)
	  (term -> int)
  (destruct term POS-NUMBER number-of-pos-number-term
	    |destruct_natural_number: Not a natural number term.|))

(defmlfun (|destruct_minus| ml-destruct-minus) (term)
	  (term -> term)
  (ml-term
    (destruct term MINUS term-of-minus-term
	      |destruct_minus: Not minus term.|)))

;-- for a binary term, extract the two subterms and construct
;-- a pair of ML terms.

(defun destruct-binary-term (prl-term)
  (cons
    (ml-term (leftterm-of-binary-term prl-term))
    (ml-term (rightterm-of-binary-term prl-term))))

(defmlfun (|destruct_addition| ml-destruct-addition) (term)
	  (term -> (term |#| term))
  (destruct term ADD destruct-binary-term
	    |destruct_addition: Not addition term.|))

(defmlfun (|destruct_subtraction| ml-destruct-subtraction) (term)
	  (term -> (term |#| term))
  (destruct term SUB destruct-binary-term
	    |destruct_subtraction: Not subtraction term.|))

(defmlfun (|destruct_multiplication| ml-destruct-multiplication) (term)
	  (term -> (term |#| term))
  (destruct term MUL destruct-binary-term
	    |destruct_multiplication: Not multiplication term.|))

(defmlfun (|destruct_division| ml-destruct-division) (term)
	  (term -> (term |#| term))
  (destruct term DIV destruct-binary-term
	    |destruct_division: Not division term.|))

(defmlfun (|destruct_modulo| ml-destruct-modulo) (term)
	  (term -> (term |#| term))
  (destruct term MOD destruct-binary-term
	    |destruct_modulo: Not modulo term.|))

(defmlfun (|destruct_integer_induction| ml-destruct-integer-induction) (term)
	  (term -> (term |#| (term |#| (term |#| term))))
  (when (eql (ml-term-kind term) 'IND)
    (setq term (prl-term term))
    (cons
      (ml-term (value-of-ind-term term))
      (cons
	(ml-term (downterm-of-ind-term term))
	(cons
	  (ml-term (baseterm-of-ind-term term))
	  (ml-term (upterm-of-ind-term term)))))))
                  

(defmlfun (|destruct_list| ml-destruct-list) (term)
	  (term -> term)
  (ml-term (destruct term LIST type-of-list-term
		     |destruct_list: Not a list term.|)))

(defmlfun (|destruct_cons| ml-destruct-cons) (term)
	  (term -> (term |#| term))
  (if (eql (ml-term-kind term) 'CONS)
      (cons
	(ml-term (head-of-cons-term (prl-term term)))
	(ml-term (tail-of-cons-term (prl-term term))))
      (breakout evaluation '|destruct_cons: Not a cons term.|)))


(defmlfun (|destruct_list_induction| ml-destruct-list-induction) (term)
	  (term -> (term |#| (term |#| term)))
  (unless (eql (ml-term-kind term) 'LIST-IND)
    (breakout evaluation '|destruct_list_ind: not a list induction term.|))
  (setq term (prl-term term))
  (cons (ml-term (value-of-list-ind-term term))
	(cons (ml-term (baseterm-of-list-ind-term term))
	      (ml-term (upterm-of-list-ind-term term)))))


(defmlfun (|destruct_union| ml-destruct-union) (term)
	  (term -> (term |#| term))
  (unless (eql (ml-term-kind term) 'UNION)
    (breakout evaluation '|destruct_union: not a union term.|))
  (cons (ml-term (lefttype-of-union-term (prl-term term)))
	(ml-term (righttype-of-union-term (prl-term term)))))

(defun destruct-injection (prl-term)
  (ml-term (term-of-injection-term prl-term)))

(defmlfun (|destruct_inl| ml-destruct-inl) (term)
	  (term -> term)
  (destruct term INL destruct-injection |destruct_inl: not inl term.|))

(defmlfun (|destruct_inr| ml-destruct-inr) (term)
	  (term -> term)
  (destruct term INR destruct-injection |destruct_inr: not inr term.|))

(defmlfun (|destruct_decide| ml-destruct-decide) (term)
	  (term -> (term |#| (term |#| term)))
  (unless (eql (ml-term-kind term) 'DECIDE)
    (breakout evaluation '|destruct_decide: not decide term.|))
  (setq term (prl-term term))
  (cons (ml-term
	  (value-of-decide-term term))
	(cons
	  (ml-term (leftterm-of-decide-term term))
	  (ml-term (rightterm-of-decide-term term)))))

(defmlfun (|destruct_product| ml-destruct-product) (term)
	  (term -> (tok |#|  (term |#| term)))
  (unless (eql (ml-term-kind term) 'PRODUCT)
    (breakout evaluation '|destruct_product: Not a product term.|))
  (cons
    (bound-id-of-product-term (prl-term term))
    (cons
      (ml-term (lefttype-of-product-term (prl-term term)))
      (ml-term (righttype-of-product-term (prl-term term))))))

(defmlfun (|destruct_pair| ml-destruct-pair) (term)
	  (term -> (term |#| term))
  (unless (eql (ml-term-kind term) 'PAIR)
    (breakout evaluation '|destruct_pair: Not a pair term.|))
  (cons
    (ml-term (leftterm-of-pair-term (prl-term term)))
    (ml-term (rightterm-of-pair-term (prl-term term)))))

(defmlfun (|destruct_spread| ml-destruct-spread) (term)
	  (term -> (term |#| term))
  (unless (eql (ml-term-kind term) 'SPREAD)
    (breakout evaluation '|destruct_spread: Not a spread term.|))
  (cons
    (ml-term (value-of-spread-term (prl-term term)))
    (ml-term (term-of-spread-term (prl-term term)))))

(defmlfun (|destruct_function| ml-destruct-function) (term)
	  (term -> (tok |#| (term |#| term)))
  (unless (eql (ml-term-kind term) 'FUNCTION)
    (breakout evaluation '|destruct_function: Not a function term.|))
  (cons
    (bound-id-of-function-term (prl-term term))
    (cons
      (ml-term (lefttype-of-function-term (prl-term term)))
      (ml-term (righttype-of-function-term (prl-term term))))))

(defmlfun (|destruct_lambda| ml-destruct-lambda) (term)
	  (term -> (tok |#| term))
  (unless (eql (ml-term-kind term) 'LAMBDA)
    (breakout evaluation '|destruct_lambda: not a lambda term.|))
  (cons
    (bound-id-of-lambda-term (prl-term term))
    (ml-term (term-of-lambda-term (prl-term term)))))

(defmlfun (|destruct_apply| ml-destruct-apply) (term)
	  (term -> (term |#| term))
  (unless (eql (ml-term-kind term) 'APPLY)
    (breakout evaluation '|destruct_apply: not an apply term.|))
  (cons
    (ml-term (function-of-apply-term (prl-term term)))
    (ml-term (arg-of-apply-term (prl-term term)))))


(defmlfun (|destruct_partial_function| ml-destruct-partial-function) (term)
	  (term -> (tok |#| (term |#| term)))
  (unless (eql (ml-term-kind term) 'PARFUNCTION)
    (breakout evaluation '|destruct_partial_function: not a partial function term.|))
  (cons
    (bound-id-of-parfunction-term (prl-term term))
    (cons
      (ml-term (lefttype-of-parfunction-term (prl-term term)))
      (ml-term (righttype-of-parfunction-term (prl-term term))))))

(defmlfun (|destruct_fix| ml-destruct-fix) (term)
	  (term -> ((tok list) |#| ((term list) |#| tok)))
  (unless (eql (ml-term-kind term) 'FIX)
    (breakout evaluation '|destruct_fix: term is not a fix term.|))
  (cons
    (bound-ids-of-bound-id-list-term
      (bound-id-list-term-of-fix-term (prl-term term)))
    (cons
      (mapcar
	#'ml-term
	(term-list-of-bound-id-list-term
	  (bound-id-list-term-of-fix-term (prl-term term))))
      (id-of-fix-term (prl-term term)))))


(defmlfun (|destruct_dom| ml-destruct-dom) (term)
	  (term -> term)
  (unless (eql (ml-term-kind term) 'DOM)
    (breakout evaluation '|destruct_dom: not a dom term.|))
  (ml-term (term-of-dom-term (prl-term term))))

(defmlfun (|destruct_apply_partial| ml-destruct-apply-partial) (term)
	  (term -> (term |#| term))
  (unless (eql (ml-term-kind term) 'APPLY-PARTIAL)
    (breakout evaluation '|destruct_apply_partial: not an apply partial term.|))
  (cons
    (ml-term (function-of-apply-partial-term (prl-term term)))
    (ml-term (arg-of-apply-partial-term (prl-term term)))))

(defmlfun (|destruct_rec| ml-destruct-rec) (term)
	  (term -> ((tok list) |#| ((term list) |#| (term |#| (tok |#| term)))))
  (unless (and (eql (ml-term-kind term) 'RECURSIVE)
	       (fix-term-of-recursive-term (prl-term term)))
    (breakout evaluation '|destruct_rec: not a rec term.|))
  (cons
    (bound-ids-of-bound-id-list-term
      (bound-id-list-term-of-recursive-term (prl-term term)))
    (cons
      (mapcar
	#'ml-term
	(term-list-of-bound-id-list-term
	  (bound-id-list-term-of-recursive-term (prl-term term))))
      (cons
	(ml-term (fix-term-of-recursive-term (prl-term term)))
	(cons
	  (id-of-recursive-term (prl-term term))
	  (ml-term (term-of-recursive-term (prl-term term))))))))

(defmlfun (|destruct_rec_without_fix| ml-destruct-rec-without-fix) (term)
	  (term -> ((tok list) |#| ((term list) |#|  (tok |#| term))))
  (unless (and (eql (ml-term-kind term) 'RECURSIVE)
	       (not (fix-term-of-recursive-term (prl-term term))))
    (breakout evaluation '|destruct_rec: not a rec term.|))
  (cons
    (bound-ids-of-bound-id-list-term
      (bound-id-list-term-of-recursive-term (prl-term term)))
    (cons
      (mapcar
	#'ml-term
	(term-list-of-bound-id-list-term
	  (bound-id-list-term-of-recursive-term (prl-term term))))
      (cons
	(id-of-recursive-term (prl-term term))
	(ml-term (term-of-recursive-term (prl-term term)))))))

(defmlfun (|destruct_rec_ind| ml-destruct-rec-ind) (term)
	  (term -> (term |#| ((tok list) |#| ((term list) |#| tok))))
  (unless (eql (ml-term-kind term) 'REC-IND)
    (breakout evaluation '|destruct_rec_ind: not a rec ind term.|))
  (cons
    (ml-term (term-of-rec-ind-term (prl-term term)))
    (cons
      (bound-ids-of-bound-id-list-term
	(bound-id-list-term-of-rec-ind-term (prl-term term)))
      (cons
	(mapcar
	  #'ml-term
	  (term-list-of-bound-id-list-term
	    (bound-id-list-term-of-rec-ind-term (prl-term term))))
	(id-of-rec-ind-term (prl-term term))))))

(defmlfun (|destruct_simple_rec| ml-destruct-simple-rec) (term)
	  (term -> (tok |#| term))
  (unless (eql (ml-term-kind term) 'SIMPLE-REC)
    (breakout evaluation '|destruct_simple_rec: not a simple rec term.|))
  (cons
    (bound-id-of-simple-rec-term (prl-term term))
    (ml-term (term-of-simple-rec-term (prl-term term)))))

(defmlfun (|destruct_simple_rec_ind| ml-destruct-simple-rec-ind) (term)
	  (term -> (term |#| term))
  (unless (eql (ml-term-kind term) 'SIMPLE-REC-IND)
    (breakout evaluation '|destruct_simple_rec_ind: not a simple rec ind term.|))
  (cons
    (ml-term (value-of-simple-rec-ind-term (prl-term term)))
    (ml-term (term-of-simple-rec-ind-term (prl-term term)))))

(defmlfun (|destruct_quotient| ml-destruct-quotient) (term)
	  (term -> (tok |#| (tok |#| (term |#| term))))
  (unless (eql (ml-term-kind term) 'QUOTIENT)
    (breakout evaluation '|destruct_quotient: not a quotient type|))
  (append					;-- there are 2 bound ids.
    (bound-ids-of-quotient-term (prl-term term))
    (cons
      (ml-term (lefttype-of-quotient-term (prl-term term)))
      (ml-term (righttype-of-quotient-term (prl-term term))))))

(defmlfun (|destruct_set| ml-destruct-set) (term)
	  (term -> (tok |#| (term |#| term)))
  (unless (eql (ml-term-kind term) 'SET)
    (breakout evaluation '|destruct_set: Not a set term.|))
  (cons
    (bound-id-of-set-term (prl-term term))
    (cons
      (ml-term (lefttype-of-set-term (prl-term term)))
      (ml-term (righttype-of-set-term (prl-term term))))))

(defmlfun (|destruct_equal| ml-destruct-equal) (term)
	  (term -> ((term list) |#| term))
  (unless (eql (ml-term-kind term) 'EQUAL)
    (breakout evaluation '|destruct_equal: not equal term.|))
  (cons
    (mapcar
      #'ml-term
      (terms-of-equal-term (prl-term term)))
    (ml-term (type-of-equal-term (prl-term term)))))

(defmlfun (|destruct_less| ml-destruct-less) (term)
	  (term -> (term |#| term))
  (unless (eql (ml-term-kind term) 'LESS)
    (breakout evaluation '|desruct_less: not a less term.|))
  (cons
    (ml-term (leftterm-of-less-term (prl-term term)))
    (ml-term (rightterm-of-less-term (prl-term term)))))

(defmlfun (|destruct_var| ml-destruct-var) (term)
	  (term -> tok)
  (destruct term VAR id-of-var-term |destruct_var: not a var term.|))

(defmlfun (|destruct_bound_id| ml-destruct-bound-id) (term)
	  (term -> ((tok list) |#| term))
  (unless (eql (ml-term-kind term) 'BOUND-ID-TERM)
    (breakout evaluation '|destruct_bound_id: not a bound id term.|))
  (cons
                (bound-ids-of-bound-id-term (prl-term term))
                (ml-term (term-of-bound-id-term (prl-term term)))))

(defmlfun (|destruct_bound_id_list| ml-destruct-bound-id-list) (term)
	  (term -> ((tok list) |#| (term list)))
  (unless (eql (ml-term-kind term) 'BOUND-ID-LIST-TERM)
    (breakout evaluation '|destruct_bound_id_list: not a bound id list term.|))
  (cons
    (bound-ids-of-bound-id-list-term (prl-term term))
    (mapcar #'ml-term (term-list-of-bound-id-list-term (prl-term term)))))

(defmlfun (|destruct_term_of_theorem| ml-destruct-term-of-theorem) (term)
	  (term -> tok)
  (destruct term TERM-OF-THEOREM name-of-term-of-theorem-term 
	    |destruct_term_of_theorem: Not a theorem term.|))

;-- decision-kind should be ATOMEQ, INTEQ, or INTLESS

(defun destruct-decision-term (decision-kind term)
  (unless (eql (ml-term-kind term) decision-kind)
    (breakout evaluation '|Not a decision term.|))
  (setq term (prl-term term))
  (cons
    (ml-term (leftterm-of-decision-term term))
    (cons
      (ml-term (rightterm-of-decision-term term))
      (cons
	(ml-term (if-term-of-decision-term term))
	(ml-term (else-term-of-decision-term term))))))

(defmlfun (|destruct_atomeq| ml-destruct-atomeq) (term)
	  (term -> (term |#| (term |#| (term |#| term))))
  (destruct-decision-term 'ATOMEQ term))

(defmlfun (|destruct_inteq| ml-destruct-inteq) (term)
	  (term -> (term |#| (term |#| (term |#| term))))
  (destruct-decision-term 'INTEQ term))

(defmlfun (|destruct_intless| ml-destruct-intless) (term)
	  (term -> (term |#| (term |#| (term |#| term))))
  (destruct-decision-term 'INTLESS term))

(defun destruct-tagged (prl-term)
  (cons
    (tag-of-tagged-term prl-term)
    (ml-term (term-of-tagged-term prl-term))))


(defmlfun (|destruct_tagged| ml-destruct-tagged) (term)
	  (term -> (int |#| term))
  (destruct term TAGGED destruct-tagged
	    |destruct_tagged: not a tagged term|))


(defun get-ml-value (var)
  (declare (special global%env))
  (symbol-value (name-for-desc (assoc var global%env))))

;;; Return the main goal of the theorem named by the argument, failing
;;; if the theorem is not in the library or if it is but has status
;;; raw or bad.
(defmlfun (|main_goal_of_theorem| ml-main-goal-of-theorem) (name)
	  (tok -> term)
  (unless (is-lib-member name)
    (breakout evaluation (concat '|main_goal_of_theorem: | name)))
  (let ((obj (library-object name)))
    (when (or (not (eql (sel (object obj) kind) `THM))
	      (member (sel (object obj) status) '(RAW BAD)))
      (breakout evaluation (concat '|main_goal_of_theorem: | name)))
    (ml-term
      (get-conclusion-of-theorem-object
	(sel (object obj) value)))))

(defmlfun (|proof_of_theorem| ml-proof-of-theorem) (name)
	  (tok -> proof)
  (unless (is-lib-member name)
    (breakout evaluation '|proof_of_theorem|))
  (let ((obj (library-object name)))
    (when (or (not (eql (sel (object obj) kind) `THM))
	      (eql (sel (object obj) status) 'RAW))
      (breakout evaluation '|main_goal_of_theorem |))
    (get-proof-of-theorem-object (sel (object obj) value) name)))

;;; Return the extracted term of the named theorem, failing if extraction
;;; does.

(defmlfun (|extracted_term_of_theorem| ml-extracted-term-of-theorem) (name)
	  (tok -> term)
  (when (or (not (is-lib-member name))
	    (not (eql 'THM (sel (object (library-object name)) kind))))
    (breakout evaluation
      (concat '|extracted_term_of_theorem: | name '| not in library or not a THM.|)))
  (let ((term (evaluable-term-of-theorem name))
	(status  (sel (object (library-object name)) status)))
    (when (or (member status '(RAW BAD))
	      (and (eql status 'INCOMPLETE)
		   (not (extraction-completed? term))))
      (breakout evaluation
	(concat '|extracted_term_of_theorem: | name '| inappropriate for extraction.|)))
    (ml-term term)))

;;;  Lift map-on-subterms from ref-support to ML.

(defmlfun (|map_on_subterms| ml-map-on-subterms) (f term)
	  ((term -> term) -> (term -> term)) 
  (ml-term
    (map-on-subterms
      #'(lambda (x) (prl-term (ap f (ml-term x))))
      (prl-term term))))

(defmlfun (|subterms| ml-subterms) (ml-term)
	  (term -> (term list))
  (let* ((term (prl-term ml-term))
	 (k (kind-of-term term)))
    (mapcar
      #'ml-term
      (cond ((member k terms-with-no-subterms)
	     nil)
	    ((eql k 'EQUAL)
	     `(,@(cadddr term) ,(caddr term)))
	    ((or
	      (member k terms-with-one-binding-id)
	      (member k terms-with-a-list-of-binding-ids))
	     (cdddr term))
	    ((eql k 'REC-IND)
	     `(,(caddr term) ,@(cadddr (cadddr term))))
	    ((eql k 'FIX)
	     (cadddr (caddr term)))
	    ((eql k 'RECURSIVE)
	     (if (fix-term-of-recursive-term term)
		 `(,@(cadddr (caddr term)) ,(cadddr term) ,(sixth term))
		 `(,@(cadddr (caddr term)) ,(sixth term))))
	    ((eql k 'TAGGED)
	     (cdddr term))
	    ((member k terms-with-no-binding-ids)
	     (cddr term))
	    (t
	     (breakout evaluation
		       (concat '|list_subterms: illegal term kind -- | k)))))))

(defmlfun (|free_vars| ml-free-vars) (ml-term)
	  (term -> (term list))
  (mapcar
    #'(lambda (x) (ml-term `(VAR nil ,x)))
    (free-vars (prl-term ml-term))))

;;; The next three functions rely on the fact that illegal-tags-1 returns
;;; a list whose members are eq to the corresponding subterms of term.
(defun remove-illegal-tags (term illegal-tag-list)
    (if (and (eql (kind-of-term term) 'TAGGED)
	     (member term illegal-tag-list))
	(remove-illegal-tags (term-of-tagged-term term) illegal-tag-list) 
	(map-on-subterms
	  #'(lambda (x) (remove-illegal-tags x illegal-tag-list))
	  term)))

(defmlfun (|remove_illegal_tags| ml-remove-illegal-tags) (ml-term)
	  (term -> term)
  (let ((term (prl-term ml-term)))
    (ml-term (remove-illegal-tags term (illegal-tags-1 term)))))

(defmlfun (|member_of_tok_list| ml-memq) (x l) (tok -> ((tok list) -> bool))
  (and (member x l) t))

(defmlfun (|do_computations| ml-do-computations) (x)
	  (term -> term)
  (ml-term (do-indicated-computations (prl-term x))))

(defmlfun (|compute| ml-compute) (x)
	  (term -> term)
  (ml-term (initialize-and-compute 0 (prl-term x))))

(defmlfun (|no_extraction_compute| ml-no-extraction-compute) (ml-term)
	  (term -> (term |#| int))
  (multiple-value-bind
    (term steps)
      (no-extraction-compute 0 (prl-term ml-term))
    (cons (ml-term term) steps)))

(defmlfun (|apply_without_display_maintenance| ml-apply-without-display-maintenance)
	  (f x) ((* -> **) -> (* -> **))
  (let ((*hack-Ttree?* nil))
    (ap f x)))

(defmlfun |set_display_maintenance_mode| (on?) (bool -> void)
  (setf *hack-ttree?* on?))

(defmlfun (|simplify| ml-simplify) (term)
	  (term -> term)
  (ml-term (simplify (prl-term term))))


(defmlfun (|lambda_compute| ml-lambda-compute)
	  (term normalizep expand-extractions-p excepted-extractions)
	  (term -> (bool -> (bool -> ((tok list) -> term))))
  (ml-term (lambda-compute
	     (prl-term term) normalizep expand-extractions-p excepted-extractions)))


(defmlfun (|parse| ml-parse) (tok)
	  (tok -> term)
  (let ((res (catch 'process-err (parse (cons 'TTREE (istring tok))))))
    (flush-scanner-input)
    (when (eql (car res) 'ERR)
      (breakout evaluation (cdr res)))
    (ml-term res)))

(defun remove-best-Ttree (term)
  (<- (Ttree-of-term term) nil))

(defun flatten-defs (term)
  (remove-best-ttree term)
  (map-on-subterms #'flatten-defs term))

(defmlfun (|represent_nodef_term| ml-represent-term) (term) 
	  (term -> tok)
  (ml-term_to_tok (ml-term (flatten-defs (prl-term term)))))

(defun lib-object (name) (library-object name))

;;; This, of course, must be used with care.  
(defmlfun (|set_extraction| ml-set-extraction) (name term)
	  (tok -> (term -> void ))
  (check-library-membership name 'THM)
  (<- (sel (theorem-object (sel (object (lib-object name)) value)) extracted-term)
      (prl-term term))
  nil)
