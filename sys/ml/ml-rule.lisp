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

 
;-- 
;--     A note about rule representation.
;-- 
;-- Rules in ML for prl differ from the prl rules in that the combine
;-- both the representation of the rule (the rule body) and the actual
;-- internal version of the the rule.  The rules are dotted-pairs: the 
;-- car is the rule, and the cdr is the rule body.  In some cases, the
;-- rule body is absent this will be indicated by a nil for the rule 
;-- body.  Since null rule bodies (rules that have no print form) are
;-- indicated using the null-ttree, this should not cause a problem.
;-- All nil rule bodies are generated using the prl function rule-to-ttree
;-- before the return to PRL, so PRL should never see a nil rule body.
;-- 



(defun check-level (level rule-name)
  (unless (and (integerp level) (< 0 level))
    (breakout evaluation
	      (concat rule-name '|: level must be strictly positive.|)))
  level) 

;-- the function prl-id maps the tokens `NIL` and `nil` to (),
;-- i.e. lisp nil.  This is for optional identifiers in rules.

(defun prl-id (id)
  (if (or (eql id '|nil|) (eql id '|NIL|))
      ()
      id))

;-- 
;-- rule constructors.
;-- 


;-- Rules for universes.

(dmlc |universe_intro_void|
      (cons (univ-intro-rule 'UNIVERSE-INTRO-VOID)
	    nil)
      rule)

(dmlc |universe_intro_integer|
      (cons (univ-intro-rule 'UNIVERSE-INTRO-INT)
	    nil)
      rule)

(dmlc |universe_intro_atom| (cons
                                (univ-intro-rule 'UNIVERSE-INTRO-ATOM)
                                nil
                            ) rule)


;(defun ml-universe-intro-list (type)
;  (cons
;    (univ-intro-rule-list 'UNIVERSE-INTRO-LIST (prl-term type))
;    nil ))

(dmlc |universe_intro_list| (cons
			      (univ-intro-rule 'UNIVERSE-INTRO-LIST)
			      nil
			    ) rule)

(dmlc |universe_intro_union| (cons
                                 (univ-intro-rule 'UNIVERSE-INTRO-UNION)
                                 nil
                             ) rule)


(defmlfun (|universe_intro_product| ml-universe-intro-product) (id type)
	  (tok -> (term -> rule))
  (cons
    (univ-intro-rule-product
        'UNIVERSE-INTRO-PRODUCT
        (prl-id id)
        (prl-term type))
    nil))

(defmlfun (|intro_function| ml-universe-intro-function) (id type)
	  (tok -> (term -> rule))
  (cons
    (univ-intro-rule-function
        'UNIVERSE-INTRO-FUNCTION
        (prl-id id)
        (prl-term type))
    nil))


(dmlc |universe_intro_function_independent|
      (cons
	(univ-intro-rule-function
	  'UNIVERSE-INTRO-FUNCTION
	  nil
	  nil
	)
	nil
      )
      rule
)

(defmlfun (|universe_intro_quotient| ml-universe-intro-quotient) (term1 term2 tok1 tok2 tok3)
	  (term -> (term -> (tok -> (tok -> (tok -> rule)))))
  (cons
    (univ-intro-rule-quotient
      'UNIVERSE-INTRO-QUOTIENT
      (prl-term term1)
      (prl-term term2)
      (list (prl-id tok1) (prl-id tok2) (prl-id tok3)))
    nil))
                         
(defmlfun (|universe_intro_set| ml-universe-intro-set) (id type)
	  (tok -> (term -> rule))
  (cons 
    (univ-intro-rule-set
      'UNIVERSE-INTRO-SET
      (prl-id id)
      (prl-term type))
    nil))


(dmlc |universe_intro_set_independent|
      (cons
          (univ-intro-rule-set
              'UNIVERSE-INTRO-SET
              nil    ;-- no id
              nil    ;-- no term
          )
          nil
      )
      rule
)



(defmlfun (|universe_intro_equality| ml-universe-intro-equality) (type num-terms)
	  (term -> (int -> rule))
  (cons
    (univ-intro-rule-equal 'UNIVERSE-INTRO-EQUAL (prl-term type) num-terms)
    nil))

(dmlc |universe_intro_less| (cons
                                (univ-intro-rule 'UNIVERSE-INTRO-LESS)
                                nil
                            ) rule)



(defmlfun (|universe_intro_universe| ml-universe-intro-universe) (level)
	  (int -> rule)
  (check-level level '|universe_intro_universe|)
  (cons
    (univ-intro-rule-universe 'UNIVERSE-INTRO-UNIVERSE level)
    nil))  ;-- no rule body



(dmlc |universe_equality| (cons
                              (equal-intro-rule 'EQUAL-INTRO-UNIVERSE)
                              nil
                          ) rule)


;-- 
;--  Rules for Void.
;-- 



(defmlfun (|void_elim| ml-void-elim) (assum-num)
	  (int -> rule)
  (cons
    (void-elim-rule 'VOID-ELIM assum-num)
    nil  ;-- no rule body
  )
)

(dmlc |void_equality| (cons
                          (equal-intro-rule 'EQUAL-INTRO-VOID)
                          nil
                      ) rule)

(dmlc |void_equality_any| (cons
                              (equal-intro-rule 'EQUAL-INTRO-ANY)
                              nil
                          ) rule)

;-- 
;-- Rules for Integers.
;-- 



(defmlfun (|integer_intro_integer| ml-integer-intro-integer) (selector)
	  (int -> rule)
  (cons
    (int-intro-rule 'INT-INTRO-NUMBER selector)
    nil  ;-- no rule body
  )
)

(dmlc |integer_intro_addition| (cons
                                   (int-intro-rule 'INT-INTRO-OP TPlus)
                                   nil
                               ) rule)
(dmlc |integer_intro_subtraction| (cons
                                      (int-intro-rule 'INT-INTRO-OP TMinus)
                                      nil
                                  ) rule)
(dmlc |integer_intro_multiplication|
    (cons
        (int-intro-rule 'INT-INTRO-OP TStar)
        nil
    ) rule
)
(dmlc |integer_intro_division| (cons
                                   (int-intro-rule 'INT-INTRO-OP TSlash)
                                   nil
                               ) rule)
(dmlc |integer_intro_modulo| (cons
                                 (int-intro-rule 'INT-INTRO-OP TMod)
                                 nil
                             ) rule)


(defmlfun (|integer_elim| ml-integer-elim) (assum-num id1 id2)
	  (int -> (tok -> (tok -> rule)))
    (cons
      (int-elim-rule
        'INT-ELIM
        assum-num
        (list (prl-id id1) (prl-id id2))
      )      
      nil                                       ;-- no rule body
    )
)


(dmlc |integer_equality| (cons
                             (equal-intro-rule 'EQUAL-INTRO-INT)
                             nil
                         ) rule)

(dmlc |integer_equality_natural_number|
    (cons
        (equal-intro-rule 'EQUAL-INTRO-POS-NUMBER)
        nil
    ) rule
)
(dmlc |integer_equality_minus| (cons
                                   (equal-intro-rule 'EQUAL-INTRO-MINUS)
                                   nil
                               ) rule)
(dmlc |integer_equality_addition| (cons
                                      (equal-intro-rule 'EQUAL-INTRO-ADD)
                                      nil
                                  ) rule)
(dmlc |integer_equality_subtraction| (cons
                                         (equal-intro-rule 'EQUAL-INTRO-SUB)
                                         nil
                                     ) rule)
(dmlc |integer_equality_multiplication| 
    (cons
        (equal-intro-rule 'EQUAL-INTRO-MUL)
        nil
    ) rule
)
(dmlc |integer_equality_division| (cons
                                      (equal-intro-rule 'EQUAL-INTRO-DIV)
                                      nil
                                  ) rule)
(dmlc |integer_equality_modulo| (cons
                                    (equal-intro-rule 'EQUAL-INTRO-MOD)
                                    nil
                                ) rule)



(defmlfun (|integer_equality_induction| ml-integer-equality-induction)
	  (over-id over-type new-id1 new-id2)
	  (tok -> (term -> (tok -> (tok -> rule))))
  (cons
    (Plet (new-ids (cond ((and (prl-id new-id1) (prl-id new-id2))
			  (list (prl-id new-id1) (prl-id new-id2))
			 )
			 (t nil)
		   )
	 )
    (cond
        ((null (prl-id over-id))
            (equal-intro-rule-over
                'EQUAL-INTRO-IND
                nil              ;-- no over-type
		new-ids
            )
        )
        (t (equal-intro-rule-over
               'EQUAL-INTRO-IND
               (cons (prl-id over-id) (prl-term over-type))
               new-ids
           )
        )
    ))
    nil  ;-- no rule body
  )
)

(defun build-computation-rule (kind where)
  (cons
    (comp-rule kind where)
    nil   ;-- no rule body
  )
)
        


(defmlfun (|integer_computation| ml-integer-computation) (kind where)
	  (tok -> (int -> rule))
    (cond
        ((eql kind '|DOWN|) (setq kind 'IND-COMP-DOWN))
        ((eql kind '|BASE|) (setq kind 'IND-COMP-BASE))
        ((eql kind '|UP|)   (setq kind 'IND-COMP-UP))
        (t (breakout evaluation
             '|integer_computation:  kind must be `DOWN`, `BASE`, or `UP`|
           )
        )
    )
    (build-computation-rule kind where)
)


;-- 
;-- Rules for decision terms.
;-- 

(dmlc |atom_eq_equality|
      (cons (equal-intro-rule 'EQUAL-INTRO-ATOMEQ) nil)
      rule)

(dmlc |int_eq_equality|
      (cons (equal-intro-rule 'EQUAL-INTRO-INTEQ) nil)
      rule)

(dmlc |int_less_equality|
      (cons (equal-intro-rule 'EQUAL-INTRO-INTLESS) nil)
      rule)

(defmlfun (|atom_eq_computation| ml-atom-eq-computation) (where case)
	  (int -> (bool -> rule))
  (let* ((kind (cond (case 'ATOMEQ-COMP-TRUE) (t 'ATOMEQ-COMP-FALSE))))
    (build-computation-rule kind where)))


(defmlfun (|int_eq_computation| ml-int-eq-computation) (where case)
	  (int -> (bool -> rule))
    (let* ((kind (cond (case 'INTEQ-COMP-TRUE) (t 'INTEQ-COMP-FALSE))))
      (build-computation-rule kind where)))


(defmlfun (|int_less_computation| ml-int-less-computation) (where case)
	  (int -> (bool -> rule))
  (let* ((kind (cond (case 'INTLESS-COMP-TRUE) (t 'INTLESS-COMP-FALSE))))
    (build-computation-rule kind where)))




;-- 
;-- rules for atoms.
;-- 




(defmlfun (|atom_intro| ml-atom-intro) (token-term)
	  (term -> rule)
  (cons
    (cond ((equal (ml-term-kind token-term) 'TOKEN)
              (atom-intro-rule 'ATOM-INTRO (prl-term token-term))
          )
       (t 
        (breakout evaluation '|atom_intro: term must be a token term.|))
    )
    nil  ;-- no rule body
  )
)


(dmlc |atom_equality| (cons
                          (equal-intro-rule 'EQUAL-INTRO-ATOM)
                          nil
                      ) rule)


(dmlc |atom_equality_token|
      (cons
	(equal-intro-rule 'EQUAL-INTRO-TOKEN)
	nil)
      rule)


;-- 
;-- rules for LISTS.
;-- 


(defmlfun (|list_intro_nil| ml-list-intro-nil) (level)
	  (int -> rule)
  (check-level level '|list_intro_nil|)
  (cons
    (list-intro-rule 'LIST-INTRO-NIL level)
    nil  ;-- no rule body
  )
)

(dmlc |list_intro_cons|
    (cons
        (list-intro-rule 'LIST-INTRO-CONS nil)
        nil
    ) 
    rule
)





(defmlfun (|list_elim| ml-list-elim) (assum-num new-id1 new-id2 new-id3)
	  (int -> (tok -> (tok -> (tok -> rule))))
  (cons
    (list-elim-rule
      'LIST-ELIM
      assum-num
      (list
        (prl-id new-id1) (prl-id new-id2) (prl-id new-id3)
      )
    )
    nil  ;-- no rule body
  )
)

(dmlc |list_equality| (cons
                          (equal-intro-rule 'EQUAL-INTRO-LIST)
                          nil
                      ) rule)


(defmlfun (|list_equality_nil| ml-list-equality-nil) (level)
	  (int -> rule)
  (check-level level '|list_equality_nil|)
  (cons
    (equal-intro-rule-level
      'EQUAL-INTRO-NIL
      level
      nil
    )
    nil  ;-- no rule body
  )
)


(dmlc |list_equality_cons| (cons
                               (equal-intro-rule 'EQUAL-INTRO-CONS)
                               nil
                           ) rule)



(defmlfun (|list_equality_induction| ml-list-equality-induction)
	  (over-id over-type using-term id1 id2 id3)
	  (tok -> (term -> (term -> (tok -> (tok -> (tok -> rule))))))
  (cons
    (let ((new-ids (if (and (prl-id id1) (prl-id id2) (prl-id id3))  ;-- all there?
		       (list (prl-id id1) (prl-id id2) (prl-id id3))
		       nil)))
      (cond
	((null (prl-id over-id))
	 (equal-intro-rule-using
	   'EQUAL-INTRO-LIST-IND
	   nil              ;-- no over-type
	   (prl-term using-term)
	   new-ids))
	(t
           (equal-intro-rule-using
               'EQUAL-INTRO-LIST-IND
               (cons (prl-id over-id) (prl-term over-type))
	       (prl-term using-term) 
	       new-ids))))
    nil))  ;-- no rule body




(defmlfun (|list_computation| ml-list-computation) (where)
	  (int -> rule)
    (build-computation-rule 'LIST-IND-COMP where)
)


;-- 
;-- rules for union.
;-- 

(defun ml-union-intro (level selector)
  (check-level level '|union_intro|)
  (cons
    (case selector
      (left (union-intro-rule 'UNION-INTRO level TLeft))
      (right (union-intro-rule 'UNION-INTRO level TRight)))
    nil  ;-- no rule body
  )
)

(defmlfun (|union_intro_left| ml-union-intro-left) (level)
	  (int -> rule)
    (ml-union-intro level 'left)
)

(defmlfun (|union_intro_right| ml-union-intro-right) (level)
	  (int -> rule)
    (ml-union-intro level 'right)
)


(defmlfun (|union_elim| ml-union-elim) (assum-num new-id1 new-id2)
	  (int -> (tok -> (tok -> rule)))
  (cons
    (union-elim-rule
        'UNION-ELIM
        assum-num
        (list
          (prl-id new-id1)
          (prl-id new-id2)
        )
    )
    nil  ;-- no rule body
  )
)

(dmlc |union_equality| (cons
                           (equal-intro-rule 'EQUAL-INTRO-UNION)
                           nil
                       ) rule)



(defmlfun (|union_equality_inl| ml-union-equality-inl) (level)
	  (int -> rule)
    (check-level level '|union_equality_inl|)
    (cons
        (equal-intro-rule-level
            'EQUAL-INTRO-INL
            level
            nil
        )
        nil  ;-- no rule body.
    )
)



(defmlfun (|union_equality_inr| ml-union-equality-inr) (level)
	  (int -> rule)
    (check-level level '|union_equality_inr|)
    (cons
        (equal-intro-rule-level
            'EQUAL-INTRO-INR
            level
            nil
        )
        nil ;-- no rule body.
    )
)

(defmlfun (|union_equality_decide| ml-union-equality-decide)
	  (over-id over-type using-term id1 id2)
	  (tok -> (term -> (term -> (tok -> (tok -> rule)))))
  (cons
    (equal-intro-rule-using
        'EQUAL-INTRO-DECIDE
        (cond ((null (prl-id over-id)) nil)
              (t (cons (prl-id over-id) (prl-term over-type)))
        )
        (prl-term using-term)
        (cond ((or (prl-id id1) (prl-id id2)) (list (prl-id id1) (prl-id id2)))
              (t nil)
        ) 
    )
    nil  ;-- no rule body
  )
)


(defmlfun (|union_computation| ml-union-computation) (where)
	  (int -> rule)
    (build-computation-rule 'DECIDE-COMP where)
)


;--
;-- Rules for Products.
;--


(dmlc |product_intro|    
    (cons
        (product-intro-rule 'PRODUCT-INTRO nil nil nil)
        nil
    ) ;-- should never see
                                                     ;-- nil's.
    rule
)
    



(defmlfun (|product_intro_dependent| ml-product-intro-dependent) (leftterm level newid)
	  (term -> (int -> (tok -> rule)))
  (check-level level '|product_intro|)
  (cons
    (product-intro-rule 'PRODUCT-INTRO
			level (prl-term leftterm) (prl-id newid))
    nil  ;-- no rule body
  )
)


(defmlfun (|product_elim| ml-product-elim) (assum-num new-id1 new-id2)
	  (int -> (tok -> (tok -> rule)))
  (cons
    (product-elim-rule
        'PRODUCT-ELIM
        assum-num
        (list
          (prl-id new-id1) 
          (prl-id new-id2)
        )
    )
    nil  ;-- no rule body
  )
)



(defmlfun (|product_equality| ml-product-equality) (new-id)
	  (tok -> rule)
  (cons
    (equal-intro-rule-new-id 'EQUAL-INTRO-PRODUCT (prl-id new-id))
    nil  ;-- no rule body
  )
)



(defmlfun (|product_equality_pair| ml-product-equality-pair) (level new-id)
	  (int -> (tok -> rule))
  (check-level level '|product_equality_pair|)
  (cons
    (equal-intro-rule-level
        'EQUAL-INTRO-PAIR
        level
        (prl-id new-id)
    )
    nil  ;-- no rule body
  )
)

(dmlc |product_equality_pair_independent|
      (cons
    (equal-intro-rule-level
        'EQUAL-INTRO-PAIR
        1       ;-- ignore universe level and id.
        nil
    )
    nil  ;-- no rule body
  )
  rule
)




(defmlfun (|product_equality_spread| ml-product-equality-spread)
	  (over-id over-type using-term id1 id2)
	  (tok -> (term -> (term -> (tok -> (tok -> rule)))))
  (cons
    (equal-intro-rule-using
        'EQUAL-INTRO-SPREAD
        (cond ((null (prl-id over-id)) nil)
              (t (cons (prl-id over-id) (prl-term over-type)))
        )
        (prl-term using-term)
        (cond ((or (prl-id id1) (prl-id id2)) (list (prl-id id1) (prl-id id2)))
              (t nil)
        )
    )
    nil  ;-- no rule body
  )
)



(defmlfun (|product_computation| ml-product-computation) (where)
	  (int -> rule)
    (build-computation-rule 'SPREAD-COMP where)
)

;-- 
;-- Rules for functions.
;-- 


(defmlfun (|function_intro| ml-function-intro) (level new-id)
	  (int -> (tok -> rule))
  (check-level level '|function_intro|)
  (cons
    (function-intro-rule
        'FUNCTION-INTRO
        level
        (prl-id new-id)
    )
    nil  ;-- no rule body
  )
)

(dmlc |function_intro_independent|
    (cons
        (function-intro-rule
            'FUNCTION-INTRO
            1
            nil
        )
        nil
    )
    rule
)


            



(defmlfun (|function_elim| ml-function-elim) (assum-num leftterm new-id)
	  (int -> (term -> (tok -> rule)))
  (cons
    (function-elim-rule 
        'FUNCTION-ELIM
        assum-num
        (prl-term leftterm)
        (list (prl-id new-id))
    )
    nil  ;-- no rule body
  )
)


(defmlfun (|function_elim_independent| ml-function-elim-independent) (assum-num new-id)
	  (int -> (tok -> rule))
  (cons
    (function-elim-rule
        'FUNCTION-ELIM
        assum-num
        nil        ;-- ignore the left term
        (list (prl-id new-id))        ;-- ignore the identifier.
    )
    nil  ;-- no rule body
  )
)


(defmlfun (|function_equality| ml-function-equality) (new-id)
	  (tok -> rule)
  (cons
    (equal-intro-rule-new-id 'EQUAL-INTRO-FUNCTION (prl-id new-id))
    nil  ;-- no rule body
  )
)

(dmlc |function_equality_independent| (ml-function-equality nil) rule) 


(defmlfun (|function_equality_lambda| ml-function-equality-lambda) (level new-id)
	  (int -> (tok -> rule))
  (check-level level '|function_equality_lambda|)
  (cons
    (equal-intro-rule-level
        'EQUAL-INTRO-LAMBDA
        level
        (prl-id new-id)
    )
    nil  ;-- no rule body
  )
)




(defmlfun (|function_equality_apply| ml-function-equality-apply) (using-term)
	  (term -> rule)
  (cons
     (equal-intro-rule-using
       'EQUAL-INTRO-APPLY
       nil              ;-- no over-type
       (prl-term using-term)
       nil					;-- no new id
     )
     nil  ;-- no rule body
  )
)



(defmlfun (|function_computation| ml-function-computation) (where)
	  (int -> rule)
    (build-computation-rule 'APPLY-COMP where)
)


;--
;-- Rules for quotients.
;--


(defmlfun (|quotient_intro| ml-quotient-intro) (level)
	  (int -> rule)
  (check-level level '|quotient_intro|)
  (cons
    (quotient-intro-rule 'QUOTIENT-INTRO level)
    nil      ;-- No rule body.
  )
)


(defmlfun (|quotient_elim| ml-quotient-elim) (assum-num level new-id1 new-id2)
	  (int -> (int -> (tok -> (tok -> rule))))
  (check-level level '|quotient_elim|)
  (cons
    (quotient-elim-rule 'QUOTIENT-ELIM
	 assum-num level
	 (cond ((and (prl-id new-id1) (prl-id new-id2))
		(list (prl-id new-id1) (prl-id new-id2)))
	       (t nil)
	 )
    )
    nil        ;-- No rule body.
  )
)



(defmlfun (|quotient_formation| ml-quotient-formation) (new-id1 new-id2 new-id3)
	  (tok -> (tok -> (tok -> rule)))
    (cons
      (equal-intro-rule-quotient 'EQUAL-INTRO-QUOTIENT
        (list (prl-id new-id1) (prl-id new-id2) (prl-id new-id3)) 
      )
      nil ;-- no rule body.
    )
)


(defmlfun (|quotient_equality| ml-quotient-equality) (new-id1 new-id2)
	  (tok -> (tok -> rule))
    (cons
      (equal-intro-rule-quotient 'EQUAL-INTRO-QUOTIENT
        (list (prl-id new-id1) (prl-id new-id2)) 
      )
      nil ;-- no rule body.
    )
)


(defmlfun (|quotient_equality_element| ml-quotient-equality-element) (level)
	  (int -> rule)
  (check-level level '|quotient_equality_element|)
    (cons
      (equal-intro-rule-level
        'EQUAL-INTRO-QUOTIENT-ELEM
        level
        nil    ;--  no id
      )
      nil      ;--  No body yet.
    )
)



;--
;-- Rules for sets.
;--



(defmlfun (|set_intro| ml-set-intro) (level leftterm new-id)
	  (int -> (term -> (tok -> rule)))
  (check-level level '|set_intro|)
    (cons
      (set-intro-rule 'SET-INTRO level (prl-term leftterm) (prl-id new-id))
      nil ;-- no rule body.
    )
)

(dmlc |set_intro_independent| (cons
                                (set-intro-rule 'SET-INTRO nil nil nil)
                                nil
                              )
      rule
)



(defmlfun (|set_elim| ml-set-elim) (assum-num level new-id)
	  (int -> (int -> (tok -> rule)))
  (check-level level '|set_elim|)
    (cons
      (set-elim-rule
        'SET-ELIM
        assum-num
        level
        (list (prl-id new-id))
      )
      nil   ;-- no rule body
    )
)



(defmlfun (|set_equality| ml-set-equality) (new-id)
	  (tok -> rule)
    (cons
      (equal-intro-rule-new-id 'EQUAL-INTRO-SET (prl-id new-id))
      nil
    )
)


(defmlfun (|set_formation| ml-set-formation) (new-id)
	  (tok -> rule)
    (cons
      (equal-intro-rule-new-id 'EQUAL-INTRO-SET (prl-id new-id))
      nil
    )
)

(dmlc |set_formation_independent|
    (cons
      (equal-intro-rule-new-id 'EQUAL-INTRO-SET nil)
      nil
    )
    rule
)


(defmlfun (|set_equality_element| ml-set-equality-element) (level new-id)
	  (int -> (tok -> rule))
  (check-level level '|set_equality_element|)
    (cons
      (equal-intro-rule-level 'EQUAL-INTRO-SET-ELEM level (prl-id new-id))
      nil
    )
)



;-- 
;-- Additional Equality Rules.
;-- 

(dmlc |axiom_equality_equal|
                      (cons
                           (equal-intro-rule 'EQUAL-INTRO-AXIOM-EQUAL)
                           nil
                       ) rule)                  


(dmlc |axiom_equality_less|
                      (cons
                           (equal-intro-rule 'EQUAL-INTRO-AXIOM-LESS)
                           nil
                       ) rule)                  

(dmlc |equal_equality| (cons
                           (equal-intro-rule 'EQUAL-INTRO-EQUAL)
                           nil
                       ) rule)

(dmlc |equal_equality_variable|
    (cons
        (equal-intro-rule 'EQUAL-INTRO-VAR)
        nil
    ) 
    rule
)


;-- 
;-- Rules for less.
;-- 

(dmlc |less_intro| (cons
                       (less-intro-rule 'LESS-INTRO)
                       nil
                   ) rule)

(dmlc |less_equality| (cons
                          (equal-intro-rule 'EQUAL-INTRO-LESS)
                          nil
                      ) rule)

(dmlc |less_equality_axiom|
    (cons
        (equal-intro-rule 'EQUAL-INTRO-LESS-AXIOM)
        nil
    ) 
    rule
)



;-- 
;-- Misc. Additional Rules.



    
(defmlfun (|hyp| ml-hyp) (assum-num)
	  (int  -> rule)
  (cons
    (hyp-rule 'HYP assum-num)
    nil  ;-- no rule body
  )
)

;-- Construct outline of lemma rule.  Prl refinement will
;-- fill in missing fields when the rule is used. 


(defmlfun (|lemma| ml-lemma) (lemma new-id)
	  (tok -> (tok -> rule))
  (cons
    (lemma-rule 'LEMMA lemma (prl-id new-id) nil nil)
    nil  ;-- no rule body
  )
)



(defmlfun (|def| ml-def) (theorem new-id)
	  (tok -> (tok -> rule))
  (cons
    (def-rule 'DEF theorem (prl-id new-id))
    nil  ;-- no rule body
  )
)


(defmlfun (|seq| ml-seq) (terms new-ids)
	  ((term list) -> ((tok list) -> rule))
  (cons
    (sequence-rule 'SEQUENCE
        (mapcar #'prl-term terms) ;-- change to prl terms
        (mapcar #'prl-id new-ids)
    )
    nil  ;-- no rule body
  )
)


(defmlfun (|explicit_intro| ml-explicit-intro) (term)
	  (term -> rule)
  (cons
    (explicit-intro-rule 'EXPLICIT-INTRO (prl-term term))
    nil  ;-- no rule body
  )
)

;-- tactic rule consructor


(defmlfun (|tactic| ml-tactic) (tactic-name)
	  (tok -> rule)
  (cons
    (tactic-rule 'TACTIC
        (cons 'Ttree
            (istring tactic-name)
        )
        nil   ;-- This is for the proof top.
    )
    nil  ;-- no rule body
  )
)


(defmlfun (|experimental| ml-experimental) (subgoal-function)
	  (tok -> rule)
    (cons
      (experimental-rule
	'EXPERIMENTAL
	(cons 'Ttree
	      (istring subgoal-function)
	)
	nil
      )
      nil ;-- no rule body
    )
)


(defmlfun (|subproof_of_tactic_rule| ml-subproof-of-tactic-rule) (rule)
	  (rule -> proof)
    (cond
      ((and (equal (kind-of-rule (car rule)) 'TACTIC)  ;-- car gets actual rule
	    (proof-top-of-tactic-rule (car rule)))
       (proof-top-of-tactic-rule (car rule)))
      (t (breakout evaluation '|subproof_of_tactic_rule:  rule is not a refinement tactic rule or no subproof.|))))


(defmlfun (|cumulativity| ml-cumulativity) (level)
	  (int -> rule)
  (check-level level '|cumulativity|)
  (cons
    (cumulativity-rule
        'CUMULATIVITY
        level
    )
    nil  ;-- no rule body
  )
)

(dmlc |equality| (cons
                     (equality-rule 'EQUALITY)
                     nil
                 ) rule)

(defmlfun (|substitution| ml-substitution)
	  (level equality-term over-id over-term)
	  (int ->  (term -> (tok -> (term -> rule))))
  (check-level level '|substitution|)
    (cons
      (substitute-rule 'SUBSTITUTE
                    level
                    (prl-term equality-term)
                    (bound-id-term
                      'BOUND-ID-TERM
                      nil ;-- no Ttree representation.
		      (list (prl-id over-id))
                      (prl-term over-term)
                    )
      )
      nil   ;-- no rule body.    
   )
)


(defmlfun (|arith| ml-arith) (level)
	  (int -> rule)
  (check-level level '|arith|)
  (cons (arith-rule 'ARITH level) nil))




(defmlfun |extensionality| (level using-terms new-id)
   ( int -> ( (term list) -> (tok -> rule) ) )
  (check-level level '|extensionality|)
  (cons
    (extensionality-rule
      'EXTENSIONALITY level (mapcar #'prl-term using-terms) (prl-id new-id))
    nil)) 

;(defmlfun (|extensionality| ml-extensionality) (new-id level)
;	  (tok -> (int -> rule))
;    (cons
;      (extensionality-rule
;	'EXTENSIONALITY
;	(prl-id new-id)
;;	level					
;      )
;      nil
;    )
;)


;--
;-- Partial function type rules.
;--


(defmlfun (|partial_function_equality| ml-partial-function-equality) (new-id)
	  (tok -> rule)
    (cons
      (equal-intro-rule-new-id
	'EQUAL-INTRO-PARFUNCTION
	(prl-id new-id)
      )
      nil
    )
) 

(dmlc |partial_function_equality_independent| (ml-partial-function-equality nil)
      rule
)




(defmlfun (|partial_function_equality_fix| ml-partial-function-equality-fix)
	  (level using-terms new-ids)
	  (int -> ((term list) -> ((tok list) -> rule )))
  (check-level level '|partial_function_equality_fix|)
    (cond ((equal (length using-terms) (1- (length new-ids)))
	   (cons
	     (equal-intro-rule-fix
	       'EQUAL-INTRO-FIX
	       level
	       (mapcar #'prl-term using-terms)
	       (mapcar #'prl-id new-ids)
	     )
	     nil
	   )
	  )
	  (t (breakout evaluation
  '|partial_function_equality_fix: Number of using terms must be one less than the number of new ids.|
	     ))
      )
)




(defmlfun (|partial_function_equality_apply| ml-partial-function-equality-apply)
	  (using-term new-id)
	  (term -> (tok -> rule))
    (cons
      (equal-intro-rule-using
	'EQUAL-INTRO-APPLY-PARTIAL
	nil
        (prl-term using-term)
	(list (prl-id new-id))
      )
      nil
     )
 )




(defmlfun (|partial_function_equality_dom| ml-partial-function-equality-dom)
	  (using-term) (term -> rule)
    (cons
      (equal-intro-rule-using
	'EQUAL-INTRO-DOM
	nil 
	(prl-term using-term)
	nil
      )
      nil
    )
)


(defmlfun (|partial_function_elim| ml-partial-function-elim)
	  (hyp on-argument new-id1 new-id2)
	  (int -> (term -> (tok -> (tok -> rule))))
    (cons
      (parfunction-elim-rule
	'PARFUNCTION-ELIM
	hyp
	(prl-term on-argument)
	(list (prl-id new-id1) (prl-id new-id2))
      )
      nil
    )
)


(defmlfun (|partial_function_computation| ml-partial-function-computation)
	  (where) (int -> rule)
    (cons
      (comp-rule 'FIX-COMP where)
      nil
    )
)


;--
;-- Rules for recursive types.
;--



(defmlfun (|recursive_type_equality| ml-recursive-type-equality) (using-terms)
	  ((term list) -> rule)
    (cons
      (equal-intro-rule-recursive
	'EQUAL-INTRO-RECURSIVE
	(mapcar #'prl-term using-terms)
      )
      nil
    )
)



(defmlfun (|simple_rec_equality| ml-simple-rec-equality) (new-id)
	  (tok -> rule)
    (cons (equal-intro-rule-simple-rec
	    'EQUAL-INTRO-SIMPLE-REC
	    new-id)
	  nil))



(defmlfun (|recursive_type_intro| ml-recursive-type-intro) (level)
	  (int -> rule)
  (check-level level '|recursive_type_intro|)
    (cons
      (recursive-intro-rule
	'RECURSIVE-INTRO
	level
      )
      nil
    )
)




(defmlfun (|simple_rec_intro| ml-simple-rec-intro) (level)
	  (int -> rule)
    (check-level level '|simple-rec-intro|)
    (cons (simple-rec-intro-rule
	    'SIMPLE-REC-INTRO
	    level)
	  nil))


(defmlfun (|recursive_type_equality_rec| ml-recursive-type-equality-rec) (level)
	  (int -> rule)
  (check-level level '|recursive_type_equality_rec|)
    (cons
      (equal-intro-rule-level
	'EQUAL-INTRO-REC-MEMBER
	level
	nil
      )
      nil
    )
)



(defmlfun (|simple_rec_equality_element| ml-simple-rec-equality-element) (level)
	  (int -> rule)
    (check-level level '|simple_rec_equality_element|)
    (cons
      (equal-intro-rule-level
	'EQUAL-INTRO-SIMPLE-REC-MEMBER
	level
	nil)
      nil))


(defmlfun (|recursive_type_equality_induction| ml-recursive-type-equality-induction)
	  (level over-ids over-terms using-terms id rec-type)
	  (int -> ((tok list) -> ((term list) -> ((term list) -> (tok -> (term -> rule))))))
  (check-level level '|recursive_type_equality_induction|)
    (cond ((not (equal (length over-ids)  (length over-terms)))
           (breakout evaluation
'|recursive_type_equality_induction: over id and over term lists are not the same length|)
	  )
    )
    (cons
      (equal-intro-rule-rec-ind
	'EQUAL-INTRO-REC-IND
	level
	(mapcar #'(lambda (x y) (cons x (prl-term y))) over-ids over-terms)
	(cons
	  (bound-id-term 'BOUND-ID-TERM nil (list id) (prl-term rec-type))
	  (mapcar #'prl-term using-terms)
        )
      )
      nil
    )
)



(defmlfun (|simple_rec_equality_rec_ind| ml-simple-rec-equality-rec-ind)
	  (level over-id over-term using-term new-ids)
	  (int -> (tok -> (term -> (term -> ((tok list) -> rule)))))
    (check-level level '|simple_rec_equality_rec_ind|)
    (cons
      (equal-intro-rule-simple-rec-ind
	`EQUAL-INTRO-SIMPLE-REC-IND
	level
	(cons over-id (prl-term over-term))
	(prl-term using-term)
	new-ids)
      nil))


(defmlfun (|recursive_type_elim| ml-recursive-type-elim)
	  (hyp level over-ids over-terms using-terms new-ids)
	  (int -> (int -> ((tok list) -> ((term list) -> ((term list) -> ((tok list) -> rule))))))
  (check-level level '|recursive_type_elim|)
    (cond ((not (equal (length over-ids) (length over-terms)))
           (breakout evaluation
'|recursive_type_elim: over id and over term lists are not the same length|)
	  )
    )

    (cons
      (recursive-elim-rule
	'RECURSIVE-ELIM
	hyp
	level
	(mapcar #'(lambda (x y) (cons x (prl-term y))) over-ids over-terms)
	(mapcar #'prl-term using-terms)
	(mapcar #'prl-id new-ids)
      )
      nil
    )
)


(defmlfun (|simple_rec_elim| ml-simple-rec-elim) (assum-num level new-ids)
	  (int -> (int -> ((tok list) -> rule)))
    (check-level level '|simple_rec_elim|)
    (cons
      (simple-rec-elim-rule
	'SIMPLE-REC-ELIM
	assum-num
	level
	new-ids)
      nil))




(defmlfun (|simple_rec_unroll_elim| ml-simple-rec-unroll-elim) (assum-num new-ids)
	  (int -> ((tok list) -> rule))
    (cons
      (simple-rec-unroll-elim-rule
	'SIMPLE-REC-UNROLL-ELIM
	assum-num
	(prl-id (car new-ids)))
      nil))


(defmlfun (|recursive_type_computation| ml-recursive-type-computation) (where)
	  (int -> rule)
    (cons
      (comp-rule
	'REC-IND-COMP where
      )
      nil
    )
)


(defmlfun (|simple_rec_computation| ml-simple-rec-computation) (where)
	  (int -> rule)
    (declare (ignore where))
    (breakout
      evaluation
      '|implementation: not yet, maybe never. Use direct computation.|))




(defmlfun (|dom_computation| ml-dom-computation) (where new-ids)
	  (int -> ((tok list) -> rule))
    (cons
      (dom-comp-rule 'DOM-COMP where (mapcar #'prl-id new-ids))
      nil
    )
)





(defmlfun (|direct_computation| ml-direct-comp) (new-term)
	  (term -> rule)
    (cons (direct-comp-rule 'DIRECT-COMP (prl-term new-term)) nil))


(defmlfun (|direct_computation_hyp| ml-direct-comp-hyp) (assum-num new-term)
	  (int -> (term -> rule))
    (cons (direct-comp-hyp-rule 'DIRECT-COMP-HYP
				assum-num (prl-term new-term))
	  nil))




(defmlfun (|thinning| ml-thinning) (int-list)
	  ((int list) -> rule)
    (cons (thinning-rule 'THINNING int-list)
	  nil))


(defmlfun (|propagate_thinning| ml-propagate-thinning) (hyp-list int-list)
	  ((declaration list) -> ((int list) -> (int list)))
    (propagate-thinning-in-assums$		;written for extractor
	       int-list
	       ()
	       ()
	       1
	       hyp-list))


(defmlfun (|monotonicity| ml-monotonicity) (op hyp1 hyp2)
	  (tok -> (int -> (int -> rule)))
  (let ((monot-op (cdr (assoc op '((+ . PLUS) (- . MINUS) (* . MULT) (/ . DIV))))))
    (if (member monot-op valid-monot-opkinds)
      (ncons (monot-rule 'MONOT monot-op hyp1 hyp2))
      (breakout evaluation (concat '|Bad operator for monotonicity: | op)))))



(dmlc |division| (cons
                     (division-rule 'division)
                     nil
                 ) rule)




;-- 
;-- rule destructors.
;-- 


(defmlfun (|rule_kind| ml-rule-kind) (rule)
	  (rule -> tok)
    (kind-of-rule (car rule))   ;-- first part of rule is the real rule--
                                ;-- not the rule body.
)

(dmlc |object_equality|
      (cons (equal-intro-rule 'EQUAL-INTRO-OBJECT)
	    nil)
      rule)



(defmlfun (|object_equality_member| ml-object-equality-member) (using)
	  (term -> rule)
    (cons
      (equal-intro-rule-using
	'EQUAL-INTRO-OBJECT-MEMBER
	nil
	(prl-term using)
	nil)
      nil))
