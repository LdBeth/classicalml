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


(deftuple rule kind)      ;-- Generic rule.

;-- intro rules


(deftuple int-intro-rule kind selector)       ;-- (INT-INTRO-NUMBER selector)
                                              ;--   where selector is an integer
                                              ;-- (INT-INTRO-OP selector) 
                                              ;--   where selector is TPlus,
                                              ;--   TMinus,TStar,TSlash,or TMod

(deftuple atom-intro-rule kind token-term)    ;-- (ATOM-INTRO token-term) where
                                              ;--   token-term is a token-term

(deftuple less-intro-rule kind)               ;-- (LESS-INTRO)

(deftuple list-intro-rule kind level)         ;-- (LIST-INTRO-NIL level) or
                                              ;-- (LIST-INTRO-CONS nil)    
                                              ;-- level is a universe level

(deftuple union-intro-rule kind level selector) ;-- (UNION-INTRO level selector)
                                                ;--  level is a universe level 
                                                ;--  (one that the union term will
                                                ;--  be shown to inhabit.)
                                                ;--  selector is Tleft or Tright                                               

(deftuple product-intro-rule kind level leftterm new-id) 
                                              ;-- (PRODUCT-INTRO level leftterm)
                                              ;-- level is like in union intro.
                                              ;-- leftterm is a member of the
                                              ;-- lefttype of the goal (which 
                                              ;-- is a product term)             
                                              ;-- if goal does not have a bound-
                                              ;-- id the level,leftterm,new-id
                                              ;-- fields must be nil

(deftuple function-intro-rule kind level new-id)
                                              ;-- (FUNCTION-INTRO level)
                                              ;-- level is like in union intro.
                                              ;-- new-id may be nil

(deftuple quotient-intro-rule kind level)     ;-- (QUOTIENT-INTRO level)

(deftuple recursive-intro-rule kind level)    ;-- (RECURSIVE-INTRO level)

(deftuple simple-rec-intro-rule kind level)   ;-- (SIMPLE-REC-INTRO level)

(deftuple set-intro-rule kind level leftterm new-id) 
                                              ;-- (SET-INTRO level leftterm new-id)
                                              ;-- level is like in union intro.
                                              ;-- leftterm is a member of the
                                              ;-- lefttype of the goal (which 
                                              ;-- is a set term)             
                                              ;-- if goal does not have a bound-
                                              ;-- id the level,leftterm
                                              ;-- fields must be nil.

(deftuple univ-intro-rule kind)  ;-- kind is UNIVERSE-INTRO-x where x is one 
                                 ;-- of ATOM,INT,VOID,UNION,LESS, LIST

(deftuple univ-intro-rule-equal kind type num-terms) ;-- (UNIVERSE-INTRO-EQUAL
                                                     ;--      type num-terms)
                                                     ;-- type is a term that is
                                                     ;-- to be the type of the 
                                                     ;-- equal term being
                                                     ;-- introduced. num-terms
                                                     ;-- is the arity of the 
                                                     ;-- of the equal term and
                                                     ;-- must be greater than 0.

(deftuple univ-intro-rule-function kind id type)  ;-- (UNIVERSE-INTRO-FUNCTION
                                                  ;--                   id type)
                                                  ;-- id,type are either both
                                                  ;-- nil or both non-nil

(deftuple univ-intro-rule-product kind id type)   ;-- (UNIVERSE-INTRO-PRODUCT
                                                  ;--                   id type) 
                                                  ;-- id,type are either both
                                                  ;-- nil or both non-nil

(deftuple univ-intro-rule-quotient kind term term2 new-ids)
                                                  ;-- kind is 
                                                  ;--   UNIVERSE-INTRO-QUOTIENT
                                                  ;-- the terms may not be nil
                                                  ;-- new-ids must be length 3

(deftuple univ-intro-rule-set kind id type)       ;-- kind is UNIVERSE-INTRO-SET
                                                  ;-- id and type are either 
                                                  ;-- both nil or both non-nil.

(deftuple univ-intro-rule-universe kind level)    ;-- (UNIVERSE-INTRO-UNIVERSE
                                                  ;--                    level)

(deftuple equal-intro-rule kind)   ;-- kind is EQUAL-INTRO-* where * is one of
                                   ;-- AXIOM-LESS, AXIOM-EQUAL,
                                   ;-- EQUAL,LESS,VOID,ANY,INT,UNIVERSE,
                                   ;-- ATOM,TOKEN,LIST,UNION, CONS, POS-NUMBER
                                   ;-- MINUS,ADD, SUB, MUL, DIV, ATOMEQ, INTEQ
                                   ;-- INTLESS, VAR 

(deftuple equal-intro-rule-new-id kind new-id)   ;-- kind is EQUAL-INTRO-PRODUCT
                                                 ;-- EQUAL-INTRO-FUNCTION, or
                                                 ;-- EQUAL-INTRO-SET
                                                 ;-- EQUAL-INTRO-PARFUNCTION
                                                 ;-- new-id may be nil

(deftuple equal-intro-rule-quotient kind new-ids) 
                                                 ;-- kind is EQUAL-INTRO-QUOTIENT
                                                 ;-- length of new-ids is 2

(deftuple equal-intro-rule-fix kind level using-term-list new-ids)
						;-- kind is EQUAL-INTRO-FIX

(deftuple equal-intro-rule-recursive kind using-term-list)
						;-- kind is EQUAL-INTRO-RECURSIVE

(deftuple equal-intro-rule-simple-rec kind new-id)
                                                ;-- kind is EQUAL-INTRO-SIMPLE-REC

(deftuple equal-intro-rule-rec-ind kind level over-pair-list using-term-list )
                                                ;--kind is EQUAL-INTRO-REC-IND

(deftuple equal-intro-rule-simple-rec-ind kind level over-pair using-term new-ids)
						;-- kind is EQUAL-INTRO-SIMPLE-REC-IND

(deftuple equal-intro-rule-level kind level new-id) 
                                              ;-- level is a universe level
                                              ;-- kind is EQUAL-INTRO-* with *
                                              ;-- one of INL,INR,PAIR,LAMBDA,
					      ;-- REC-MEMBER, SIMPLE-REC-MEMBER
                                              ;-- NIL,SET-ELEM, or QUOTIENT-ELEM
                                              ;-- new-id may be nil

(deftuple equal-intro-rule-over kind over-pair new-ids)   
                                             ;-- over-pair is nil
                                             ;-- or pair dotted pair - (id.term)
                                             ;-- new-ids is a list of ids
                                             ;-- nil or length 2 for ind
                                             ;-- kind is EQUAL-INTRO-IND

(deftuple equal-intro-rule-using kind over-pair using-term new-ids)
                                             ;-- new-ids is 
                                             ;-- nil or length 3 for list-ind
                                             ;-- as above except using-term
                                             ;-- is a term. kind is EQUAL-INTRO-
                                             ;-- DECIDE,EQUAL-INTRO-SPREAD,
					     ;-- EQUAL-INTRO-APPLY-PARTIAL,
                                             ;-- EQUAL-INTRO-APPLY,
                                             ;-- EQUAL-INTRO-LIST-IND or
					     ;-- EQUAL-INTRO-DOM
                                             ;-- new-ids is nil or length 2 for
                                             ;-- decide and spread, nil or 
                                             ;-- length 1 for apply
                                             ;-- using term is a union-term for
                                             ;-- decide,product-term for spread,
                                             ;-- function-term for apply.

   
;-- elim rules

(deftuple int-elim-rule kind assum-num new-ids)
(deftuple list-elim-rule kine assum-num new-ids)
(deftuple void-elim-rule kind assum-num)
(deftuple union-elim-rule kind assum-num new-ids)
(deftuple product-elim-rule kind assum-num new-ids)
(deftuple function-elim-rule kind assum-num leftterm new-ids)
(deftuple parfunction-elim-rule kind assum-num leftterm new-ids)
(deftuple quotient-elim-rule kind assum-num level new-ids)
(deftuple set-elim-rule kind assum-num level new-ids)
(deftuple recursive-elim-rule
	  kind assum-num level over-pair-list using-term-list new-ids
)
(deftuple simple-rec-elim-rule kind assum-num level new-ids)
(deftuple recursive-unroll-elim-rule kind assum-num level new-ids)	
(deftuple simple-rec-unroll-elim-rule kind assum-num new-id)

;(zl:comment                                                        
;    (deftuple int-elim-rule kind assum-num new-id1 new-id2) ;-- assum-num is the
;                                                        ;-- index of the 
;                                                        ;-- assum being elim-med.
;                                                        ;-- kind is INT-ELIM
;                                                        ;-- new-id1 may not be 
;                                                        ;-- nil. new-id2 is nil
;                                                        ;-- iff the id of the
;                                                        ;-- assum being elimmed
;                                                        ;-- does not occur free
;                                                        ;-- in any assumptions
;                                                        ;-- occurring further to
;                                                        ;-- the right.
;
;    (deftuple list-elim-rule kind assum-num new-id1 new-id2 new-id3) 
;                                                  ;-- kind is LIST-ELIM
;                                                  ;-- new-id1 and new-id2 may
;                                                  ;-- not be nil. new-id3 is 
;                                                  ;-- nil iff ..(as in int-elim)
;
;    (deftuple void-elim-rule kind assum-num)   ;-- (VOID-ELIM assum-num) 
;
;    (deftuple union-elim-rule kind assum-num new-id1 new-id2 new-id3) 
;                                           ;-- (UNION-ELIM assum-num new-id1
;                                           ;--   new-id2)
;                                           ;--  where assum-num is as in void
;                                           ;--  elim. new-id1 and new-id2 may
;                                           ;--  not be nil if the id of the
;                                           ;--  assum being elimmed occurs
;                                           ;--  free in the conclusion. 
;                                           ;--  new-id1,new-id2 always both
;                                           ;--  nil or both non-nil. new-id3
;                                           ;--  may be non-nil only if 1,2 are
;                                           ;--  non-nil.
;
;    (deftuple product-elim-rule kind assum-num new-id1 new-id2 new-id3)
;                                           ;-- (PRODUCT-ELIM assum-num new-id1 
;                                           ;--   new-id2 new-id3)
;                                           ;-- new-id1,new-id2 may not be nil
;                                           ;-- if the id of the assum being
;                                           ;-- elimmed occurs free in the concl.
;                                           ;-- other restrictions on the ids
;                                           ;-- are as for union elim.
;
;    (deftuple function-elim-rule kind assum-num leftterm new-id new-id2)
;                                          ;-- (FUNCTION-ELIM assum-num leftterm new-id new-id2)
;                                          ;--  where leftterm is in the lefttype
;                                          ;--  of the term being elim-ed   
;                                          ;-- leftterm,new-id may not be nil
;                                          ;-- if the id of the assum being
;                                          ;-- elimmed occurs free in the concl.
;                                          ;-- new-id2 may be non-nil of if 
;                                          ;-- new-id is non-nil.
;
;
;    (deftuple quotient-elim-rule kind assum-num level new-ids) 
;                                          ;-- kind is QUOTIENT-ELIM
;                                          ;-- new-ids must be of length 2
;
;    (deftuple set-elim-rule kind assum-num level new-id)  ;-- kind is SET-ELIM
;                                                      ;-- new-id may not be nil.
;  
;)
;-- computation rules

(deftuple comp-rule kind where)
                ;-- Kind is one of
                ;-- APPLY-COMP
                ;-- SPREAD-COMP
                ;-- DECIDE-COMP
                ;-- IND-COMP-DOW
                ;-- IND-COMP-BASE
                ;-- IND-COMP-UP
                ;-- LIST-IND-COMP
                ;-- ATOMEQ-COMP-TRUE
                ;-- ATOMEQ-COMP-FALSE
                ;-- INTEQ-COMP-TRUE
		;-- INTEQ-COMP-FALSE
                ;-- INTLESS-COMP-TRUE
                ;-- INTLESS-COMP-FALSE
		;-- FIX-COMP
		;-- REC-IND-COMP
                ;-- SIMPLE-REC-IND-COMP
                ;-- where: index of the term being reduced among the terms of 
                ;--        the equality term

(deftuple dom-comp-rule kind where new-ids)
(deftuple direct-comp-rule kind using-term)
(deftuple direct-comp-hyp-rule kind assum-num using-term)


;-- other rules

(deftuple hyp-rule kind assum-num)         ;-- (HYP assum-num) where assum-num
                                           ;--  indicates an assumption whose
                                           ;--  type is equal to the conclusion

(deftuple lemma-rule
    kind                ;-- LEMMA
    lemma               ;-- lib name of theorem being referenced (an atom)
    new-id              ;-- may be nil.
    assum-map           ;;; not used
    conclusion-match    ;;; not used
)

(deftuple def-rule kind theorem new-id) ;-- (DEF theorem new-id)
                                        ;-- where theorem is the lib name of
                                        ;-- the theorem being referenced.
                                        ;-- new-id may be nil.

(deftuple sequence-rule kind terms new-ids) ;-- (SEQUENCE terms new-ids)
                                            ;-- terms and new-ids are simply
                                            ;-- lists of terms and ids, 
                                            ;-- respectively. 
                                            ;-- new-ids is either nil or the same
                                            ;-- length as terms.
                                            

(deftuple explicit-intro-rule kind term)    ;-- (EXPLICIT-INTRO term) where term
                                            ;--  is the term being introduced

(deftuple cumulativity-rule kind level)     ;-- (CUMULATIVITY level) where level
                                            ;-- is a universe level

(deftuple equality-rule kind)               ;-- (EQUALITY)
    
(deftuple substitute-rule kind level equality-term bound-id-term) 
                                            ;-- kind is SUBSTITUTE        
                                            ;-- the number of bound ids in
                                            ;-- the bound-id-term must be
                                            ;-- equal to the length of 
                                            ;-- (terms-of-equal-term 
                                            ;--                equality-term)

(deftuple arith-rule kind level)            ;-- (ARITH level)
                                            ;-- level is a universe level

(deftuple extensionality-rule kind level using-terms new-id) 
;(deftuple extensionality-rule kind new-id)

(deftuple thinning-rule kind assum-num-list)	; (THINNING assum-num-list)

(deftuple because-rule kind)                ;-- (BECAUSE)

(deftuple experimental-rule 
     kind                   ;-- EXPERIMENTAL
     subgoal-calculation    ;-- Name of ml function that calculates subgoals.
     extraction-calculation ;-- Field not yet used.
)

(deftuple tactic-rule
    kind                ;-- TACTIC
    tactic-body         ;-- the Ttree rule body of the tactic --
                        ;--   that which would lead the rule parser to
                        ;--   reconstruct this TACTIC rule.
    proof-top           ;-- the proof top produced by the tactic,
                        ;--   its unrefined subgoals (in left to right
                        ;--   order at the frontier) are the children
                        ;--   of this level.

)

(deftuple monot-rule
    kind                ;-- MONOT
    op                  ;-- one of 'PLUS, 'MINUS, 'MULT or 'DIV
    hypnum1
    hypnum2             ;-- hyp numbers of relevant hypotheses
)





(deftuple division-rule kind)     ; (DIVISION)





;;; make-rule is a macro which allows (relatively) easy
;;; definition of new rules.  The commented-out application after 
;;; make-rule's definition gives an example of the macros use.  
;;; A rule constructed using this macro should be compiled in the
;;; context of Nuprl's macros, and loaded after Nuprl has been loaded
;;; since the rule's definition involves the destructive modification of
;;; some of Nuprl's run-time structures (e.g., rule-to-tree-table).

(defmacro make-rule

	  (rule-name				;The rule kind,
						;the prefix of the name of the rule
						;tuple constructor (suffix is "-rule"),
						;first word of the rule invocation, name
						;of ML rule constructor.

	   field-names-of-rule-def		;excluding the "kind" field

	   parse-function-body			;returns rule

	   refinement-function-body		;returns no value

	   extraction-function-body		;arguments bound to pt,
						;rule, assum-map

	   rule-to-Ttree-action-list		

	   type-of-ML-constructor

	   ML-constructor-checks		;a lambda form.
						;body forms are checks.  rule constructing
						;form is computed from lambda-list.
	   )

  ;; Check that symbol args are really symbols.
  (mapc #'(lambda (x y)
	    (cond ((not (symbolp x))
		   (error "~a~^ ~a" y " must be a symbol"))))
	(list rule-name rule-name
	      rule-name)
	'("rule-name" "rule-name"
		    "rule-name"))
  ;; Check that list args are really lists.
  (mapc #'(lambda (x y)
	    (cond ((not (consp x))
		   (error "~a~^ ~a"  y " must be a list"))))
	(list field-names-of-rule-def parse-function-body refinement-function-body
	      extraction-function-body rule-to-Ttree-action-list
	      type-of-ML-constructor ML-constructor-checks)
       '("field-names-of-rule-def" "parse-function-body" "refinement-function-body"
			     "extraction-function-body" "rule-to-Ttree-action-list"
			     "type-of-ML-constructor" "ML-constructor-checks"))
  (cond ((not (eql 'LAMBDA (car ML-constructor-checks)))
	 (error "~a~^ ~a" "ML-constructor-definition must be a lambda-form")))
  (let* ((internal-rule-name (intern (string-upcase (string rule-name)) (find-package 'nuprl)))
	 (constructor-name (build-name "" internal-rule-name "-RULE")))
    `(progn
       (eval-when (load eval compile)
	 (deftuple ,constructor-name
		   kind ,@field-names-of-rule-def))
       (defun ,(build-name "PARSE-" internal-rule-name "-RULE")
	      ()
	 ,parse-function-body)
       (setf (get ',rule-name 'parse-function)
	     ',(build-name "PARSE-" internal-rule-name "-RULE"))
       (defun ,(build-name "REFINE-" internal-rule-name "")
	      ()
	 ,refinement-function-body)
       (setf (get ',internal-rule-name 'ref-function)
	     ',(build-name "REFINE-" internal-rule-name ""))
       (let* ((x (assoc ',internal-rule-name rule-to-ttree-table)))
	 (cond (x (setf (cdr x) ',rule-to-ttree-action-list))
	       (t (setf (cdr (last rule-to-ttree-table))
			(list (cons ',internal-rule-name ',rule-to-ttree-action-list))))))
       (defun ,(build-name "EXT-" internal-rule-name "")
	      (pt rule assum-map)
	 ,extraction-function-body)
       (setf (get ',internal-rule-name 'extract-fcn)
	     ',(build-name "EXT-" internal-rule-name ""))
       (defmlfun ,rule-name
		 ,(second ML-constructor-checks)
		 ,type-of-ML-constructor
	 (progn ,@(cddr ML-constructor-checks))
	 (cons (,constructor-name ',internal-rule-name ,@(second ML-constructor-checks))
	       nil))))) 

;;; Note: pay attention to case in string arguments.
(defun build-name (prefix-string symbol suffix-string)
  (intern (concatenate 'string prefix-string (symbol-name symbol) suffix-string)
	  (find-package 'nuprl)))


;(make-rule
;  c
;  (level)
;  |c|
;  (let* ((r (parse-cumulativity-rule)))
;    (c-rule 'C (cadr r)))
;  (progn
;    (let* ((ref-rule (cumulativity-rule 'CUMULATIVITY (level-of-c-rule ref-rule))))
;      (refine-cumulativity)))
;  (ext-equal-intro pt rule assum-map)
;  ((L |c |) (2 U))
;  |moose_and_owl|
;  (int -> rule)
;  (lambda (n) (cons (c-rule 'c n) nil)))



;;; Old version.
;(defmacro make-rule
;
;	  (rule-name				;doubles as the rule kind
;						;and the prefix of the name of the
;						;tuple constructor (suffix is "-rule").
;
;	   field-names-of-rule-def		;excluding the "kind" field
;
;	   first-word-in-rule-invocation
;
;	   parse-function-body			;returns rule
;
;	   refinement-function-body		;returns no value
;
;	   extraction-function-body		;arguments bound to pt,
;						;rule, assum-map
;
;	   rule-to-Ttree-action-list		
;
;	   name-of-uncurried-ML-rule-constructor
;
;	   type-of-ML-constructor
;
;	   ML-constructor-definition		;a lambda form.
;						;remember that ml-rules are
;						;rule . rule-body 
;	   )
;
;  ;; Check that symbol args are really symbols.
;  (mapc #'(lambda (x y)
;	    (cond ((not (symbolp x))
;		   (error "~a~^ ~a" y " must be a symbol"))))
;	(list rule-name first-word-in-rule-invocation
;	      name-of-uncurried-ML-rule-constructor)
;	'("rule-name" "first-word-in-rule-invocation"
;		    "name-of-uncurried-ML-rule-constructor"))
;  ;; Check that list args are really lists.
;  (mapc #'(lambda (x y)
;	    (cond ((not (consp x))
;		   (error "~a~^ ~a"  y " must be a list"))))
;	(list field-names-of-rule-def parse-function-body refinement-function-body
;	      extraction-function-body rule-to-Ttree-action-list
;	      type-of-ML-constructor ML-constructor-definition)
;       '("field-names-of-rule-def" "parse-function-body" "refinement-function-body"
;			     "extraction-function-body" "rule-to-Ttree-action-list"
;			     "type-of-ML-constructor" "ML-constructor-definition"))
;  (cond ((not (eql 'LAMBDA (car ML-constructor-definition)))
;	 (error "~a~^ ~a" "ML-constructor-definition must be a lambda-form")))
;  `(progn
;     (eval-when (load compile eval)
;       (deftuple ,(build-name "" rule-name "-RULE")
;		 kind ,@field-names-of-rule-def))
;     (defun ,(build-name "PARSE-" rule-name "-RULE")
;	    ()
;       ,parse-function-body)
;     (setf (get ',first-word-in-rule-invocation
;	      'parse-function) ',(build-name "PARSE-" rule-name "-RULE"))
;     (defun ,(build-name "REFINE-" rule-name "")
;	    ()
;       ,refinement-function-body)
;     (setf (get ',rule-name
;	      'ref-function) ',(build-name "REFINE-" rule-name ""))
;     (let* ((x (assoc ',rule-name rule-to-ttree-table)))
;       (cond (x (setf (cdr x) ',rule-to-ttree-action-list))
;	     (t (setf (cdr (last rule-to-ttree-table))
;		      (list (cons ',rule-name ',rule-to-ttree-action-list))))))
;     (defun ,(build-name "EXT-" rule-name "")
;	    (pt rule assum-map)
;       ,extraction-function-body)
;     (setf (get ',rule-name
;	      'extract-fcn) ',(build-name "EXT-" rule-name ""))
;     (defun ,(build-name "ML-" name-of-uncurried-ML-rule-constructor "")
;	    ,@(cdr ML-constructor-definition))
;     (dml ,name-of-uncurried-ML-rule-constructor
;	  ,(length (second ML-constructor-definition))
;	  ,(build-name "ML-" name-of-uncurried-ML-rule-constructor "")
;	  ,type-of-ML-constructor)))

