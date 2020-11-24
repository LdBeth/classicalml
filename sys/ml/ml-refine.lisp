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
;-- This file contains the implementation
;-- of the refine primitive.  Following this are some functions
;-- for manipulating declarations, proofs, the auto tactic, and substitutions.


(declaim (special %val AUTO-TACTIC))

(defmacro assign-variable (var val typ)
  `(progn
     (set ,var ,val)
     (setf (get ,var 'mldescriptor) (list ,var 'VALUE ,var))
     (setf (get ,var 'mltype) ,typ)))


(defun apply-tactic (ptree tactic-rep)
  (assign-variable '|prlgoal| ptree '(mk-prooftyp))
  (let ((rslt (ML (make-tactic-call tactic-rep))))
    (if (equal (car rslt) 'SUCCESS) 
	(cons 'SUCCESS %val)  ;-- %val is ML global containing current
                              ;-- value.
	rslt)))


(defparameter *void-goal-proof*
	      (proof-tree
		nil				;-- assumptions
		(void-term 'VOID nil)		;-- void goal, nil Ttree rep.
		'(TTREE 0)			;-- body of rule
		nil				;-- rule
		nil				;-- children
		'INCOMPLETE			;-- status
		nil				;-- list of hidden assumptions
		))


(setf (get '|new_id_initialized| 'refvar) t)
(setf (get '|new_id_count| 'refvar) t)
(assign-variable '|new_id_initialized| nil '(mk-booltyp))
(assign-variable '|new_id_count| 0 '(mk-inttyp))
(assign-variable '|prlgoal| *void-goal-proof* '(mk-prooftyp))

;;; The following are ML functions for historical reasons only.
(defmlfun |initialize_tactics| (foo) (void -> bool)
  (assign-variable '|new_id_initialized| nil '(mk-booltyp))
  nil)

(defmlfun |applytac| (tactic-result) ( ((proof list) |#| ((proof list) -> proof)) -> proof )
  (ap (cdr tactic-result)
      (car tactic-result)))

;-- The call produced is:
;--  
;--  "initialize_tatics (); applytac ((tactic-rep) prlgoal);;<nl>"
;-- 

(defun make-tactic-call (tactic-rep)
    (cons 'Ttree                ;-- this object is a Ttree.  
        (append (istring '|initialize_tactics (); applytac ((|)
            (cdr tactic-rep)         ;-- strip off the first Ttree marker.
            (istring '|) prlgoal);;|)
            (list 10.)          ; return character (new-line)
        )
    )
)


;--
;-- check that corresponding entries in lists are a-equal declarations.
;--

(defun a-equal-decl-lists (hyp1 hyp2)
    (cond
      ((null hyp1) (null hyp2))
      ((null hyp2) nil)    ;-- wrong length
      ((and
       (eql (id-of-declaration (car hyp1)) (id-of-declaration (car hyp2)))
       (equal-terms (type-of-declaration (car hyp1))  (type-of-declaration (car hyp2)))
       (a-equal-decl-lists (cdr hyp1) (cdr hyp2))
       )
      )
    )
)



;--
;-- check for alpha equality of sequents.
;--

(defun equal-sequent (seq1 seq2)
  (and
    (or (eql (assumptions-of-proof-tree seq1)
	    (assumptions-of-proof-tree seq2))
	(a-equal-decl-lists
	  (assumptions-of-proof-tree seq1)
	  (assumptions-of-proof-tree seq2)))
    (equal-terms (conclusion-of-proof-tree seq1)
		 (conclusion-of-proof-tree seq2))
    ;; 2-2-89! then 5-4-89 equal -> not set-xor
    (not (set-exclusive-or (hidden-of-proof-tree seq1) (hidden-of-proof-tree seq2) :test #'eql))))

;-- Verify that the achievement proofs match the children of the orignal
;-- proof.

(defun equal-sequent-list (children-list achievement-list)     
    (cond
        ((null children-list) (null achievement-list))
	((null achievement-list) nil)  ;-- wrong number of achievements
        ((and
	   (equal-sequent (car children-list) (car achievement-list))
	   (equal-sequent-list (cdr children-list) (cdr achievement-list))
	  )
	)
    ) 
)


;-- The body passed in will either be a real rule body, or a nil.  If
;-- real, use it.  If not, call the prl function rule-to-Ttree to calculate
;-- the body based upon the rule representation.

(defun get-rule-body (body rule)
    (cond 
        (body (copy body))                   ;-- if non-nil body, return a copy of it.
        (t (rule-to-Ttree rule))
    )
)

(defun make-result (rule ptree  ptree-list)
  (cons ptree-list (make-validation rule ptree ptree-list)))


;-- Make an ML closure that builds a proof tree given the goal list.
;-- The rule is the refinement rule being applied.  The variable ptree
;-- is the goal.  The ptree-list is the list of children returned by 
;-- deduce-children.

(defun make-validation (rule ptree ptree-list)
  (make-closure
    #'(lambda (achievement)
	(if (equal-sequent-list ptree-list achievement)
	    (progn
	      (<- (children-of-proof-tree ptree) achievement)
	      (<- (rule-of-proof-tree ptree) (car rule))
	      (<- (rule-body-of-proof-tree ptree)
                  (get-rule-body (cdr rule) (rule-of-proof-tree ptree)))
	      (<- (status-of-proof-tree ptree)
                  (calculate-status-from-children achievement))
	      ptree)
	    (breakout evaluation
	      '|refine: validation achievements do not match subgoals|)))
    1))

;--  Main refinement function.
;-- This functions is curried as part of the ml library.  It turns out to
;-- be hard to write primitive curried functions.  
;-- The result is of one of the following forms:
;-- (SUCCESS.(rule.children))    or
;-- (FAILURE.message).  This is necessary since refining by a tactic
;-- rule potentially changes the rule (i.e., it includes the proof-top
;-- in the rule.

(defmlfun (|refine| ml-refine) (rule ptree)
	  (rule -> (proof -> ((proof list) |#| ((proof list) -> proof))))
  (let ((result (deduce-children ptree (car rule))))
    (if (eql (car result) 'SUCCESS)
	(make-result
	  (cons (cadr result) (cdr rule))
	  ptree
	  (cddr result))
	(breakout evaluation (concat '|refine: | (cdr result))))))


;;; It is assumed here that the mechanisms for grafting tactic results
;;; into proofs will do the copying necessary to prevent ted from having
;;; illegal side effects.
(defun make-frontier-validation (pf leaves)
  (flet ((rebuild-proof (pf leaf-extensions)
	   (labels
	     ((rebuild-proof-aux (pf)
		(cond
		  ((and (null (children-of-proof-tree pf))
			(eql (status-of-proof-tree pf) 'COMPLETE))
		   pf)
		  ((null (children-of-proof-tree pf))
		   (prog1 (car leaf-extensions)
			  (setq leaf-extensions (cdr leaf-extensions))))
		  (t
		   (let* ((rebuilt-children
			    (mapcar #'rebuild-proof-aux (children-of-proof-tree pf)))
			  (copied-pf (copy-list pf)))
		     (setf (children-of-proof-tree copied-pf) rebuilt-children)
		     (setf (status-of-proof-tree copied-pf)
			   (calculate-status-from-children rebuilt-children))
		     copied-pf)))))
	     (rebuild-proof-aux pf))))
    (make-closure
      #'(lambda (achievement)
	(if (equal-sequent-list achievement leaves)
	    (rebuild-proof pf achievement)
	    (breakout evaluation '|frontier|)))
      1)))

(defmlfun (|frontier| ml-frontier) (pf)
	  (proof -> ((proof list) |#| ((proof list) -> proof)))
  (labels (;; collect in reverse order
	   (collect-leaves (pf-list leaves-to-the-left)
	     (cond ((null pf-list)
		    leaves-to-the-left)
		   ((eql (status-of-proof-tree (car pf-list)) 'COMPLETE)
		    (collect-leaves (cdr pf-list) leaves-to-the-left))
		   ((null (children-of-proof-tree (car pf-list)))
		    (collect-leaves
		      (cdr pf-list)
		      (cons (car pf-list) leaves-to-the-left)))
		   (t
		    (collect-leaves
		      (cdr pf-list)
		      (collect-leaves (children-of-proof-tree (car pf-list))
				      leaves-to-the-left))))))
    (let* ((leaves (mapcar #'copy-proof (reverse (collect-leaves (list pf) ())))))
      (cons leaves (make-frontier-validation pf leaves)))))

;-- allow auto tactics to be changed       



(defmlfun (|set_auto_tactic| ml-set-auto-tactic) (tactic-name) (tok -> void)
    (setq AUTO-TACTIC `(Ttree ,@(istring tactic-name)))
)

(defmlfun (|show_auto_tactic| ml-show-auto-tactic) (x) (void -> tok)
    (declare (ignore x))
    (implode (cdr AUTO-TACTIC)))

(ml-set-auto-tactic  '|\\p. [p],hd|)


;-- 
;-- constructors and destructors for declarations.
;-- 

(defmlfun (|destruct_declaration| ml-destruct-declaration) (decl)
	  (declaration -> (tok |#| term))
    (cons
        (id-of-declaration decl)
        (ml-term (type-of-declaration decl))
    )
)



(defmlfun (|make_declaration| ml-make-declaration) (id type)
	  (tok -> (term -> declaration))
    (declaration nil id (prl-term type)) ;-- nil Ttree field
)



;-- 
;-- Constructor of degenerate proof with ">> void" as the goal.
;-- 

(dmlc |void_goal_proof|
      *void-goal-proof*
      proof)

;-- 
;-- destructors for proofs
;-- 



(defmlfun (|hypotheses| ml-hypotheses) (proof)
	  (proof -> (declaration list))
    (assumptions-of-proof-tree proof)
)

(defmlfun (|conclusion| ml-conclusion) (proof-tree) (proof -> term)
    (ml-term
        (conclusion-of-proof-tree proof-tree)
    )
)

;-- return refinement rule.  Fail if no rule.

(defmlfun (|refinement| ml-refinement-rule) (proof-tree) (proof -> rule)
    (cond ((rule-of-proof-tree proof-tree)  ;-- non-nil if good.
              (cons
                  (rule-of-proof-tree proof-tree)
                  (rule-body-of-proof-tree proof-tree)
              )
          )
        (t (breakout evaluation '|refinement_rule: no rule in proof|))
    )
)

;-- return list of children of refinement.  Fail if no refinement.

(defmlfun (|children| ml-children) (proof-tree) (proof -> (proof list))
    (cond ((rule-of-proof-tree proof-tree) ;-- non-nil if a refinement
              (children-of-proof-tree proof-tree) ;-- return children
          )
        (t (breakout evaluation '|children: no refinement.|))
    )
)





;--
;-- Convert a ML substitution to a substitution for the PRL substitution 
;-- function.  The PRL function wants something that is of the form
;--      ((id1 term1) ... (idn termn))   whereas the ML function will
;-- take a substitution of the form
;--      ((var1.term1) ... (varn.termn)).  Note that id is just an atom
;-- but var is a variable term.  Also note the the ML terms will have to
;-- be coerced into prl terms.  See the note on representing PRL terms above.
;--

(defun prl-substitution (sub-list)
    (mapcar
     #'(lambda (sub-pair)
	 (cond ((not
		 (equal (ml-term-kind (car sub-pair)) 'VAR)
                 )
		(breakout evaluation
			  '|substitute: object to substitute for is not a variable term.|)
                )
	       )         
	 (list
	  (id-of-var-term (prl-term (car sub-pair)))
	  (prl-term (cdr sub-pair))
          )
	 )
      sub-list
    )
)

;--
;-- ML subroutine for substituting for variables in terms.
;--


(defmlfun (|substitute| ml-substitute) (term sub)
	  (term -> (((term |#| term) list) -> term))
  (ml-term
    (substitute
      (prl-term term)				;-- the term.
      (prl-substitution sub)			;-- the substitution.
      )
    )
  )


(defmlfun (|replace| ml-replace) (term sub)
	  (term -> (((term |#| term) list) -> term))
    (ml-term
      (substitute-with-capture
        (prl-term term)           ;-- the term.
        (prl-substitution sub)   ;-- the substitution.
      )
    )
)


(defmlfun (|top_def_of_term| ml-def-name) (term) (term -> tok)
  (breakout evaluation '|top_def_of_term: no longer implemented.|))

(defun check-library-membership (name kind)
  (cond ((or (not (is-lib-member name))
	     (not (eql (sel (object (library-object name)) kind)
		      kind)))
	 (breakout evaluation
		   (concat '|Object named "| name '|" not in library or is of wrong kind.|)))))

;;; Define an ML primitive which given a def name returns the number of
;;; formal parameters in the def's left hand side.

(defmlfun (|arity_of_def| arity-of-def) (name) (tok -> int)
    (check-library-membership name 'DEF)
    (sel (definition-object
	   (sel (object (library-object name))
		value))
	 num-formals))



(defmlfun (|formal_list_of_def| formal-list-of-def) (name)
	  (tok -> (tok list))
  (check-library-membership name 'DEF)
  (cdr (mapcar #'(lambda (x) (car (mapcar #'(lambda (x) (implode x)) (coerce x 'list))))
	       (coerce (sel (definition-object
				 (sel (object (library-object name)) value))
			       formal) 'list))))

(defmlfun (|rhs_formal_occurrences_of_def| rhs-formal-occurrences-of-def) (name)
	  (tok -> (tok list))
  (check-library-membership name 'DEF)
  (labels ((remaining-occurrences (ones-so-far Ttree-suffix)
	     (cond ((null Ttree-suffix)
		    ones-so-far)
		   (t
		    (let* ((l (car Ttree-suffix))
			   (ones-so-far (cond ((not (consp l))
					       ones-so-far)
					      ((eql (car l) 'FORMAL)
					       (cons (cadr l) ones-so-far))					       
					      (t
					       (remaining-occurrences ones-so-far (cdr l))))))
		      (remaining-occurrences ones-so-far (cdr Ttree-suffix)))))))
    (reverse (remaining-occurrences
	       ()
	       (sel (definition-object
		      (sel (object (library-object name)) value))
		    rhs)))))


;;;  Define an ML primitive which instantiates a def; i.e., which given
;;;  a def name, textually instantiates the def with the print-representation
;;;  of the supplied terms and parses, failing if the def is not in the library, if
;;;  the parse fails, or if the term list is not exactly the right length.

(defmlfun (|instantiate_def| ml-instantiate-def) (name ml-term-list)
	  (tok -> ((term list) -> term))
    (Pif (or (not (lib-member name))
	    (not (eql 'COMPLETE
		     (sel (object (library-object name)) status)))
	    (not (eql (length ml-term-list)
		      (arity-of-def name))))
	--> (breakout evaluation (concat '|instantiate_def: no such def | name))  ||
	t
	--> (Plet (x (catch
		      'process-err
		      (ml-term
			(parse
			  `(TTREE
			     (,name
			      ,@(mapcar #'(lambda (x) (term-to-Ttree (prl-term x)))
					ml-term-list)))))))
	      (flush-scanner-input)
		 (Pif (or (eql (first x) 'ERR))
		     --> (breakout evaluation
				   (concat '|instantiate_def failed to parse | name))  ||
		     t
		     --> x fi)) fi))



(dml |copy_proof| 1 copy-proof (proof -> proof))
;--
;-- functions to get and set assum-num field of ELIM and HYP rules
;--


(defmlfun (|get_assum_number| ml-get-assum-number) (rule) (rule -> int)
    (assum-num-of-hyp-rule (car rule))   ;-- ignore the rule body.
        ;-- use fact that all assum numbers are in same position in rules
)


(defmlfun (|set_assum_number| ml-set-assum-number) (rule assum-number)
	  (rule -> (int -> rule))
  (cons
    (Plet (new-rule (copy (car rule))
         )

        (<- (assum-num-of-hyp-rule new-rule) assum-number)
            ;-- use fact that all assum numbers are in same position in rules
        new-rule
    )
    nil  ;-- no rule body since the body has changed.
  )
)


;--
;-- rule parser: lets ML users invoke the Prl rule parser     
;--



(defmlfun (|parse_rule_in_context| ml-parse-rule) (rule-body-token proof)
	  (token -> (proof -> rule))
  (cons

    (Plet (rule      nil
          new-proof (proof-tree
                        (assumptions-of-proof-tree proof)
                        (conclusion-of-proof-tree proof)
                        (cons 'Ttree (istring rule-body-token))
                        nil
                        nil
                        nil
                        (hidden-of-proof-tree proof)
                    )
         )

        (<- rule (parse-rule new-proof))

        (Pif (null rule) -->
            (breakout evaluation
               '|While parsing rule token: rule token was empty.|
            )

         || (member (kind-of-rule rule) '(HELP ERR)) -->
            (breakout evaluation
               (concat '|While parsing rule token: | (cadr rule))
            )  
    
         fi)

        rule
    )
    nil  ;-- no rule body
  )
)


;-- integer square-root used for statistics calculations. 

(defmlfun (|sqrt| ml-sqrt) (n) (int -> int)
    (round (sqrt n))
)








;;; ****************************************************************************

;;; This section implements various ML functions that allow automation of
;;; various PRL activities which normally require entering commands and using
;;; red and ted.

;;; ****************************************************************************


;;; The token argument is interpreted as a line of text entered into
;;; the command processor.
(defmlfun (|execute_command_line| ml-execute-command-line) (line)
	  (tok -> void)
  (<- cmd-text$ (append (istring line) '((NL))))
  (scan-cmd$)
  (expand-cmd-word$)
  (let*
    ((return-message
       (catch
	 'CMDERR
	 (case cmd-token$
	   (|load| (load-cmd$))
	   (|dump| (dump-cmd$))
	   (|create| (create-cmd$))
	   (|delete| (delete-cmd$))
	   (|jump| (jump-cmd$))
	   (|move| (move-cmd$))
	   (|scroll| (scroll-cmd$))
	   (|down| (down-cmd$))
	   (|check| (check-cmd$))
	   (|view| (view-cmd$))
	   (|save| (save-cmd$))
	   (|restore| (restore-cmd$))
	   (|states| (states-cmd$))
	   (|copystate| (copystate-cmd$))
	   (|kill| (kill-cmd$))
	   (|exit| (<- prl-running$ nil) (<- mlrun$ nil))
	   (otherwise '#.(istring "Command not available, ambiguous, or nonexistent."))))))
    (cond ((null return-message)
	   nil)
	  (t (breakout evaluation (implode return-message))))))


;;; Execute the prl command specified by the token cmd with arguments
;;; given by the token list args.  Command errors are thrown as ML
;;; failures.
(defun execute-command (cmd-name &rest args)
  (ml-execute-command-line
    (implode
      (apply #'append (cons (istring cmd-name)
			    (mapcar #'(lambda (arg)
					(cons (ichar #\space) (istring arg)))
				    (copy-list args)))))))


(defmlfun |execute_command| (cmd-name args) (tok -> ( (tok list) -> void ) )
  (apply #'execute-command (cons cmd-name args)))

;;; Create and check a DEF object with name and library position given by two
;;; token arguments, whose left-hand side is given by the token argument lhs
;;; and whose right hand side is derived from the ML term rhs by unparsing it
;;; and in the process changing all free variables of the term to formal
;;; parameters.  Fail if creating or checking causes a PRL error, or if
;;; the set of lhs formals does not equal the set of rhs formals.
(defmlfun (|create_def|  ml-create-def) (name library-position lhs rhs)
	  (tok -> (tok -> (tok -> (term -> void))))
  (execute-command '|create| name '|def| library-position)
  (let* ((rhs (prl-term rhs))
	 (var-hacker
	   #'(lambda (var)
	       (list var
		     (var-term 'var nil
			       (implode `(#\( #\<
					  ,@(istring var)
					  #\> #\) ))))))
	 (hacked-rhs-Ttree
	   (term-to-Ttree
	     (substitute rhs (mapcar var-hacker (free-vars rhs))))))
    (<- (sel (definition-object
	       (sel (object (object-of-library-member name)) value))
	     body)
	`(Ttree ,@(istring lhs)
		,(ichar #\=) ,(ichar #\=)
		,(ichar #\() ,@(cdr hacked-rhs-Ttree) ,(ichar #\)) ))
    (execute-command '|check| name)
    (cond ((let* ((l1 (formal-list-of-def name))
		  (l2 (rhs-formal-occurrences-of-def name)))
	     (union (prl-set-difference l1 l2) (prl-set-difference l2 l1)))
	   (breakout evaluation '|create_def: formal parameter mismatch.|))))
  nil)


(defmlfun (|make_sequent| ml-make-sequent) (decl-list hidden-hyps concl)
	  ((declaration list) -> ((int list) -> (term -> proof)))
  (mapc #'(lambda (hidden)
	    (cond
	      ((or (< hidden 1)
		   (< (length decl-list) hidden)
		   (not (null (id-of-declaration (nth (1- hidden) decl-list)))))
	       (breakout
		 evaluation
		 '|make_sequent: number inappropriate for hidden hyp.|))))
	hidden-hyps)
  (labels ((closed (term revd-decls)
	     (and (all-free-vars-declared term (reverse revd-decls))
		  (or (null revd-decls)
		      (closed (type-of-declaration (car revd-decls))
			      (cdr revd-decls))))))
    (cond ((not (closed (prl-term concl) (reverse decl-list)))
	   (breakout evaluation
		     '|make_sequent: sequent not closed.|))
	  ((let* ((decld-ids (remove-if #'null
				     (mapcar #'(lambda (decl) (id-of-declaration decl))
					     decl-list))))
	     (not (eql (length decld-ids) (length (remove-duplicates decld-ids)))))
	   (breakout evaluation
		     '|make_sequent: not all declared ids unique.|))
	  (t
	   (proof-tree
	     decl-list
	     (prl-term concl)
	     '(TTREE 0)
	     nil
	     nil
	     'INCOMPLETE
	     hidden-hyps)))))


(defmlfun (|hidden| ml-hidden) (proof) (proof -> (int list))
  (hidden-of-proof-tree proof))

;;; Assumes that the reference fields in theorem objects are
;;; not used.

(defmlfun (|transform_theorem| ml-transform-theorem) (name proof)
	  (tok -> (proof -> void))
  (when (not (null (assumptions-of-proof-tree proof)))
    (breakout evaluation '|transform_theorem: top of proof cannot have assums.|))
  (when (being-viewed$ name)
    (breakout evaluation '|transform_theorem: named thm being viewed.|))
  (check-library-membership name 'THM)
  (let* ((obj (object-of-library-member name))
	 (thm-obj (sel (object obj) value)))
    (<- (sel (object obj) status)
	(red-status-to-obj-status (status-of-proof-tree proof)))
    (<- (sel (theorem-object thm-obj) goal-body)
	`(TTREE ,(ichar #\>) ,(ichar #\>) ,(ichar #\Space)
		,@(cdr (term-to-Ttree (conclusion-of-proof-tree proof)))))
    (<- (sel (theorem-object thm-obj) proof-rep-type)
	'PROOF-TREE)
    (<- (sel (theorem-object thm-obj) proof-representation)
	(copy-proof proof))
    (<- (sel (theorem-object thm-obj) saved-status)
	nil)
    (<- (sel (theorem-object thm-obj) extracted-term)
	nil)
    (<- (sel (theorem-object thm-obj) conclusion)
	(conclusion-of-proof-tree proof)))
  (cond ((is-in-lib-window name)
	 (lib-display)))
  nil)


(defmlfun (|create_theorem| ml-create-theorem) (name position proof)
	  (tok -> (tok -> (proof -> void)))
  (execute-command `|create| name '|thm| position)
  (ml-transform-theorem proof name)
  nil)


(defmlfun (|create_ml_object| ml-create-ml-object) (name position text)
	  (tok -> (tok -> (tok -> void)))
  (execute-command '|create| name '|ml| position)
  (<- (sel (ML-object (sel (object (library-object name)) value)) body)
      `(TTREE ,@(istring text) ,(ichar #\space)))
;  (execute-command '|check| name)
  nil)




;-- ML side of interface for experimental rules.
;-- call a ml function to calculate subgoals. Return a list of (PRL!) sequents.

(defun apply-subgoal-calculation (proof subgoal-function)
  (assign-variable  '|prlgoalseq|
	 (cons
	   (assumptions-of-proof-tree proof)
	   (ml-term
	     (conclusion-of-proof-tree proof)
	   )
	 )

	 (makety '((declaration list) |#|  term))
  )
  (Plet (result (ML (make-subgoal-calculation-call subgoal-function)))
       (cond
	 ((equal (car result) 'SUCCESS)
	  (cons 'SUCCESS %val)
	 )
	 (t result)
       )
  )
)


;-- The ml call produced is
;-- "expersubgoals ((subgoal-function) prlgoalseq);;<nl>"
;--

(defun make-subgoal-calculation-call (subgoal-function)
  (cons 'Ttree
	(append (istring '|expersubgoals ((|)
		(cdr subgoal-function)  ;-- stip of first Ttree marker.
                (istring '|) prlgoalseq);;|)
		(list 10.)    ;-- new line
        )
  )
)


;-- 
;-- This function is used only to insure that the result is the correct
;-- type.  In the future, it may enter into the initialization for the
;-- extraction calculation.



(defmlfun (|expersubgoals| ml-expersubgoals) (s)
	  ((((declaration list) |#|  term) list) -> (((declaration list) |#|  term) list))
  s
)




(defmlfun (|kill_extraction| ml-kill-extraction) (thm-name) (tok -> void)
  (check-library-membership thm-name 'THM)
  (<- (sel (theorem-object (sel (object (library-object thm-name))
				value))
	   extracted-term)
      nil))

(defun set-snapshot-file (x)
  (setq *snapshot-file* x))

(defun reset-snapshot-file ()
  (setq *snapshot-file* "local:>snapshot.lisp")) 

(defmlfun (|set_snapshot_file| ml-set-snapshot-file) (x)
	  (tok -> void)
  (set-snapshot-file (symbol-name x)))

(defmlfun (|reset_snapshot_file| ml-reset-snapshot-file) (ignore)
	  (void -> void)
  (reset-snapshot-file))

