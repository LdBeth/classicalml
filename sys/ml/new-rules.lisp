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


(make-rule
  |eval|
  (case thm-names)
  (let* ((case-atom (get-decision-case$))
	 (case (cond ((eql case-atom '|true|) t)
		     (t nil)))
	 (thm-names (cond ((eql token-type TEndInput) ())
			  (t (get-new-id-list$)))))
    (eval-rule 'EVAL case thm-names))
  (let* ((*top-level-mode-p* nil)
	 (*exceptions-are-constant-p* (case-of-eval-rule ref-rule))
	 (*excepted-thms* (thm-names-of-eval-rule ref-rule)))
    (<- ref-children
	(list
	  (make-child ref-assums (iterated-eval ref-concl eval-empty-env)))))
  (extract$ (first (children-of-proof-tree pt)) assum-map)
  ((L |eval |) (2 BOOL) (3 TOKENS))
  ( bool -> ((tok list) -> rule))
  (lambda (case thm-names) nil))


(make-rule
  |eval_hyp|
  (assum-num case thm-names)
  (let* ((assum-num (get-assumption))
	 (case-atom (get-decision-case$))
	 (case (cond ((eql case-atom '|true|) t)
		     (t nil)))
	 (thm-names (cond ((eql token-type TEndInput) ())
			  (t (get-new-id-list$)))))
    (eval_hyp-rule 'EVAL_HYP assum-num case thm-names))
  (let* ((*top-level-mode-p* nil)
	 (*exceptions-are-constant-p* (case-of-eval_hyp-rule ref-rule))
	 (*excepted-thms* (thm-names-of-eval_hyp-rule ref-rule))
	 (assum-num (assum-num-of-eval_hyp-rule ref-rule))
	 (assum-to-be-replaced (nth (1- assum-num) ref-assums))
	 (copied-assums (copy-list ref-assums)))
    (cond ((not assum-to-be-replaced)
	   (ref-error '|hypothesis number out of range|)))
    (<- ref-children
	(list
	  (make-child (progn
			(setf (car (nthcdr (1- assum-num) copied-assums))
			      (declaration
				nil
				(id-of-declaration assum-to-be-replaced)
				(iterated-eval (type-of-declaration assum-to-be-replaced)
					       eval-empty-env)))
			copied-assums)
		      ref-concl))))
  (extract$ (first (children-of-proof-tree pt)) assum-map)
  ((L |eval_hyp |) (2 N) (L | |) (3 BOOL) (4 TOKENS))
  ( int -> (bool -> ( (tok list) -> rule)) )
  (lambda (assum-num case thm-names)
    (cons (eval_hyp-rule 'EVAL_HYP assum-num case thm-names) nil)))



(make-rule
  |reverse_direct_computation|
  (using-term)
  (reverse_direct_computation-rule
    'REVERSE_DIRECT_COMPUTATION
    (check-for-using-term$ '||))
  (let* ((using-term (using-term-of-reverse_direct_computation-rule ref-rule))
	 (comp-res (do-indicated-computations using-term)))
    (cond ((not (equal-terms ref-concl comp-res))
	   (ref-error '|Using term does not compute to conclusion.|))
	  ((has-legal-tagging using-term)
	   (<- ref-children
	       (list (make-child ref-assums
				 (erase-tags using-term)))))
	  (t
	   (ref-error '|Using term has illegal tagging|)))
    (values))
  (extract$ (first (children-of-proof-tree pt)) assum-map)
  ((L |reverse_direct_computation |) (L | using |) (2 T))
  (term -> rule)
  (lambda (using)
    (setq using (prl-term using))))

(defun firstn (n list)
  (if (or (< n 1) (null list))
      (list)
      (cons (first list) (firstn (- n 1) (rest list)))))

(make-rule
  |reverse_direct_computation_hyp|
  (assum-num using-term)
  (cond ((eql token-type TNbr)
	 (cond ((or (< token-val 1) 
		    (> token-val (length ref-assums)))
		(ref-error '|assum. num after is out of range.|))
	       (t
		(reverse_direct_computation_hyp-rule
		  'REVERSE_DIRECT_COMPUTATION_HYP
		  token-val
		  (progn
		    (scan)
		    (check-for-using-term$ '||))))))
	(t
	 (ref-error '|missing assum. num|)))
  (let* ((assum-num (assum-num-of-reverse_direct_computation_hyp-rule ref-rule))
	 (using-term (using-term-of-reverse_direct_computation_hyp-rule ref-rule))
	 (assum-to-be-replaced
	   (ref-assert (o #'not #'null)
		       (nth (1- assum-num) ref-assums)
		       '|hypothesis number out of range|))
	 (preceeding-assums (firstn (1- assum-num) ref-assums))
	 (following-assums (nthcdr assum-num ref-assums))
	 (comp-res (do-indicated-computations using-term)))
    (cond ((not (equal-terms
		  (type-of-declaration assum-to-be-replaced)
		  comp-res))
	   (ref-error '|Using term does not compute to hypothesis.|))
	  ((not (has-legal-tagging using-term))
	   (ref-error '|Illegal tagging in using term.|))
	  (t
	   (<- ref-children
	       (list (make-child
		       (append
			 preceeding-assums
			 (cons (declaration
				 nil
				 (id-of-declaration assum-to-be-replaced)
				 (erase-tags using-term))
			       following-assums))
		       ref-concl)))))
    (values))
  (extract$ (first (children-of-proof-tree pt)) assum-map)
  ((L |reverse_direct_computation_hyp |) (2 N) (L | using |) (3 T))
  (int -> (term -> rule))
  (lambda (i using) (setq using (prl-term using))))
