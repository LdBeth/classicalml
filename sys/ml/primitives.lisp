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

(defmlfun (|lib| ml-lib) (tok) (tok -> (tok list))
  (let* ((name (symbol-name tok))
	 (n (length name)))
    (remove-if #'(lambda (member)
		   (let ((member-name (symbol-name member)))
		     (or (< (length member-name) n)
			 (not (string= name member-name
				       :start1 0 :start2 0 :end1 n :end2 n)))))
	       library$)))

;  (let* ((x (symbol-name tok))
;	 (n (length x)))
;    (for (y in library$)
;	 (filter (and (string= x (symbol-name y) :start1 0 :start2 0 :end1 n :end2 n)
;		      y)))))


(defmlfun (|lib_search| ml-lib_search) (tok) (tok -> (tok list))
  (let* ((name (symbol-name tok))
	 (n (length name)))
    (remove-if #'(lambda (member)
		   (let ((member-name (symbol-name member)))
		     (or (< (length member-name) n)
			 (not (search name member-name)))))
	       library$)))



(defmlfun (|library| library) (ignore) (void -> (tok list))
  (declare (ignore ignore))
  library$)


(defmlfun(|object_kind| ml-object-kind) (name) (tok -> tok)
    (if (not (lib-member name)) (breakout evaluation '|object_kind|))
    (sel (object (library-object name)) kind))

;;; match (pattern instance pattern-ids)
;;; Perform a one-way match treating the free occurrences of the
;;; pattern-vars as the meta-variables.  Throw nil to 'match if the
;;; match fails, otherwise return the appropriate a-list.



(defvar *match-bindings*)


(defun match (pattern instance pattern-ids)
    (setq *match-bindings* nil)
    (match$ pattern instance pattern-ids nil)
    (remove-duplicate-bindings *match-bindings*))


(defun remove-duplicate-bindings (a-list)
    (if
      (null a-list)
      nil
      (let*
	((x (caar a-list))
	 (a (cdar a-list)))
	`((,x . ,a)
	  ,@(remove-duplicate-bindings
	      (for
		(p in (cdr a-list))
		(filter (if
			  (eql x (car p))
			  (if (equal-terms a (cdr p))
			      nil
			      (throw 'match 'foo))
			  p))))))))

(defun match$ (pattern instance pattern-vars binding-id-pairs)
    
    (if
      
      (eql (kind-of-term pattern) 'VAR)
      
      (let*
	((x (id-of-var-term pattern)))
	(if
	  (and (member x pattern-vars)
	       (not (assoc x binding-id-pairs)))
	  (if
	    (Psome 
	      #'(lambda (y) (rassoc y binding-id-pairs))
	      (free-vars instance))
	    (throw 'match 'foo)
	    (progn (push (cons x instance) *match-bindings*) nil))
	  (if
	    (and (eql (kind-of-term instance) 'VAR)
		 (or 
		   (eql (cdr (assoc x binding-id-pairs))
		       (id-of-var-term instance))
		   (and (not (assoc x binding-id-pairs))
			(not (rassoc (id-of-var-term instance)
				    binding-id-pairs))
			(eql x (id-of-var-term instance)))))
	    nil
	    (throw 'match 'foo))))
      
      (if
	(or (not (eql (kind-of-term pattern)
		     (kind-of-term instance)))
	    (and (member (kind-of-term pattern) terms-with-no-subterms)
		 (not (equal-terms pattern instance))))
	(throw 'match 'foo)
	(let*
	  ((pattern-binding-ids
	     (binding-ids-of-term pattern))
	   (instance-binding-ids
	     (binding-ids-of-term instance))
	   (new-binding-id-pairs
	     (if
	       (eql (length pattern-binding-ids)
		    (length instance-binding-ids))
	       (append (pairlis pattern-binding-ids instance-binding-ids)
		       binding-id-pairs)
	       (throw 'match 'foo))))	    
          (unless (= (length (subterms-of-term pattern))
		     (length (subterms-of-term instance)))
	    (throw 'match 'foo))
	  (for
	    (p in (subterms-of-term pattern))
	    (i in (subterms-of-term instance))
	    (do (match$ p i pattern-vars new-binding-id-pairs)))
	  nil))))




(defmlfun (|match| ml-match) (ml-pattern ml-instance pattern-ids)
	  (term -> (term -> ((tok list) -> ((tok |#| term) list))))
    (let*
      ((res (catch 'match
		   (match (prl-term ml-pattern)
			  (prl-term ml-instance)
			  pattern-ids))))
      (if (eql res 'foo)
	  (breakout evaluation '|match: no match|)
	  (for
	    (p in res)
	    (save (cons (car p) (ml-term (cdr p))))))))

;;; same as |match|
(defmlfun |first_order_match| (ml-pattern ml-instance pattern-ids)
	  (term -> (term -> ((tok list) -> ((tok |#| term) list))))
    (let*
      ((res (catch 'match
		   (match (prl-term ml-pattern)
			  (prl-term ml-instance)
			  pattern-ids))))
      (if (eql res 'foo)
	  (breakout evaluation '|first_order_match|)
	  (for
	    (p in res)
	    (save (cons (car p) (ml-term (cdr p))))))))


;;; Hacked from the function lib-delete (lives in lib) Operation is
;;; equivalent to creating a new object with the new name after the old
;;; object in the library, then copying the contents, then deleting the
;;; old object.
(defmlfun (|rename_object| ml-rename-object) (name new-name)
	  (tok -> (tok -> void))
    (if (or (not (lib-member name))
	    (being-viewed$ name)
	    (lib-member new-name))
	(breakout evaluation '|rename_object|))
    (let* ((obj (library-object name)))
      (if (eql lib-window-top$ name) (<- lib-window-top$ new-name))
      (invalidate-lib$ (cdr (member name library$)) (list name))
      (for (x in (sel (object obj) references))
	   (do
	     (<- (sel (object (library-object x)) referenced-by)
		 (delete obj *-*))))
      (bind-library-object new-name obj)
      (unbind-library-object name)
      (setf (car (member name library$)) new-name)
      (lib-display)
      nil))


(defmlfun (|eval_term| ml-eval-term) (ml-term) (term -> term)
  (let* ((result (catch 'process-err
			(eval-eval-term
			  (prlterm-eval-term
			    'EVAL-TERM
			    (prl-term ml-term))))))
    (if (eql `ERR (car result))
	(breakout evaluation (concat '|eval_term: | (cadr result)))
	(ml-term result))))


(defmlfun (|make_eval_binding| ml-make-eval-binding) (id ml-term)
	  (tok -> (term -> term))
  (let* ((result (catch 'process-err
			(eval-eval-term
			  (let-term-eval-term
			    'EVAL-LET
			    id
			    (prl-term ml-term))))))
    (if (eql `ERR (car result))
	(breakout evaluation (concat '|make_eval_binding: | (cadr result)))
	(ml-term result))))




(defun try-to-replace-subterm-in-Ttree (Ttree term1 term2)
    (labels ((replace-in-def-ref-body (l)
	       (cond ((null l) nil)
		     (t
		      (cons (replace-in-Ttree (car l))
			    (replace-in-def-ref-body (cdr l))))))
	     (replace-in-Ttree-body (l)
	       (cond ((null l) nil)
		     ((consp (car l))
		      (cons (replace-in-def-ref (car l))
			    (replace-in-Ttree-body (cdr l))))
		     (t
		      (cons (car l)
			    (replace-in-Ttree-body (cdr l))))))
	     (replace-in-Ttree (Ttree)
	       (let* ((parse-res
			(catch
			  'process-err
			  (cons 'SUCCESS (parse Ttree)))))
		 (flush-scanner-input)
		 (cond ((and (eql (car parse-res) 'SUCCESS)
			     (equal-terms (cdr parse-res) term1))
			(term-to-Ttree term2))
		       (t
			(cons 'TTREE (replace-in-Ttree-body (cdr Ttree)))))))
	     (replace-in-def-ref (def-ref)
	       (let* ((parse-res
			(catch
			  'process-err
			  (cons 'SUCCESS (parse (cons 'Ttree def-ref))))))
		 (flush-scanner-input)
		 (cond ((and (eql (car parse-res) 'SUCCESS)
			     (equal-terms (cdr parse-res) term1))
			(cdr (term-to-Ttree term2)))
		       (t
			(cons (car def-ref) (replace-in-def-ref-body (cdr def-ref))))))))
      (replace-in-Ttree Ttree)))



(defmlfun (|try_to_replace_subterm| ml-try-to-replace-subterm) (containing-term old-term new-term)
	  (term -> (term -> (term -> term)))
    (let* ((parse-res
	     (catch
	       'process-err
	       (cons 'SUCCESS
		     (parse (try-to-replace-subterm-in-Ttree
			      (term-to-Ttree (prl-term containing-term))
			      (prl-term old-term)
			      (prl-term new-term)))))))
      (flush-scanner-input)
      (cond ((eql (car parse-res) 'SUCCESS)
	     (ml-term (cdr parse-res)))
	    (t (breakout evaluation `|try_to_replace_subterm.|)))))




(defmlfun (|object_status| ml-object-status) (name) (tok -> tok)
    (if (not (lib-member name)) (breakout evaluation '|object_status|))
    (sel (object (library-object name)) status))

(defmlfun (|status_of_object| ml-status-of-object) (name) (tok -> tok)
    (if (not (lib-member name)) (breakout evaluation '|status_of_object|))
    (sel (object (library-object name)) status))


(defmlfun |open_eval| (term exceptions-are-constant-p exceptions)
	  ( term -> (bool -> ((tok list) -> term)) )
  (let* ((*exceptions-are-constant-p* exceptions-are-constant-p)
	 (*excepted-thms* exceptions)
	 (*top-level-mode-p* nil)
	 (res (catch 'process-err (iterated-eval (prl-term term) eval-empty-env))))
    (cond ((eql (first res) 'ERR)
	   (breakout evaluation (second res)))
	  (t (ml-term res)))))



;;; The following two functions used to be internal to ml-add-display-form (via labels),
;;; but Sun Common Lisp couldn't handle it.

(defun compute-ttree-for-ml-add-display-form (f term)
  (let* ((def? (catch 'evaluation (ap f (ml-term term)))))
    (cond ((symbolp def?)
	   (let* ((x (map-on-subterms
		       #'(lambda (x) (add-ttree-for-ml-add-display-form f x))
		       term)))
	     (term-to-ttree x)))
	  (t
	   `(TTREE (,(car def?)
		    ,@(mapcar #'(lambda (x) (compute-ttree-for-ml-add-display-form f (prl-term x)))
			      (cdr def?))))))))

(defun add-ttree-for-ml-add-display-form (f term)
  (let* ((new-term (copy-list term)))
    (setf (ttree-of-term new-term) (compute-ttree-for-ml-add-display-form f term))
    new-term))
  

(defmlfun (|add_display_form| ml-add-display-form) (f term)
     ( (term -> (tok |#| (term list))) -> (term -> term) )
    (let* ((new-term? (add-ttree-for-ml-add-display-form f (prl-term term))) 
	   (parse-result (catch 'process-err (parse (ttree-of-term new-term?)))))
      (cond ((eql (first parse-result) 'ERR)
	     (breakout evaluation '|add_display_form|))
	    ((equal-terms parse-result (prl-term term))
	     (ml-term parse-result))
	    (t
	     term))))


(defmlfun (|instantiate_trivial_def| ml-instantiate-trivial-def) (name term)
	  (tok -> (term -> term))
  (let* ((lhs-formals (formal-list-of-def name))
	 (rhs (sel (definition-object
		     (sel (object (library-object name)) value))
		   rhs))
	 (new-term (copy-list (prl-term term))))
    (unless (and (eql (length lhs-formals) 1)
		 (equal rhs `(TTREE (FORMAL ,(car lhs-formals)))))
      (breakout evaluation '|instantiate_trivial_def: def not trivial.|))
    (setf (Ttree-of-term new-term) `(TTREE (,name ,(term-to-ttree (prl-term term)))))
    (ml-term new-term)))

(defun kill-ttrees (term)
  (let* ((x (copy-list (map-on-subterms #'kill-ttrees term))))
    (setf (ttree-of-term x) nil)
    x))

(defun destructively-kill-Ttrees-except-in-term-of-terms (term)
  (if (eq (kind-of-term term) 'TERM-OF-THEOREM)
      term
      (let ((x (map-on-subterms #'destructively-kill-Ttrees-except-in-term-of-terms term)))
	(setf (ttree-of-term x) nil)
	x)))

(defmlfun |remove_display_forms_except_for_term_of_theorem_terms|
	  (term) (term -> term)
  (ml-term (destructively-kill-Ttrees-except-in-term-of-terms
	     (copy-tree (prl-term term)))))

(defmlfun (|remove_display_forms| ml-remove-display-forms) (term) (term -> term)
  (ml-term (kill-ttrees (prl-term term))))

;;; Clobbers current library, but does not touch the current ML or eval states.
(defmlfun |restore_library_from_state| (state-name) (tok -> void)
  (restore-library-from-state state-name))
  

(defmlfun |enter_lisp_debugger| (message) (tok -> void) (break (string message)))


(defun ML-string (input-string)
  (let* ((input (cons 'TTREE (map 'list #'(lambda (ch) (char->ichar ch LF))
				  input-string))))
    (setf (cdr (last input))
	  (append (istring ";;") (list LF)))
    (map 'string
	 #'ichar->char
	 (cdr (ML input)))))
	    
(defun expand-library ()
  (declare (special library$))
  (let ((whole-start (get-universal-time)))
    (format t "~%Checking whole library ~%")
    (dolist (name library$)
      (if (eq (sel (object (library-object name)) kind) 'THM)
	  (let ((item-start (get-universal-time)))
	    (format t "checking ~D " name)
	    (check-obj name)
	    (format t "took ")
	    (format t " ~D seconds ~%" (- (get-universal-time) item-start))
	    (force-output))
	  (check-obj name))) 
    (format t "Checking whole library took ~D seconds."
	    (- (get-universal-time) whole-start))))

(defmlfun |expand_library| (x) (void -> void)
  (declare (ignore x))
  (expand-library))

(defmlfun |set_nuprl_path_prefix| (path) (tok -> void)
  (setf *nuprl-path-prefix* (string path)))

(defmlfun |complete_nuprl_path| (directories file)
	  ( (tok list) -> (tok -> tok) )
  (intern (or (namestring (complete-nuprl-path directories file))
	      (breakout evaluation '|complete_nuprl_path: not implemented.|))
	  (find-package 'nuprl)))

(defvar *all-tags-legal?* t)
(defvar *use-new-set-rules-p* t)
(defvar *because-rule-enabled?* t)

(defmlfun |make_all_tags_legal| (yes?) (bool -> bool)
  (setq *all-tags-legal?* yes?)
  yes?)

(defmlfun |use_old_set_rules| (yes?) (bool -> bool)
  (setq *use-new-set-rules-p* (not yes?))
  yes?)

(defmlfun |enable_because_rule| (yes?) (bool -> bool)
  (setq *because-rule-enabled?* yes?)
  yes?)

(defmlfun |old_set_rules_in_use| (foo) (void -> bool)
  (declare (ignore foo))
  (not *use-new-set-rules-p*))

(defmlfun |all_tags_legal| (foo) (void -> bool)
  (declare (ignore foo))
  *all-tags-legal?*)

(defmlfun |because_rule_enabled| (foo) (void -> bool)
  (declare (ignore foo))
  *because-rule-enabled?*)

(defmlfun |reset_rules| (foo) (void -> void)
  (declare (ignore foo))
  (setq *all-tags-legal?* t
	*use-new-set-rules-p* t
	*because-rule-enabled?* t))

;;; Keys are ml-terms with respect to lisp equality, values are proofs.
(defvar *proof-store* (make-hash-table :test #'equal :size 500))

(defmlfun |initialize_proof_store| (foo) (void -> void)
  (clrhash *proof-store*)
  (values))

(defmlfun |add_to_proof_store| (term proof) (term -> (proof -> proof))
  (let* ((term (kill-ttrees (prl-term term)))
	 (l (gethash term *proof-store*)))
    (cond ((null l)
	   (setf (gethash term *proof-store*) (list proof)))
	  ((member proof l :test #'equal-sequent))
	  (t
	   ;; avoid another table lookup.
	   (let ((p (car l))
		 (pl (cdr l)))
	     (setf (car l) proof)
	     (setf (cdr l) (cons p pl))))))
  proof)

(defmlfun |apply_proof_store| (term) (term -> (proof list))
  (copy-list
    (or (gethash (prl-term term) *proof-store*)
	(gethash (kill-ttrees (prl-term term)) *proof-store*)
	(breakout evaluation '|proof_store_lookup|))))

(defmlfun |stored_proofs| (foo) (void -> ((proof list) list))
  (let ((table-values nil))
    (maphash #'(lambda (key value) (push value table-values)) *proof-store*)
    table-values))

(defun head-of-iterated-ap (term)
  (if (eq (kind-of-term term) 'APPLY)
      (head-of-iterated-ap (function-of-apply-term term))
      term))

(defmlfun |head_of_iterated_ap| (term) (term -> term)
  (ml-term (head-of-iterated-ap (prl-term term))))

(defun head-and-length-of-iterated-ap (term)
  (if (eq (kind-of-term term) 'APPLY)
      (multiple-value-bind (head length)
	  (head-and-length-of-iterated-ap (function-of-apply-term term))
	(values head (1+ length)))
      (values term 1)))

(defmlfun |head_and_length_of_iterated_ap| (term) (term -> (term |#| int))
  (multiple-value-bind (head length)
      (head-and-length-of-iterated-ap (prl-term term))
    (cons (ml-term head) length)))


(defmlfun |destruct_iterated_ap| (term) (term -> (term list))
  (labels ((f (ap args-so-far) 
	     (if (eq (kind-of-term ap) 'APPLY)
		 (f (function-of-apply-term ap)
		    (cons (ml-term (arg-of-apply-term ap)) args-so-far))
		 (cons (ml-term ap) args-so-far))))
    (f (prl-term term) '())))

(defmlfun |make_iterated_ap| (head args) (term -> ((term list) -> term))
  (labels ((f (hd args)
	     (if (null args)
		 hd
		 (f (apply-term 'APPLY nil hd (prl-term (car args)))
		    (cdr args)))))
    (ml-term (f (prl-term head) args))))

(defmlfun |concatenate_tokens| (tok1 tok2) (tok -> (tok -> tok))
  (intern (concatenate 'string (string tok1) (string tok2)) (find-package 'nuprl)))

(defmlfun |remove_trailing_underscores| (token) (tok -> tok)
  (intern (string-right-trim '(#\_) (string token)) (find-package 'nuprl)))

(defmlfun |memq| (token token-list) (tok -> ((tok list) -> bool))
  (and (member token token-list :test #'eq)
       t))

(defmlfun |assq| (token token-alist) (tok -> (((tok |#| *) list) -> *))
  (or (cdr (assoc token token-alist :test #'eq))
      (breakout evaluation '|assq|)))

(defmlfun |time| (fun) ((void -> **) -> void)
  (time (ap fun nil)))

(defmlfun |equal_sequents| (p1 p2) (proof -> (proof -> bool))
  (equal-sequent p1 p2))

(defmlfun |display_message| (tok) (tok -> void)
  (display-message (istring tok)))

(defmlfun |is_lib_member| (tok) (tok -> bool)
  (and t (is-lib-member tok)))

;; true if t1 is lexicographically less than t2. false otherwise.
(defmlfun (|compare_terms| ml-compare-terms) (t1 t2) (term -> (term -> bool))
  (eq 'arg1 (compare-terms (prl-term t1) (prl-term t2))))


(defun arith-simplify (expr)

    (<- simp-fcn-stack nil)
    (arith-simplify$ expr))

;--
;-- simplify$ (expr: term)
;--                       

(defun arith-simplify$ (expr)    
    
    (Plet (term-type (kind-of-term expr)
         )
         
        (Pif (eql term-type 'ADD) -->
            (poly-add (list (arith-simplify$ (leftterm-of-binary-term expr))
                            (arith-simplify$ (rightterm-of-binary-term expr))
                      )
            )
           
         || (eql term-type 'MUL) -->
            (poly-mult (list (arith-simplify$ (leftterm-of-binary-term expr))
                             (arith-simplify$ (rightterm-of-binary-term expr))
                       )
            )
         
         || (eql term-type 'DIV) -->
            (Plet (result-args (list (arith-simplify$ (leftterm-of-binary-term expr))
                                    (arith-simplify$ (rightterm-of-binary-term expr))
                              )
                 )
                 (Pif (and (all-constants result-args)
                          (not
			      (any-zeroes (cdr result-args))
                          )
                     ) -->     
                     (Plet (result (apply 'truncate 
                                         (mapcar 'get-coeff result-args)
                                  )
                          )
                          (Pif (minusp result) -->
                              (minus-term 'MINUS 
                                          nil 
                                          (pos-number-term
                                             'POS-NUMBER nil (- result)
                                          )
                              )              

                           || t -->
                              (pos-number-term 'POS-NUMBER nil result)
 
                           fi)
                     )

                  || t -->
                     (binary-term 'DIV nil (car result-args) (cadr result-args))

                  fi)
            )
                                                         
         || (eql term-type 'MOD) -->
            (binary-term 'MOD
                         nil
                         (arith-simplify$ (leftterm-of-binary-term expr))
                         (arith-simplify$ (rightterm-of-binary-term expr))
            )

         || (eql term-type 'SUB) -->
            (poly-add (list 
                         (arith-simplify$ (leftterm-of-binary-term expr))
                         (dist-neg (arith-simplify$ (rightterm-of-binary-term expr)))
                      )
            )

         || (eql term-type 'MINUS) -->
            (dist-neg (arith-simplify$ (term-of-minus-term expr)))

	 || t -->
	    expr

         fi)

    )
)


(defmlfun (|arith_simplify| ml-arith-simplify) (term)
	  (term -> term)
  (ml-term (arith-simplify (prl-term term))))
