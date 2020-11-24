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


(global simp-fcn-stack)          ;-- a list of function ids.  In simplification
                                 ;-- function refs. may be expanded, i.e.
                                 ;-- replaced by the recursive step right hand
                                 ;-- side of the def.  simp-fcn-stack is used to
                                 ;-- prevent further inductive step expansions 
                                 ;-- of the fcn.


            
(defun simplify (expr)

    (<- simp-fcn-stack nil)
    (simplify$ expr)

)

;--
;-- simplify$ (expr: term)
;--                       

(defun simplify$ (expr)    
    
    (Plet (term-type (kind-of-term expr)
         )
         
        (Pif (eql term-type 'CONS) -->
            (cons-term 'CONS nil (simplify$ (head-of-cons-term expr))
                                 (simplify$ (tail-of-cons-term expr))
            )

         || (eql term-type 'ADD) -->
            (poly-add (list (simplify$ (leftterm-of-binary-term expr))
                            (simplify$ (rightterm-of-binary-term expr))
                      )
            )
           
         || (eql term-type 'MUL) -->
            (poly-mult (list (simplify$ (leftterm-of-binary-term expr))
                             (simplify$ (rightterm-of-binary-term expr))
                       )
            )
         
         || (eql term-type 'DIV) -->
            (Plet (result-args (list (simplify$ (leftterm-of-binary-term expr))
                                    (simplify$ (rightterm-of-binary-term expr))
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
                         (simplify$ (leftterm-of-binary-term expr))
                         (simplify$ (rightterm-of-binary-term expr))
            )

         || (eql term-type 'SUB) -->
            (poly-add (list 
                         (simplify$ (leftterm-of-binary-term expr))
                         (dist-neg (simplify$ (rightterm-of-binary-term expr)))
                      )
            )

         || (eql term-type 'MINUS) -->
            (dist-neg (simplify$ (term-of-minus-term expr)))

         || (eql term-type 'APPLY) -->
            (function-simp (apply-term 
                                'APPLY
                                nil 
                                (simplify$ (function-of-apply-term expr))
                                (simplify$ (arg-of-apply-term expr))
                           )
            )

         || (eql term-type 'ANY) -->
            (any-term 'ANY nil (simplify$ (term-of-any-term expr)))

         || (eql term-type 'IND) -->
            (ind-term 'IND
                      nil
                      (simplify$ (value-of-ind-term expr))
                      (simplify$ (downterm-of-ind-term expr))
                      (simplify$ (baseterm-of-ind-term expr))
                      (simplify$ (upterm-of-ind-term expr))
            )                   

         || (eql term-type 'LIST) -->
            (list-term 'LIST nil (simplify$ (type-of-list-term expr)))

         || (eql term-type 'LIST-IND) -->
            (list-ind-term 'LIST-IND
                           nil
                          (simplify$ (value-of-list-ind-term expr))
                          (simplify$ (baseterm-of-list-ind-term expr))
                          (simplify$ (upterm-of-list-ind-term expr))
            )                   
                                                     
         || (eql term-type 'UNION) -->
            (union-term 'UNION
                        nil
                        (lefttype-of-union-term expr)
                        (righttype-of-union-term expr)
            )

         || (member term-type '(INL INR)) -->
            (injection-term 
                'INJECTION nil (simplify$ (term-of-injection-term expr))
            )

         || (eql term-type 'DECIDE) -->
            (decide-term 'DECIDE
                         nil
                         (simplify$ (value-of-decide-term expr))
                         (simplify$ (leftterm-of-decide-term expr))
                         (simplify$ (rightterm-of-decide-term expr))
            )
         || (eql term-type 'PRODUCT) -->
            expr
         || (eql term-type 'PAIR) -->
            (pair-term 'PAIR
                       nil
                       (simplify$ (leftterm-of-pair-term expr))
                       (simplify$ (rightterm-of-pair-term expr))
            )
         || (eql term-type 'SPREAD) -->
            (spread-term 'SPREAD
                         nil
                         (simplify$ (value-of-spread-term expr))
                         (simplify$ (term-of-spread-term expr))
            )
         || (eql term-type 'FUNCTION) -->
            expr
         || (eql term-type 'LAMBDA) -->
            expr
         || (eql term-type 'QUOTIENT) -->
            expr
         || (eql term-type 'EQUAL) -->
            (equal-term 'EQUAL
                        nil
                        (simplify$ (type-of-equal-term expr))
                        (mapcar #'simplify$
                                (terms-of-equal-term expr)
                        )
            )
         || (eql term-type 'LESS) -->
            (less-term 'LESS
                       nil
                       (simplify$ (leftterm-of-less-term expr))
                       (simplify$ (rightterm-of-less-term expr))
            )
         || (eql term-type 'BOUND-ID-TERM) -->
            expr
         || (member term-type '(ATOMEQ INTEQ INTLESS)) -->
            (decision-term term-type
                           nil
                           (simplify$ (leftterm-of-decision-term expr))
                           (simplify$ (rightterm-of-decision-term expr))
                           (simplify$ (if-term-of-decision-term expr))
                           (simplify$ (else-term-of-decision-term expr))
            )                              
         || (member term-type 
                    '(UNIVERSE VOID ATOM TOKEN INT POS-NUMBER NIL AXIOM VAR)
            ) -->
            expr
	 || t -->
	    expr

         fi)

    )
)

;--                                      
;-- dist-neg (term: term)
;--
;--     negate a simplified term (by distrubuting a negation operation to the 
;--     appropriate place in the term)
;--
;--

(defun dist-neg (term)

    (Plet (term-type (kind-of-term term)
         )

        (Pif (eql term-type 'ADD) -->
            (binary-term 'ADD 
                         nil
                         (dist-neg (leftterm-of-binary-term term))
                         (dist-neg (rightterm-of-binary-term term))
            )          

	 || (eql term-type 'MUL) -->                                 
            (Plet (coeff (get-coeff term)
                 )
                (Pif (> coeff 1) -->
                    (binary-term 'MUL
                                 nil
                                 (minus-term 
                                      'MINUS
                                      nil
                                      (pos-number-term 'POS-NUMBER nil coeff)
                                 )
                                 (n-args-to-binary-term$
				   'MUL
				   (get-term term)
				 )
                    )
         
                 || (< coeff -1) -->
                    (binary-term 'MUL 
                                 nil
                                 (pos-number-term 'POS-NUMBER nil (- coeff))
				 (n-args-to-binary-term$
				   'MUL
				   (get-term term)
				 )
                    )   

                 || (= coeff 1) -->
                    (minus-term 'MINUS nil
				(n-args-to-binary-term$
				  'MUL
				  (get-term term)
				)
		    )

                 fi)
            )

         || (eql term-type 'MINUS) -->
            (term-of-minus-term term)

         || (zero-term term) -->
            term

         || t -->
            (minus-term 'MINUS nil term)

         fi)   
    )
)

;--
;-- poly-add (term-list: list of simplified terms ("polynomials") )
;--
;--     return the term which is the result of summing the terms
;--     of term list

(defun poly-add (term-list)
  
  (if (= (length term-list) 1)
      (car term-list)
      (let ((arg1 nil)
	    (arg2 nil)
            (result-arg-list  nil))

	(if (eq (kind-of-term (car term-list)) 'ADD)
	    (setf arg1 (get-addends$ (car term-list)))
	    (setf arg1 (list (car term-list))))

	(let ((add-result (poly-add (cdr term-list))))
	  (if (eq (kind-of-term add-result) 'ADD)
	      (setf arg2 (get-addends$ add-result))
	      (setf arg2 (list add-result))))

	(let ((temp-result nil))
	  (do ()
	      ((or (null arg1) (null arg2)))
	    (let ((lower-degree (compare-term-degrees arg1 arg2)))
	      (cond ((eq lower-degree 'ARG1)
		     (when (not (zero-term (car arg1)))
		       (push (car arg1) temp-result))
		     (setf arg1 (cdr arg1)))

		    ((eq lower-degree 'ARG2)
		     (when (not (zero-term (car arg2)))
		       (push (car arg2) temp-result))
		     (setf arg2 (cdr arg2)))

		    (t
		     (let ((eq-deg-add-result (eq-degree-add (car arg1) (car arg2))))
		       (when (not (zero-term eq-deg-add-result))
			 (push eq-deg-add-result temp-result)))
		     (<- arg1 (cdr arg1))
		     (<- arg2 (cdr arg2)) )) ))
	  (if (and (null arg1) (null arg2))
	      (setf result-arg-list (nreverse temp-result))
	      (if arg1
		  (setf result-arg-list (append (nreverse temp-result) arg1))
		  (setf result-arg-list (append (nreverse temp-result) arg2)))))

	(cond ((= (length result-arg-list) 0)
	       (pos-number-term 'POS-NUMBER nil 0))
	      ((= (length result-arg-list) 1)
	       (car result-arg-list))
	      (t (n-args-to-binary-term$ 'ADD result-arg-list))))))


(defun n-args-to-binary-term$ (kind arg-list)
    (Pif (onep (length arg-list)) -->
        (car arg-list)

     || (= (length arg-list) 2) -->
        (binary-term kind nil (car arg-list) (cadr arg-list))

     || t -->
        (binary-term 
            kind 
            nil
            (car arg-list)
            (n-args-to-binary-term$ kind (cdr arg-list))
        )

     fi)
)

;--
;-- zero-term (term: term)
;--
;--     return t if term is the 0 integer term
;--

(defun zero-term (term)

    (equal-terms term (pos-number-term 'POS-NUMBER nil 0))

)

;--
;-- minus-one-term (term: term)
;--
;--     return t if term is -1
;--                           

(defun minus-one-term (term)
    (equal-terms term 
                 (minus-term 'MINUS nil (pos-number-term 'POS-NUMBER nil 1))
    )
)


;;; compare-term-degrees (term-list1 term-list2)
;;;    the terms in the lists must be simplified terms.
;;;    returns :  'ARG1 if first term of term-list1 is of lower degree.
;;;               'ARG2 if first term of term-list2 is of lower degree.
;;;     degree - a lexicographic comparison between terms stripped of their coefficients.
;;;     coefficient - 'MUL term with leftterm a number :
;;;                       ('POS-NUMBER ttree i) or ('MINUS ttree ('POS-NUMBER ttree i)) 
;;;                    or a 'MINUS term in which case coefficient is -1.


(defun strip-coefficient-from-simplified-term (term)
  (if (eq 'MINUS (kind-of-term term))
      (if (eq 'POS-NUMBER (kind-of-term (term-of-minus-term term)))
	  nil
	  (term-of-minus-term term))
      (if (eq 'POS-NUMBER (kind-of-term term))
	  nil
	  (if (eq 'MUL (kind-of-term term))
	      (if (or (eq 'POS-NUMBER (kind-of-term (leftterm-of-binary-term term)))
		      (and (eq 'MINUS (kind-of-term (leftterm-of-binary-term term)))
			   (eq 'POS-NUMBER 
			       (kind-of-term (term-of-minus-term 
					       (leftterm-of-binary-term term))))))
		  (rightterm-of-binary-term term)
		  term)
	      term) )))

(defun compare-term-degrees (term-list1 term-list2)
  (compare-terms 
    (strip-coefficient-from-simplified-term (car term-list1)) 
    (strip-coefficient-from-simplified-term (car term-list2))))

;;; compare-terms (term1 term2)
;;;  does a lexicographic comparison of the terms. (terms need not be simplified).
;;;  returns ARG1 if term1 is lexically less than term2 and returns ARG2 if term2 less
;;;    and returns nil if they be equal.

(defun compare-terms (term1 term2)

  (if (and (null term1) (null term2))
      nil
      (if (null term1)
	  'arg1
	  (if (null term2)
	      'arg2
	      (if (not (eq (kind-of-term term1) (kind-of-term term2)))
		  (let ((assoc-list 
			  '((POS-NUMBER 0) (VAR 1) (APPLY 2) (MUL 3)
			    (DIV 4) (MOD 5) (ADD 6) (SUB 7) (CONS 8) (UNIVERSE 9)
			    (VOID 10) (ANY 11) (ATOM 12) (TOKEN 13) (IND 14)
			    (LIST 15) (NIL 16) (LIST-IND 17) (UNION 18)
			    (INL 19) (INR 20) (DECIDE 21) (PRODUCT 22)
			    (PAIR 23) (SPREAD 24) (FUNCTION 25) (LAMBDA 26)
			    (QUOTIENT 27) (SET 28) (EQUAL 29) (AXIOM 30)
			    (LESS 31) (BOUND-ID-TERM 32) (TERM-OF-THEOREM 33)
			    (ATOMEQ 34) (INTEQ 35) (INTLESS 36) 
			    (INT 37) (OBJECT 38) (SIMPLE-REC-IND 39) (SIMPLE-REC 40)
			    (MINUS 41)
			    )))
                    (if (< (cadr (assoc (kind-of-term term1) assoc-list))
			   (cadr (assoc (kind-of-term term2) assoc-list)))
                        'ARG1
                        'ARG2))

		  ;; term kinds eq.
		  (case (kind-of-term term1)

		    ((POS-NUMBER UNIVERSE) (cond ((= (third term1) (third term2)) nil)
						 ((< (third term1) (third term2)) 'ARG1)
						 (t 'ARG2)))

		    (VAR (cond ((eq (third term1) (third term2)) nil)
			       ((string< (third term1) (third term2)) 'ARG1)
			       (t 'ARG2)))

		    ((APPLY ADD SUB DIV MOD CONS UNION PAIR SPREAD LESS MUL SIMPLE-REC-IND)
		     (let ((result (compare-terms (third term1) (third term2))))
		       (if result
			   result
			   (compare-terms (fourth term1) (fourth term2)))))

		    ((ANY LIST INL INR MINUS)
		     (compare-terms (third term1) (third term2)))

		    ((IND INTLESS INTEQ ATOMEQ)
		     (compare-term-lists 
		       (list (third term1) (fourth term1) (fifth term1) (sixth term1))
		       (list (third term2) (fourth term2) (fifth term2) (sixth term2))))

		    ((LIST-IND DECIDE)
		     (compare-term-lists 
		       (list (third term1) (fourth term1) (fifth term1))
		       (list (third term2) (fourth term2) (fifth term2))))

		    ((LAMBDA SIMPLE-REC)
		     (let ((result (compare-ids$ (third term1) (third term2))))
		       (if result
			   result
			   (compare-terms (fourth term1) (fourth term2)))))

		    ((PRODUCT FUNCTION SET)
		     (let ((result (compare-ids$ (third term1) (third term2))))
		       (if result
			   result
			   (progn
			     (setf result (compare-terms (fourth term1) (fourth term2)))
			     (if result
				 result
				 (compare-terms (fifth term1) (fifth term2)))))))
			   
		    (TOKEN 
		      (let ((atom1 (implode (atom-of-token-term term1)))
			    (atom2 (implode (atom-of-token-term term2))))
			(cond 
			  ((string< atom1 atom2) 'ARG1)
                          ((string< atom2 atom1) 'ARG2)
			  (t nil))))

		    (QUOTIENT
		      (let ((result (compare-id-lists$ 
				      (bound-ids-of-quotient-term term1)
				      (bound-ids-of-quotient-term term2))))
                        (if result
			    result
			    (progn
			      (setf result (compare-terms (fourth term1) (fourth term2)))
			      (if result
				  result
				  (compare-terms (fifth term1) (fifth term2)))))))

		    (EQUAL 
		      (let ((result (compare-terms (type-of-equal-term term1)
						   (type-of-equal-term term2))))
			(if result
			    result
			    (compare-term-lists (terms-of-equal-term term1)
						(terms-of-equal-term term2)))))

		    (BOUND-ID-TERM
		      (let ((result (compare-id-lists$ 
				      (bound-ids-of-bound-id-term term1)
				      (bound-ids-of-bound-id-term term2))))
                        (if result
			    result
			    (compare-terms (term-of-bound-id-term term1)
					   (term-of-bound-id-term term2)))))

		    (TERM-OF-THEOREM
		      (cond ((string< (name-of-term-of-theorem-term term1)
				      (name-of-term-of-theorem-term term2))
			     'ARG1)
	     ((string< (name-of-term-of-theorem-term term2)
				      (name-of-term-of-theorem-term term1))
			     'ARG2)
			    (t nil)))

		    (OTHERWISE nil)
		    ) )))))


;;;
;;; compare-term-lists (term-list-1 term-list-2)
;;;  call compare-terms on pairs of terms in the pair of lists.
;;;

(defun compare-term-lists (term-list-1 term-list-2)
  (if (and (null term-list-1)
	   (null term-list-2))
      nil
      (let ((result (compare-terms (car term-list-1) (car term-list-2))))
	(if result
	    result
	    (compare-term-lists (cdr term-list-1) (cdr term-list-2))))))


(defun compare-ids$ (id1 id2) 
    (Pif (and (null id1) (null id2)) -->
        nil
     || (null id1) -->
        'ARG1
     || (null id2) -->
        'ARG2
     || (string< id1 id2) -->
        'ARG1
     || (string< id2 id1) -->
        'ARG2 
     || t -->
        nil
     fi)
)

(defun compare-id-lists$ (id-list1 id-list2)
    (Pif (and (null id-list1) (null id-list2)) -->
        nil
     || (null id-list1) -->
        'ARG1
     || (null id-list2) -->
        'ARG2
     || t -->
        (Plet (result (compare-ids$ (car id-list1) (car id-list2)) 
             )
            (Pif (not result) -->
                (compare-id-lists$ (cdr id-list1) (cdr id-list2))
             || t -->
                result
             fi)
        )
     fi)
)
        
;--
;-- eq-degree-add (term1:term, term2: term)
;--
;--     add two simplified terms of the same "degree" and return the result.
;--

(defun eq-degree-add (term1 term2)

    (Plet (rest-of-term  (get-term term1)
          result-coeff  nil
         )
        
        (<- result-coeff (+ (get-coeff term1) (get-coeff term2)))
        (make-result-term result-coeff rest-of-term)
          
    )  
)                   

;--
;-- get-coeff (term: term)
;--
;--     return the integer coefficient of a simplified term
;--                      

(defun get-coeff (term)

    (Pif (eql (kind-of-term term) 'MINUS) -->
        (- (get-coeff (term-of-minus-term term)))

     || (eql (kind-of-term term) 'POS-NUMBER) -->
        (number-of-pos-number-term term)

     || (eql (kind-of-term term) 'MUL) -->
        (get-coeff (leftterm-of-binary-term term))

     || t -->
        1
 
     fi)

)
   
;--
;-- get-term (term: term)
;--
;--     return a list of the multiplicands (excluding the leading constant term)
;--     of a simplified term.

(defun get-term (term)

    (Pif (eql (kind-of-term term ) 'MINUS) -->
        (get-term (term-of-minus-term term))

     || (eql (kind-of-term term) 'POS-NUMBER) -->
        nil

     || (eql (kind-of-term term) 'MUL) -->
        (Pif (or (eql (kind-of-term (leftterm-of-binary-term term))
                    'POS-NUMBER
                )
                (< (get-coeff term) 0)
            ) -->
            (get-term (rightterm-of-binary-term term))

         || t -->
            (cons (leftterm-of-binary-term term) 
                  (get-term (rightterm-of-binary-term term))
            )

         fi)

     || t -->
        (list term)

     fi)

)

                  
;--
;-- poly-mult (term-list: list of simplified terms ("polynomials") )
;--
;--     return the product of the terms of term-list
;--

(defun poly-mult (term-list)

    (Pif (=  (length term-list) 1) -->
        (car term-list)

     || t -->
        (Plet (arg1 (car term-list)
              arg2 (poly-mult (cdr term-list))
             )
            
            (Pif (not (eql (kind-of-term arg1) 'ADD)) -->
                (mult-term-and-poly arg1 arg2)

             || t -->
                (poly-add 
                    (mapcar #'(lambda (x) (mult-term-and-poly x arg2))
                            (get-addends$ arg1)
                    )
                )

             fi)
                                                                    
        )

     fi)
)            

(defun get-addends$ (add-term)
    (Pif (eql (kind-of-term (rightterm-of-binary-term add-term)) 'ADD) -->
        (cons (leftterm-of-binary-term add-term) 
              (get-addends$ (rightterm-of-binary-term add-term))
        )
     || t -->
        (list (leftterm-of-binary-term add-term)
              (rightterm-of-binary-term add-term)
        )
     fi)
)
                                                                          
;-- 
;-- mult-term-and-poly (term: term, poly: simplified term ("polynomial") )
;--
;--     return the result of multiplying term by poly
;--     (term is not an ADD term)
;--

(defun mult-term-and-poly (term poly)
    
    (Pif (not (eql (kind-of-term poly) 'ADD)) -->
        (mult-terms-merge term poly)

     || t -->
        (poly-add (mapcar #'(lambda (x) (mult-terms-merge term x))
                          (get-addends$ poly)
                  )
        )

     fi)

)
   
;--
;-- mult-terms-merge (term1: term, term2: term)
;--
;--     return the result of multiplying two non-ADD terms together
;--

(defun mult-terms-merge (term1 term2)
    (Plet (result       nil                       
          coeff1       (get-coeff term1)
          coeff2       (get-coeff term2)
	  result-coeff nil
         )
                          
        (<- result-coeff (* coeff1 coeff2))
        (Pif (zerop result-coeff) -->
            (pos-number-term 'POS-NUMBER nil 0)

         || t -->
            (Plet (arg-list-1      (get-term term1)
                  arg-list-2      (get-term term2)
                  result-arg-list nil 
                 )

	      (let ((temp-result nil))
		(do ()
		    ((or (null arg-list-1) (null arg-list-2)))
		  (let ((lower-degree (compare-term-degrees arg-list-1 arg-list-2)))
		    (if (eq lower-degree 'ARG1)
			(progn
			  (push (car arg-list-1) temp-result)
			  (setf arg-list-1 (cdr arg-list-1)))
			(progn
			  (push (car arg-list-2) temp-result)
			  (setf arg-list-2 (cdr arg-list-2)))) ))
		(if (and (null arg-list-1) (null arg-list-2))
		    (setf result-arg-list (nreverse temp-result))
		    (if arg-list-1
			(setf result-arg-list (append (nreverse temp-result) arg-list-1))
			(setf result-arg-list (append (nreverse temp-result) arg-list-2)))))

                (make-result-term result-coeff result-arg-list)
                
             )
  
         fi)
    )

)                        

                        
;--
;-- make-result-term (coeff: integer, rest-of-term: list of terms)
;--
;--     construct a simplified product term (not necessarily a MUL term;
;--     may also be a NEG,HD,VAR, or FUNCTION term) with coeff as its 
;--     integer coefficient and the terms of rest-of-terms as its multiplicands.
;--

(defun make-result-term (coeff rest-of-term)                        

    (Pif (null rest-of-term) -->
        (Pif (< coeff 0) -->
            (dist-neg (pos-number-term 'POS-NUMBER nil (- coeff)))
                  
         || t -->
            (pos-number-term 'POS-NUMBER nil coeff)
         fi)

     || (zerop coeff) -->
        (pos-number-term 'POS-NUMBER nil 0)
  
     || (= coeff 1) -->
        (Pif (= (length rest-of-term) 1) -->
            (car rest-of-term)

         || t -->
            (n-args-to-binary-term$ 'MUL rest-of-term)

         fi)
 
     || (= coeff -1) -->
        (Pif (= (length rest-of-term) 1) -->
            (dist-neg (car rest-of-term))

         || t -->
            (dist-neg (n-args-to-binary-term$ 'MUL rest-of-term))

         fi)

     || (< coeff -1) -->
        (binary-term 
            'MUL 
            nil 
            (dist-neg (pos-number-term 'POS-NUMBER nil (- coeff)))
            (n-args-to-binary-term$ 'MUL rest-of-term)
        )

     || t -->
        (binary-term 'MUL 
                     nil 
                     (pos-number-term 'POS-NUMBER nil coeff)
                     (n-args-to-binary-term$ 'MUL rest-of-term)
        )
 
     fi)

)


;--
;-- function-simp (term: term)
;--
;--     if all arguments of the function term term are integer or list 
;--     constants then return the result of evaluating the function on those
;--     arguments, else return, if possible, the "expansion" of the function
;--     term by using it's (if it has one) rec. fcn. definition.
;--                                    

(defun function-simp (term)

     term

;    (if (all-constants (args-of-fcn-term term)) -->
;        (eval-function-term term)
;
;     || t -->
;        (expand-function-term term)
;     fi)

)

;-- 
;-- eval-function-term (term: term)
;--
;--     return the result of evaluating the function term (just as in the 
;--     prl EVAL command).                                                          

;(de eval-function-term (term)
;
;    (make-fcn-eval-result (eval (rep-term term)))
;
;)
                          
;-- 
;-- make-fcn-eval-result (eval-result: integer or list of integers)
;--
;--     returns a term corresponding to eval-result.

;(de make-fcn-eval-result (eval-result)
;                 
;        (if (numberp eval-result) -->
;            (int-term 'INTEGER nil eval-result)
;
;         || t -->
;            (simplify$ (list-term 'LIST 
;                                 nil 
;                                 (mapcar 'make-fcn-eval-result
;                                         eval-result
;                                 )
;                      )
;            )
;
;        fi)
;
;)
  
;--
;-- expand-function (fcn-term: term)
;--
;--     return the simplification of FUNCTION term, term
;--

;(de expand-function-term (fcn-term)
;
;   (let (fcn-desc      nil ;-- descriptor of function called in fcn-term
;         rec-fcn       nil ;-- rec-fcn tuple describing recursive fcn,
;                           ;--   nil if fcn is extracted (body of fcn-desc)
;         arg-val       nil ;-- the value of the number or list 
;                           ;-- of the induction variable
;         rhs-term      nil ;-- if a rec fcn, the right hand side of the
;                           ;--   branch of the def corresponding to fcn-term
;         expanded-term nil 
;         result    nil
;        )
;
;       ;-- set fcn-desc to the function descriptor of the function
;       ;-- application.  There must be one since the term is well-formed.
;           (<- fcn-desc (lookup-function (fcn-of-fcn-term fcn-term)))
;
;       (<- rec-fcn (sel (fcn-descriptor fcn-desc) body))
;
;       (if (null rec-fcn) -->
;           ;--extracted function -- no simplification done
;              (<- result fcn-term)
;
;         || (eql (itype-of-rec-fcn rec-fcn) 'INTEGER) -->
;            (<- arg-val
;                       (value-of-term$
;                            (car (args-of-fcn-term fcn-term))
;                        )
;            )
;                
;           (if (not arg-val) -->
;               ;-- can't simplify - (first argument must be an integer constant)
;                   (<- result fcn-term)
; 
;            || t -->
;               (if (and (lessp arg-val (value-of-term$ (lo-of-rec-fcn rec-fcn))) 
;                       (not (member (fcn-of-fcn-term fcn-term) simp-fcn-stack))
;                   ) -->
;                   ;-- down going induction case
;                       (if (eql (kind-of-term (prefix-of-rec-fcn-case
;                                               (car (cases-of-rec-fcn rec-fcn))
;                                             )
;                               )
;                               'VAR
;                           ) -->
;                           ;-- a neg ind step exists, use it
;                              (<- rhs-term
;                                    (term-of-rec-fcn-case
;                                        (car (cases-of-rec-fcn rec-fcn))
;                                    )
;                               )
;         
;             
;                        || t -->
;                           ;-- no pos ind step exists, so the implicit rhs is 0
;                           ;-- or nil, depending on the range type of the fcn
;                               (if (eql (rtype-of-rec-fcn rec-fcn) 'INTEGER) -->
;                                   (<- rhs-term (int-term 'INTEGER nil 0))
;                  
;                                || t -->
;                                   (<- rhs-term (list-term 'LIST nil nil))
;                           
;                                fi)
;
;                        fi)
;
;                || (and (lessp (value-of-term$ (hi-of-rec-fcn rec-fcn)) arg-val)
;                        (not (member (fcn-of-fcn-term fcn-term) simp-fcn-stack))
;                   ) -->
;                   ;-- up going induction case
;                        (if (eql (kind-of-term
;                                    (prefix-of-rec-fcn-case
;                                        (car (last (cases-of-rec-fcn rec-fcn)))
;                                    )
;                                )
;                                'VAR
;                            ) -->
;                            ;-- a pos ind step exists, use it
;                                (<- rhs-term
;                                    (term-of-rec-fcn-case
;                                        (car (last (cases-of-rec-fcn rec-fcn)))
;                                    )
;                                )
;
;                     || t -->
;                        ;-- no pos ind step exists, so the implicit rhs is 0
;                        ;-- or nil, depending on the range type of the fcn
;                            (if (eql (rtype-of-rec-fcn rec-fcn) 'INTEGER) -->
;                                (<- rhs-term (int-term 'INTEGER nil 0))
;
;                             || t -->
;                                (<- rhs-term (list-term 'LIST nil nil))
; 
;                             fi)
;
;                        (<- rhs-term (int-term 'INTEGER nil 0))
;
;                     fi)
;
;                || t -->                                                    
;                   ;-- a base case
;                   ;-- if a negative ind step is present, increment arg-val
;                   ;-- so that the ind step is skipped over
;                       (if (eql (kind-of-term
;                                    (prefix-of-rec-fcn-case
;                                           (car (cases-of-rec-fcn rec-fcn))
;                                    )
;                               )
;                               'VAR
;                           ) -->
;                           (<- arg-val (add1 base-val))
;                        fi)
;
;                   (<- rhs-term
;                           (term-of-rec-fcn-case
;                               (nthelem
;                                   (add1 (- arg-val
;                                            (value-of-term$
;                                               (lo-of-rec-fcn rec-fcn)
;                                            )
;                                          )
;                                  )
;                                   (cases-of-rec-fcn rec-fcn)
;                               )
;                           )
;                    )
;
;                fi)
;
;               (<- expanded-term (substitute
;                                    rhs-term
;                                    (mapcar #'(lambda (parm arg)
;                                               (list (id-of-rec-fcn-parm parm)
;                                                     arg
;                                               )
;                                             )
;                                           (parms-of-rec-fcn rec-fcn)
;                                           (args-of-fcn-term fcn-term)
;                                    )
;                                 )
;               )
;         
;               (<- simp-fcn-stack (cons (fcn-of-fcn-term fcn-term)
;                                        simp-fcn-stack
;                                  )
;               )            
;               (<- result (simplify$ expanded-term))
;               (<- simp-fcn-stack (cdr simp-fcn-stack))
;
;            fi)
;
;         || (eql (itype-of-rec-fcn rec-fcn) 'LIST) -->
;
;            (if (and (greaterp (number-of-cons-terms (car (args-of-fcn-term 
;                                                                     fcn-term
;                                                          )
;                                                     )
;                               )
;                               (value-of-term$ (hi-of-rec-fcn rec-fcn))
;                     )
;                     (not (member (fcn-of-fcn-term fcn-term) simp-fcn-stack))
;                ) -->
;                ;-- induction case
;                    (<- rhs-term
;                        (term-of-rec-fcn-case
;                            (car (last (cases-of-rec-fcn rec-fcn)))
;                        )
;                    )
;              
;                    (<- expanded-term
;                           (substitute
;                               rhs-term
;                               (mapcar #'(lambda (parm arg)
;                                           (list (id-of-rec-fcn-parm parm)
;                                                 arg
;                                           )
;                                        )
;                                       (parms-of-rec-fcn rec-fcn)
;                                       (args-of-fcn-term fcn-term)
;                               )
;                           )
;                    )                   
;      
;                   (<- simp-fcn-stack (cons (fcn-of-fcn-term fcn-term)
;                                            simp-fcn-stack
;                                      )
;                   )            
;                   (<- result (simplify$ expanded-term))
;                   (<- simp-fcn-stack (cdr simp-fcn-stack))
;
;
;             || (constant-arg (car (args-of-fcn-term fcn-term))) -->
;                ;--base-case  
;                   (<- rhs-term
;                       (term-of-rec-fcn-case
;                           (nthelem
;                               (add1 (list-length (car (args-of-fcn-term
;                                                                     fcn-term
;                                                       )
;                                                  )
;                                     )
;                               )
;                               (cases-of-rec-fcn rec-fcn)
;                           )
;                       )
;                   )            
;
;                   (<- expanded-term
;                           (substitute
;                               rhs-term
;                              (mapcar #'(lambda (parm arg)
;                                           (list (id-of-rec-fcn-parm parm)
;                                                 arg
;                                           )
;                                        )
;                                       (parms-of-rec-fcn rec-fcn)
;                                       (args-of-fcn-term fcn-term)
;                               )
;                           )
;                   )
;              
;                   (<- result (simplify$ expanded-term))
;
;             || t -->
;                ;-- can't simplify -- don't know whether we have
;                ;-- a base or induction case.
;                    (<- result fcn-term)
;
;             fi)
;  
;          
;
;         fi)
;        
;        result
;    )
;
;)


(defun any-zeroes (constant-list)
    (Ploop
      (local answer nil)
      (while (and (not answer) (not (null constant-list))))
      (do
	(<- answer (zero-term (car constant-list)))
	(<- constant-list (cdr *-*))
      )
      (result answer)
    )
)

;--
;-- all-constants (arg-list: list of (simplified) terms)
;--
;--     return t if each term of arg-list is an integer or list constant
;--


(defun all-constants (arg-list)
    (Ploop
      (local answer t)
      (while (and answer (not (null arg-list))))
      (do
	(<- answer (constant-arg (car arg-list)))
	(<- arg-list (cdr arg-list))
      )
      (result answer)
    )
)


;--
;-- constant-arg (term: term)
;--
;--     return t if term is an integer or list constant
;--
(defun constant-arg (term)

    (Pif (eql (kind-of-term term) 'POS-NUMBER) -->
        t

     || (eql (kind-of-term term) 'MINUS) -->
        (constant-arg (term-of-minus-term term))

     || (eql (kind-of-term term) 'NIL) -->
        t

     || (eql (kind-of-term term) 'CONS) -->
        (and (constant-arg (head-of-cons-term term))
             (constant-arg (tail-of-cons-term term))
        )

     fi)
)

;--
;-- list-length (list-term: simplified CONS or LIST term)
;--
;--     list-term must be a list-constant
;--     return the length of the list represented by list-term
;--

;(de list-length (list-term)
;
;    (if (eql (kind-of-term list-term) 'NIL) -->
;        0
;
;     || t -->
;        (number-of-cons-terms list-term)
; 
;     fi)
;
;)
