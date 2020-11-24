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


; EQUALITY RULE -- for complete description of the congruence closure
;                  algorithm used see Johnson, A Computer System for
;                  Checking Proofs, TR 80-444, Chptr. 6, or Krafft, TR 81-458.
;                  Discussion of the use of congruence closure for the theory
;                  of LISP list structure can be found in Nelson and Oppen,
;                  Fast Decision Procedures Based on Congruence Closure,
;                  JACM, v.27, no.2 , April 1980.

(global num-buckets$)
(eval-when (compile load eval)
    (<- num-buckets$ 117)
)

(Pdeftype bucket-array-type$ array (num-buckets$)) ;buckets$ is an array of 
(global buckets$ bucket-array-type$)              ;pointers to nodes.  Each ele-
(<- buckets$ (new bucket-array-type$))            ;ment of buckets$ is a pointer
                                                  ;to a doubly linked list (with
                                                  ;header) of nodes linked 
                                                  ;through their previous and
                                                  ;next fields.

(global unknown-terms bucket-array-type$)
(<- unknown-terms (new bucket-array-type$))
(global unknown-term-count)

(global disequalities$)                           ;a list of pairs of nodes
                                                  ;that are the lhs's and rhs's
                                                  ;of disequalities in H ^ ~C  

(global non-equality-assumption-formulas)
(global non-equality-conclusion-formula)


(global num-nodes$)                               ;number of nodes now existing

(global free-node-list)
(<- free-node-list nil)
                                  
(deftuple eq-node              ; nodes in the graph used in the congruence closure
                            ; algorithm correspond to terms

          label             ; function identifier for the term corresponding to
                            ;   this node
                            ;   For some terms this label is a list. For
                            ;   other terms label is equal to the term's KIND
                            ;   field.             
          operands          ; a list of pointers to the nodes representing the
                            ;   operands for this function node    
                            ;   (the node corresponding to the type of a term
                            ;   is considered an operand of that term)
          containers        ; a list of pairs corresponding to operand fields 
                            ;   of nodes for which this is an operand
                            ;   The list is of the form (n i).  n is a pointer
                            ;   to a node whose i-th operand is this node.
          reprlink          ; either a pointer to a node, or nil (marking the
                            ;   root) such that for all modes x and y,  x and y
                            ;   are in the same equivalence class iff their
                            ;   reprlinks lead to the same root node
          reprcount         ; the number of nodes in this node's equivalence
                            ;   class (if this node is a representative)
          previous          ; the previous entry in this hash bucket
          next              ; the next entry in the hash bucket
          eligible          ; a boolean value, = "this node is in a hash bucket"
          node-iden         ; a unique integer associated with this node (used
                            ;   for hashing purposes; this value is used as a 
                            ;   "fake pointer" to this node)
)                             


;---;
;---; equality (hypotheses:term-list, conclusion:term)
;---;
;---;      hypotheses: a list of hypotheses 
;---;
;---;      conclusion: a single conclusion term
;---;
;---;    This returns the atom GOOD if the deduction succeeds, and an atom whose
;---;    print name is an error message if the deduction does not succeed.          
;---;
;---   
;---(defun equality (hypotheses conclusion)
;---        
;---  (Pcatch (Plet ()
;---
;---   (init-equality)
;---   
;---   ; process the hypotheses --
;---   ;   for each equality assert the terms equal (relative to the type of the 
;---   ;   equality) in the graph for each disequality add the pair {lhs,rhs} to 
;---   ;   the disequality list ignore all other types of forumulas
;---   ;
;---
;---    (Plet (assum-count 0
;---          assum-map-list nil
;---         )
;--- 
;---        (for (term in hypotheses)
;---             (do 
;---                (<- assum-count (add1 assum-count))
;---                (Pif (eql (kind-of-term term) 'EQUAL) -->
;---                    (do-equality (type-of-equal-term term)
;---                                 (terms-of-equal-term term)
;---                    )
;---
;---                 || (not-equal-term$ term) -->
;---                    (do-disequality 
;---                        (type-of-equal-term (not-term-body$ term))
;---                        (terms-of-equal-term (not-term-body$ term))
;---                    )
;---
;---                 || t --> 
;---                    (<- non-equality-assumption-formulas
;---                        (cons term non-equality-assumption-formulas)
;---                    )
;---                    (<- assum-map-list (cons assum-count assum-map-list))
;---
;---                 fi)
;---  
;---             )
;---         )
;---
;---   ; process the conclusion term --
;---   ;   first negate the term
;---   ;   if an equality results assert its terms equal
;---   ;   if a disequality add the list (type terms) to the disequality list
;---   ;
;---   (Pif (equal (kind-of-term conclusion) 'EQUAL) -->
;---       (do-disequality (type-of-equal-term conclusion)
;---                       (terms-of-equal-term conclusion)
;---       )
;---
;---    || (not-equal-term$ conclusion) -->
;---       (do-equality (type-of-equal-term (not-term-body$ conclusion))
;---                    (terms-of-equal-term (not-term-body$ conclusion))
;---       )
;---
;---    || t -->
;---       (<- non-equality-conclusion-formula conclusion) 
;---    fi)
;---
;---   ;
;---   ;  The graph now represents the assertion of all of the equalities.
;---   ;  For each list (type terms) in the disequality list check if each term
;---   ;  in terms is in the same equivalence class (relative to type) in the graph.
;---   ;  If so, the conjunction of the hypotheses and the negation of the
;---   ;   conclusion is unsatisfiable and
;---   ;  therefore the deduction is successful (return GOOD in this case)
;---   ;  Also check to see if there is a cons-node in the same equivalence 
;---   ;  class as NIL.  If so, H ^ ~C is again unsatisfiable, so H --> C
;---   ;  is valid(so return GOOD). Otherwise H ^ ~C is satisfiable, so return
;---   ;  an error message atom.
;---   ;  (actually a dotted pair is returned -- error-message.nil if 
;---   ;   H ^ ~C is satisfiable, GOOD.nil if the conclusion is an equal or 
;---   ;   negation of an equal term, otherwise GOOD.i where is the number of 
;---   ;   the assumption that yields the conclusion upon substitution of equals for
;---   ;   equals.)
;---   ;
;---   (Plet (result (cons '|Conclusion is not provable by equality.| nil)
;---        )
;---
;---       (Pif (unsatisfiable-graph) -->        
;---           (<- result (cons 'GOOD nil))
;---        fi)
;---
;---        result
;---   )
;---  )
;---               
;--- ) 'equality-error)
;---
;---)

(defun not-equal-term$ (term)
    (and (eql (kind-of-term term) 'FUNCTION)
         (eql (kind-of-term (righttype-of-function-term term)) 'VOID)
         (eql (kind-of-term (lefttype-of-function-term term)) 'EQUAL)
    )
)

;
; make all buckets empty, make disequality list empty 
; no new variables used yet, no nodes created yet
;

(defun init-equality ()
   (Ploop (local i 0)
         (while (< i num-buckets$))
         (do
	   ; (add-to-free-node-list (sel buckets$ (i)))
            (<- (sel buckets$ (i)) nil)
	    (<- (sel unknown-terms (i)) nil)
            (<- i (1+ i))
         )
   )
   (<- disequalities$ nil)            
;   (<- non-equality-assumption-formulas nil)
;   (<- non-equality-conclusion-formula nil)
   (<- num-nodes$ 0)
   (<- unknown-term-count 0)
)


(defun add-to-free-node-list (node-chain)
    (Ploop
        (local next nil)
        (while node-chain)
	(do
	    (<- (eligible-of-eq-node node-chain) nil)
	    (<- next (next-of-eq-node node-chain))
	    (<- (next-of-eq-node node-chain) nil)
	    (<- (previous-of-eq-node node-chain) nil)
	    (<- free-node-list (cons node-chain *-*))
	    (<- node-chain next)
	)
    )
)

; 
;  there was bad input -- throw equality-error with message 'message'
;
                         
(defun equality-error$ (message)
    (throw 'equality-error message))


;
;make two terms, u and v,  equal (make their equivalence classes in the graph
;    the same)
;

(defun do-equality (terms)
    (Pif (onep (length terms)) -->
        (eq-insert (car terms))
     || t -->
        (Ploop (local tm (car terms)
                     tms (cdr terms)
              )
              (while tms)
              (do
                 (eq-assert tm (car tms))
                 (<- tm (car tms))
                 (<- tms (cdr tms))
              )
        )
     fi)
)

(defun do-disequality (terms)
    (<- disequalities$ (cons terms disequalities$))
)                     


(defun unsatisfiable-graph ()
    (Ploop
        (local
	    diseqs             disequalities$
	    unsatisfiable      nil
	)
	(until (or (null diseqs) unsatisfiable))
	(do
	    (<- unsatisfiable
		(Ploop
		    (local
			rep1       (eq-insert (caar diseqs))
			terms      (cdar diseqs)
			all-equal  t
		    )
		    (until (or (null terms) (not all-equal)))
		    (do
			(Plet (rep (eq-insert (car terms)))
			     (<- all-equal (eql rep rep1))
			     (<- rep1 rep)
			     (<- terms (cdr terms))
			)
		    )
		    (result all-equal)
		)
	    )
	    (<- diseqs (cdr diseqs))
	)
	(result unsatisfiable)
    )
)


;
; return t if the nodes corresponding to terms u and v are in the same
;   equivalence class (and thus we may deduce that they are equal)
;

(defun eq-query (u v)
   (eql (eq-insert u) (eq-insert v)) 
)                      


;
; Make the nodes corresponding to terms u,v be in the same equivalence class
;   (thus u and v are made equal)
;   

(defun eq-assert (u v)
   
   (Plet (ToDo nil
         x nil
         y nil
         h nil
         dup nil
        )         

        (<- ToDo (cons (list (eq-insert u) (eq-insert v)) ToDo))
        (Ploop (while (not (equal ToDo nil)))
              (do
                 (<- x (caar ToDo))
                 (<- y (cadar ToDo))       ;remove a pair from the ToDo list
                 (<- ToDo (cdr ToDo))
                 
                 (Ploop (while (reprlink-of-eq-node x))
                       (do (<- x (reprlink-of-eq-node x))))
                 (Ploop (while (reprlink-of-eq-node y))
                       (do (<- y (reprlink-of-eq-node y))))
                                                                   
                 (Pif (not (eql x y)) -->
                                  
                     ; choose as the new representative the nodes who's
                     ; current equivalence class is larger.  Let x be
                     ; the name of the new representative.
                     ;
                     (Pif (> (reprcount-of-eq-node y) 
                                                 (reprcount-of-eq-node x)) -->

                         (Plet (temp x)
                              (<- x y)
                              (<- y temp))

                      || t --> 
                           nil
                      
                      fi)
                           

                      (<- (reprlink-of-eq-node y) x)
                      (<- (reprcount-of-eq-node x) (+ (reprcount-of-eq-node x)
                                                      (reprcount-of-eq-node y)))    

                      ; For each term(node) that had y as an operand have it
                      ;   now use x as operand wherever it used y before.
                      ;   Remove each node that gets changed in this way
                      ;   from its bucket, rehash, and check if an identical
                      ;   node exists in the new bucket.  If so, add the
                      ;   node and its duplicate to the ToDo list. If not,
                      ;   put the node in the bucket.
                      ;
                      (for (node-op-pair in (containers-of-eq-node y))
                           (do
                             (Plet (p-node (car node-op-pair)
                                   p-op (cadr node-op-pair))
 
                                  (<- (car (nthcdr (1- p-op) 
                                           (operands-of-eq-node p-node))) x)
                                  (Pif (eligible-of-eq-node p-node) -->
                                      
                                      (bucket-remove$ p-node)
                                      (<- h (hash$ (label-of-eq-node p-node) 
                                                   (operands-of-eq-node p-node)))
                                      (<- dup  (search-bucket$  h (label-of-eq-node 
                                             p-node) (operands-of-eq-node p-node)))
                                      (Pif dup -->
                                    
                                         (<- ToDo (cons (list p-node dup) ToDo))
      
                                       || t -->
                       
                                          (bucket-insert$ h p-node)
                    
                                       fi)


                                   || t --> 

                                      nil
                                     
                                   fi)
                             )
                          ) 
                      )
                      (<- (containers-of-eq-node x) (append (containers-of-eq-node x) 
                                                        (containers-of-eq-node y)))
                 
                  || t --> 

                     nil
                
                  fi)
              )
        )
   )
)                                     
                 
;
; delete node 'node' from the bucket array (and make the node ineligible)
;

(defun bucket-remove$ (node)

   (<- (previous-of-eq-node (next-of-eq-node node)) (previous-of-eq-node node))
   (<- (next-of-eq-node (previous-of-eq-node node)) (next-of-eq-node node))
   (<- (next-of-eq-node node) nil)
   (<- (previous-of-eq-node node) nil)
   (<- (eligible-of-eq-node node) nil)

)

;
; insert node 'node' into a bucket 'bucket 'in the bucket array.  If the bucket 
;   has no header yet, make one. (Also, make the node eligible)
;

(defun bucket-insert$ (bucket node)

   (Plet (head (sel buckets$ (bucket))
        )   
        (Pif (equal head nil) -->        ;if no header present, make one
             
            (<- (sel buckets$ (bucket)) (new-node$))
            (<- head (sel buckets$ (bucket)))
            (<- (previous-of-eq-node head) head)
            (<- (next-of-eq-node head) head)
      
         || t --> 

            nil

         fi)
             
         (<- (next-of-eq-node node) (next-of-eq-node head))
         (<- (previous-of-eq-node node) head)
         (<- (previous-of-eq-node (next-of-eq-node head)) node)
         (<- (next-of-eq-node head) node)       

         (<- (eligible-of-eq-node node) t)     
      
   )
)
 
;
; search in bucket 'bucket of the buckets array for a node which has
; a label-field equal to 'label' and has operand nodes EQ to those in 'operands'
; (return a pointer to the node if one is found, else 'nil')
;       

(defun search-bucket$ (bucket label operands)

    (Plet (head      (sel buckets$ (bucket))
          duplicate  nil
         )                         

         (Pif (not (equal head nil)) -->

            (Ploop (local current head)
               (do 
                  (<- duplicate current) 
                  (Pif (equal label (label-of-eq-node current)) -->
                
                      (Pif (equal (length operands)
                                        (length (operands-of-eq-node current))) -->
                                
                          (Ploop (local len  (length operands)
                                       n     0               )
                                (while (< n len))
                                (do 
                                  (Pif (not (eql (car (nthcdr n operands))
                                               (car (nthcdr n  (operands-of-eq-node
                                                                current))))) -->

                                        (<- duplicate nil)

                                     || t --> 

                                        nil

                                     fi)
                                     (<- n (1+ n))
                                 )
                           )
                       
                       || t --> 

                          (<- duplicate nil)

                       fi)
                                      
                   || t -->

                      (<- duplicate nil)
           
                   fi)   
                   (<- current (next-of-eq-node current))
               )
               (until (or duplicate (eql current head)))
               (result duplicate)
            )

         || t --> 

            nil

         fi)   
    )
)          

;
;if necessary create a node corresponding to this term and enter it in the graph
;return (pointer to) the node that is the representative of the equivalence
; class to which this term (node) belongs (all this relative to type type)
; 

(defun eq-insert (term)

   (Plet (fcn-id  (get-fcn-id$ term)
	 arg-pointers nil
         h nil
         eq-ins nil
         dup nil
        )          

	(Pif (not (and (consp fcn-id) (eql (car fcn-id) 'UNKNOWN-TERM))) -->
	    (<- arg-pointers
		(mapcar
		    #'eq-insert
		    (subterms-of-term term)
		)
	    )
	 fi)

        (<- h (hash$ fcn-id arg-pointers))

        ; see if a node already exists for this term.  If not make one.
        ;
        (<- dup (search-bucket$ h fcn-id arg-pointers))
        (Pif dup -->
            (Ploop (while (reprlink-of-eq-node dup))
                  (do 
                     (<- dup (reprlink-of-eq-node dup))
                  )
            ) 
            ;return eq-insert (= dup )
            dup                            

         || t -->
            (<- eq-ins (new-node$))
            (bucket-insert$ h eq-ins)
            (<- (label-of-eq-node eq-ins) fcn-id)
            (<- (operands-of-eq-node eq-ins) arg-pointers)
            (Plet (i 1)
                 (for (opnd in arg-pointers)
                      (do
                         (<- (containers-of-eq-node opnd) (cons (list eq-ins i) 
                                                    (containers-of-eq-node  opnd)))
                         (<- i (1+ i))
                      )
                 )
            )
            (<- (containers-of-eq-node eq-ins) nil)
            (<- (reprlink-of-eq-node eq-ins) nil)
            (<- (reprcount-of-eq-node eq-ins) 1)
            ;return eq-insert (= eq-ins)
            eq-ins       
         fi)
   )
)                                   

(defun convert-list-to-cons (expr)
    expr
)   

;
; return an identifier for a term (to be used as the label of a node)
;                                    

(defun get-fcn-id$ (term)
                    
  (Plet (term-kind (kind-of-term term))
       
    (Pif (eql term-kind 'UNIVERSE) -->
        (list 'u (level-of-universe-term term))

     || (equal term-kind 'VAR) -->
        (list 'v (id-of-var-term term))

     || (equal term-kind 'POS-NUMBER) -->
        (list 'i (number-of-pos-number-term term))

     || (eql term-kind 'TOKEN) -->
        (list 'a (atom-of-token-term term))
                       
     || (eql term-kind 'TERM-OF-THEOREM) -->
        (list 't (name-of-term-of-theorem-term term))

     || (member term-kind
	      '(PRODUCT FUNCTION LAMBDA QUOTIENT SET BOUND-ID-TERM)
	) -->
        (lookup-unknown-term term)

     || t -->
        (kind-of-term term)

     fi)
   )
)


(defun lookup-unknown-term (term)
    (Plet (bkt (rem (equal-term-hash term) num-buckets$))
	 (Ploop
	     (local
	          alist (sel unknown-terms (bkt))
		  entry nil
	     )
	     (while (not (null alist)))
	     (do
	          (<- entry (car alist))
		  (Pif (equal-terms term (car entry)) -->
		      (return (cdr entry))
		   fi)
	          (<- alist (cdr alist))
	      )
	     (result
	         (progn
		     (<- unknown-term-count (1+ unknown-term-count))
		     (Plet (uterm (list 'UNKNOWN-TERM unknown-term-count))
			  (<- (sel unknown-terms (bkt))
			      (cons (cons term uterm) *-*)
			  )
			  uterm
		     )
		 )
	     )
	 )
     )
)
    
;
; return a newly created node with all fields, except the identifier one, nil
;

(defun new-node$ ()
    (Pif (null free-node-list) -->
        (eq-node nil nil nil nil nil nil nil nil (get-node-iden$))
     || t -->
        (prog1 (car free-node-list) (<- free-node-list (cdr *-*)))
     fi)
)
                                                                  
;
; return an integer to be associated with a node as its unique identifier
;  (used in hashing as a "fake pointer" to the node)
;

(defun get-node-iden$ ()

   (<- num-nodes$ (1+ num-nodes$))
   num-nodes$

)

;
; return a hash value for a term           
;
(defun hash$ (function-symbol operand-list)
    (Plet (hval (sxhash function-symbol))
	 (for (opnd in operand-list)
	      (do
		  (<- hval (logxor (node-iden-of-eq-node opnd) (rot hval 1)))
	      )
	 )
	 (abs (rem hval num-buckets$))
     )
)

         

