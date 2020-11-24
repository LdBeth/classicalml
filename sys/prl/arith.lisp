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


;--
;-- arith (assns:declaration-list, concl:term, rule:??)
;--           
;--     This returns either the atom GOOD if the deduction succeeds or an
;--     atom whose print name is an error message if the deduction fails or
;--     its inputs are not of the form specified above.
;--

(defun arith (assns concl rule)
  (declare (ignore rule))
  (catch 
    'arith-result 
    (doarith$  (bust-conjunctions (ok-arith-assums$ assns)) concl)))



;--
;-- ok-arith-assums (assums:list-of-declarations)
;--
;--     Return a list of terms where each element of the list is a term of the 
;--     sort that arith can handle.
;--

(defun ok-arith-assums$ (assums)
    (Plet (ok-vars nil
          result  nil
         )
        (for (decl in assums)
             (do
                (Pif (null (id-of-declaration decl)) -->
                    (<- result (cons (type-of-declaration decl) result))
                 || t -->
                    (<- result
                        (cons (type-of-declaration decl)
                              (cons (equal-term
                                        'EQUAL 
                                        nil
                                        (type-of-declaration decl)
                                        (list (var-term 
                                                'VAR 
                                                nil
                                                (id-of-declaration decl)
                                              )
                                        )
                                    )
                                    result
                              )
                        )
                    )

                 fi)
             )
        )
        result
    )
)   
 




(defun is-independent-product (tm)
  (and 
     (eql (kind-of-term tm)  'PRODUCT)
     (eql (bound-id-of-product-term tm)  nil)))



; Given a list of nuprl terms, return a list of terms such
;  that none of the terms is a conjunction (indep. product).
;  Each independent-product term in input list is destructed into
;  their two constituent terms. 
; This allows Arith Rule to "reach inside" conjunctions, where it
;  used to ignore conjunctions as not being of valid Arith format.

(defun bust-conjunctions (tmlist)
  (cond
    
    ((null tmlist)  nil)
    
    (t
      (let* ((head  (car tmlist)))
	(cond 
	  ((is-independent-product head)
	   (append (bust-conjunctions (list (lefttype-of-product-term head)))
                   (append (bust-conjunctions (list (righttype-of-product-term head)))
			   (bust-conjunctions (cdr tmlist)))))

	  (t  (cons
		head
		(bust-conjunctions (cdr tmlist)))))))))







;--
;-- doarith$ (assums: term-list, concl:term)
;--
;--     Check if the conclusion (which may be a literal or a disjunction
;--     of literals) follows from the assumptions by considerations of
;--     arithmetic, simplification, and equality/list knowledge.
;--     Throw (with tag 'arith-result) the atom 'GOOD if the conclusion
;--     follows, an atom whose print name is an error message, otherwise.
;--
;--     Non-literals are ignored.
;--
;--     A "literal" here is an EQUAL or LESS term wrapped in any number of
;--     negations (-> VOIDs).  This allows users to define relational operators,
;--     such as a>=b as NOT(a<b), and then have NOT(...) be considered a literal.
;--

(global A-graph-literals$)           ;-- literals from assums and concl that give
                                     ;--   rise to edges in the A-graph -- this
                                     ;--   means < and ~< relations.  Each entry
                                     ;--   in the list is a triple: the relation
                                     ;--   (LESS or NOT-LESS), the simplified form
                                     ;--   of the left term, the simplified form of
                                     ;--   the right term.

(global A-disequalities$)            ;-- strict disequality literals contained
                                     ;--   in assums and concl between arithmetic
                                     ;--   terms -- this is a list of two element
                                     ;--   lists, each of which is: the simplified
                                     ;--   form of the left operand, the simplified
                                     ;--   form of the right operand.

(global A-nodes$)                    ;-- representatives in E-graph for the rest
                                     ;--   part of normal form terms entered
                                     ;--   into A-graph.  That is, each node in
                                     ;--   the A-graph is "named" by the (rep of
                                     ;--   the) class in the E-graph to which its
                                     ;--   normal form term (without constant part)
                                     ;--   belongs.

(global A-edges$)                    ;-- a list of 4 element lists, (si,ti,c,lit),
                                     ;--   where si and ti are A-node indices
                                     ;--   (1,2,...) indexing into A-nodes$,
                                     ;--   c is the weight of the edge from si
                                     ;--   to ti, and lit is the literal that
                                     ;--   gave rise to the edge.

(global A-matrix$)                   ;-- the weighted connectivity matrix over
                                     ;--   A-nodes$xA-nodes$ with entries from
                                     ;--   A-edges$.  (see build-matrices$)

(global L-matrix$)                   ;-- the literal matrix corresponding to
                                     ;--   A-matrix$.  (see build-matrices$)

(global A*-matrix$)                  ;-- the transitive closure of A-matrix$,
                                     ;--   containing max path weights in the
                                     ;--   A-graph.  (see build-matrices$)

(global A-size$)                     ;-- the size of the square matrices A-matrix$,
                                     ;--   L-matrix$, and A*-matrix$.

(global type-int$)
(<- type-int$ (int-term 'INT nil))

(defun doarith$ (assums concl)
   
    (<- A-disequalities$ nil)
    (<- A-graph-literals$ nil)
   
    (init-E-graph$)

    (process-assumptions$ assums)
    (process-conclusion$ concl)
    
    (propogate-A-E-equalities$)

    (do-A-disequalities$)

    (do-E-disequalities$)

    ;-- There is a choice of values for variables that makes the literals
    ;-- satisfiable.  Thus, the conclusion does not follow from the assumptions.
        (throw 'arith-result
               '|Conclusion does not follow from assumptions by ARITH.|
        )


)


;--
;-- process-assumptions$ (assums:term-list)
;--
;--     process each literal in assums
;--

(defun process-assumptions$ (assums)

    (for (a in assums)
         (do
             (process-literal$ a)
         )
    )

)


;--
;-- process-conclusion$ (concl:term)
;--
;--     negate the conclusion and process the resulting (conjunction of) literals
;--

(defun process-conclusion$ (concl)

    (Pif (eql (kind-of-term concl) 'UNION) -->
        (for (disjunct in (get-disjuncts$ concl))
             (do
                 (Pif (not-term$ disjunct) -->
                     (process-literal$ (not-term-body$ disjunct))
                  || t -->
                     (process-literal$ (make-not-term$ disjunct))
                  fi)
             )
        )
     || (not-term$ concl) -->
        (process-literal$ (not-term-body$ concl))

     || t -->
        (process-literal$ (make-not-term$ concl))

     fi)

)


;-- if concl is of the form 'x in T
(defun concl-suitable-for-A-graph$ (concl)
    (not (and (eql (kind-of-term concl) 'EQUAL)
              (onep (length (terms-of-equal-term concl)))
              (equal-terms (type-of-equal-term concl) type-int$)
         )
    )
)

(defun get-disjuncts$ (union-term)
    (Pif (eql (kind-of-term (righttype-of-union-term union-term)) 'UNION) -->
        (cons (lefttype-of-union-term union-term) 
              (get-disjuncts$ (righttype-of-union-term union-term))
        )
     || t -->
        (list (lefttype-of-union-term union-term) 
              (righttype-of-union-term union-term)
        )
     fi)
)

(defun not-term$ (term)
    (or (not-equal-term$ term) (not-less-term$ term))
)

(defun not-less-term$ (term)
    (and (eql (kind-of-term term) 'FUNCTION)
         (eql (kind-of-term (righttype-of-function-term term)) 'VOID)
         (eql (kind-of-term (lefttype-of-function-term term)) 'LESS)
    )
)

(defun not-term-body$ (term)
    (lefttype-of-function-term term)
)

(defun make-not-term$ (term)
    (function-term 'FUNCTION nil nil term (void-term 'VOID nil))
)


;--
;-- process-literal$ (literal:term)
;--
;--     Unwrap multiple levels of negation from literal and put it in
;--     A-graph, E-graph, or disequality list, as appropriate.
;--

(defun process-literal$ (literal)

    (Plet (poslit  literal ;-- the positive form of literal (literal with all
                          ;--   layers of negation stripped off)
          negated nil     ;-- non-nil if literal is the negation of poslit
          left    nil     ;-- the simplified form of poslit's left term
          right   nil     ;-- the simplified form of poslit's right term
          sterms   nil    ;-- if poslit is an equality, the list of simplified 
                          ;-- terms making up the terms of the equal-term poslit
         )

        (Ploop
            (while (not-term$ poslit))
            (do
                (<- negated (not negated))
                (<- poslit (not-term-body$ poslit))
            )
        )

        (Pif (eql (kind-of-term poslit) 'LESS) -->

            (<- left (simplify (leftterm-of-less-term poslit)))
            (<- right (simplify (rightterm-of-less-term poslit)))

            (assert-E-graph-equality$  
                (list (leftterm-of-less-term poslit) left)
            )
            (assert-E-graph-equality$  
                (list (rightterm-of-less-term poslit) right)
            )

            (Pif negated -->
                (<- A-graph-literals$ (cons (list 'NOT-LESS left right) *-*))

             || t -->
                (<- A-graph-literals$ (cons (list 'LESS left right) *-*))

             fi)

         || (and (eql (kind-of-term poslit) 'EQUAL)
                 (equal-terms (type-of-equal-term poslit) type-int$)
            ) -->
            (<- sterms (mapcar #'simplify
                               (terms-of-equal-term poslit)
                       )
            )

            (for (term in (terms-of-equal-term poslit))
                 (sterm in sterms)
                 (do
                    (assert-E-graph-equality$ 
                        (list term sterm)
                    )
                 )  
            )

            ;-- We have an arithmetic equality or disequality.  For an equality,
            ;-- since the nodes of the A-graph will not necessarily be left
            ;-- or right, but will be the rest parts of their normal forms,
            ;-- it is not adequate to simply assert this into the E-graph --
            ;-- we must treat it as left<=right & right <= left.  For a disequality,
            ;-- we save it and later see if left<right or right<left is satisfiable.
                (Pif (not negated) -->    
                    (for (left in sterms)
                         (right in (cdr sterms))
                         (do
                            (<- A-graph-literals$ 
                                (cons (list 'NOT-LESS left right) *-*)
                            )
                            (<- A-graph-literals$
                                (cons (list 'NOT-LESS right left) *-*)
                            )
                         )
                    )

                 || t -->
                    (Pif (= (length sterms) 2) -->
                        (<- A-disequalities$
                            (cons (list (car sterms) (cadr sterms)) *-*)
                        )
                     fi)

                 fi)

         fi)

    )    
)


;-- 
;-- propogate-A-E-equalities$ ()
;--
;--     Propogate equalities between the A-graph and the E-graph.
;--     If the A-graph ever becomes unsatisfiable, then throw the
;--     atom GOOD to tag arith-result.
;--

(defun propogate-A-E-equalities$ ()

    (Plet (new-equalities-generated nil    ;-- t iff E-graph has been changed since
                                          ;--   A-graph was built and processed
         )

        (<- new-equalities-generated t)
        (Ploop
            (while new-equalities-generated)
            (do
                (build-A-graph$)
                (build-matrices$ A-edges$)
                (<- new-equalities-generated (propogate-A-equalities-to-E-graph$))
            )
        )

    )
)


;--
;-- build-A-graph$()
;--
;--     Process A-graph-literals and build A-nodes$ and A-edges$
;--     using knowledge in the E-graph on what terms are equal.
;--

(defun build-A-graph$ ()

    (<- A-nodes$ nil)
    (<- A-edges$ nil)

    (for (lit in A-graph-literals$)
        (do
            (Plet (op      (car lit)   ;-- the literal's  operator (LESS/NOT-LESS)
                  a       (cadr lit)  ;-- the left operand of the literal
                  b       (caddr lit) ;-- the right operand of the literal
                  a-norm  nil         ;-- the normal form of a: (const rest)
                  b-norm  nil         ;-- the normal form of b: (const rest)
                 )

                (<- a-norm (norm-simplified-term$ a))
                (<- b-norm (norm-simplified-term$ b))

                (Pif (eql op 'LESS) -->
                    (add-LE-to-A-graph$ (list (1+ (car a-norm)) (cadr a-norm))
                                        b-norm
                                        lit
                    )

                 || t -->
                    (add-LE-to-A-graph$ b-norm a-norm lit)

                 fi)
            )
        )
    )
)


;--
;-- build-matrices$(edges)
;--
;--     Process A-nodes$ and edges and build the weighted connectivity
;--     matrix A, where A[i,j] = max weight edge from i to j and is
;--     minus-infinity if there is no edge from i to j.  Diagonal entries
;--     of A areis made to be 0 if they otherwise would be less than 0.
;--
;--     Build an associated matrix L, where for each non-diagonal entry
;--     of A, say A[i,j], that isn't minus-infinity, L[i,j] is the literal
;--     that gave rise to the entry of A.
;--
;--     Finally, construct A*, the transitive closure of A, where A*[i,j]
;--     is the weight of the maximum weight path in A from i to j.
;--
;--     If any diagonal entry of A* has weight greater than 0, there is a
;--     positive weight cycle in A so the literal set is unsatisfiable and
;--     we throw the atom 'GOOD to tag arith-result.  Otherwise we return nil.
;--

(defun build-matrices$ (edges)

    (Plet (matrix-changed  nil
         )

        ;-- set A-matrix$ to an "identity matrix" under (add,times)=(max,+)
            (<- A-size$ (length A-nodes$))
            (<- A-matrix$
		(make-array (list A-size$ A-size$) :initial-element 'minus-infinity))

            (Ploop
                (local i 0)
                (while (< i A-size$))
                (do
                    (setf (aref A-matrix$ i i) 0)
                    (<- i (1+ i))
                )
            )

            (<- L-matrix$ (make-array (list A-size$ A-size$)))

        ;-- add the edges into the identity matrix already formed,
        ;-- recording the generating literals in L-matrix$.
            (for (edge in edges)
                (do
                    (Plet (A-val     (aref A-matrix$ (1- (car edge))
                                               (1- (cadr edge))
                                    )
                          edge-val  (caddr edge)
                          edge-lit  (cadddr edge)
                         )

                        (Pif (or (eql A-val 'minus-infinity)
                                (> edge-val A-val)
                            ) -->
                            (setf (aref A-matrix$
                                       (1- (car edge))
                                       (1- (cadr edge))
                                   )
                                   edge-val
                            )
                            (setf (aref L-matrix$
                                       (1- (car edge))
                                       (1- (cadr edge))
                                   )
                                   edge-lit
                            )
                         fi)
                    )
                )
            )

        ;-- set A*-matrix$ to the transitive closure of A-matrix$
        ;-- under (add,times)=(max,+) throwing 'GOOD to 'arith-result
        ;-- if any diagonal entry becomes positive
            (<- A*-matrix$ (make-array (list A-size$ A-size$)))
            (Ploop
                (local i 0)
                (while (< i A-size$))
                (do
                    (Ploop
                        (local j 0)
                        (while (< j A-size$))
                        (do
                            (setf (aref A*-matrix$ i j)
                                   (aref A-matrix$ i j)
                            )
                            (<- j (1+ j))
                        )
                    )
                    (<- i (1+ i))
                )
            )

            (<- matrix-changed t)
            (Ploop
                (while matrix-changed)
                (do
                    (<- matrix-changed (matrix-square$ A*-matrix$ A-size$))
                    (Ploop
                        (local i 0)
                        (while (< i A-size$))
                        (do
                            (Pif (> (aref A*-matrix$ i i) 0) -->
                                (throw 'arith-result 'GOOD)
                             fi)
                            (<- i (1+ i))
                        )
                    )
                )
            )

        nil

    )
)


;--
;-- matrix-square$ (A:array,size:integer)
;--
;--     Set A, a size*size 2 dimensional array, to A*A where (add,times)=(max,+).
;--     Return t if A*A differs from A, else nil.

(defun matrix-square$ (A size)

    (Plet (B (make-array (list size size))     ;-- to hold A*A temporarily
          x nil
          matrix-changed nil
         )

        (Ploop
            (local i 0)
            (while (< i size))
            (do
                (Ploop
                    (local j 0)
                    (while (< j size))
                    (do
                        (<- x 'minus-infinity)
                        (Ploop
                            (local k 0)
                            (while (< k size))
                            (do
                                (<- x (max-edge-weight$
                                          x
                                          (sum-edge-weight$
                                              (aref A i k)
                                              (aref A k j)
                                          )
                                      )
                                )
                                (<- k (1+ k))
                            )
                        )
                        (setf (aref B i j) x)
                        (Pif (not (equal (aref A i j) x)) -->
                            (<- matrix-changed t)
                         fi)
                        (<- j (1+ j))
                    )
                )
                (<- i (1+ i))
            )
        )

        (Ploop
            (local i 0)
            (while (< i size))
            (do
                (Ploop
                    (local j 0)
                    (while (< j size))
                    (do
                        (setf (aref A i j) (aref B i j))
                        (<- j (1+ j))
                    )
                )
                (<- i (1+ i))
            )
        )

        matrix-changed

    )
)

                              
;--
;-- max-edge-weight$(x:weight,y;weight)
;--
;--     Return the maximum of x and y as edge weights.  Edge weights are either numbers
;--     or the symbol 'minus-infinity, which is less than any number.
;--

(defun max-edge-weight$ (x y)

    (Pif (eql x 'minus-infinity) --> y
     || (eql y 'minus-infinity) --> x
     || t --> (max x y)
     fi)

)


;--
;-- sum-edge-weight$(x:weight,y:weight)
;--
;--    Return the sum of x and y as edge weights.  This is their integer sum,
;--    unless one is minus-infinity, in which case the sum is minus-infinity.
;--

(defun sum-edge-weight$ (x y)

    (Pif (eql x 'minus-infinity) --> 'minus-infinity
     || (eql y 'minus-infinity) --> 'minus-infinity
     || t --> (+ x y)
     fi)

)


;--
;-- propogate-A-equalities-to-E-graph$()
;--
;--     Examine the A, L, and A* matrices and propogate the knowledge produced by
;--     zero weight cycles to the E-graph.  If the E-graph is changed as a result
;--     of sending it this knowlegde (equalities) then yield t, otherwise yield nil.
;--
;--     Given a zero weight cycle in A, say: 
;--
;--              w1     w2     wn-1
;--           t1---->t2---->...---->tn = t1
;--
;--     we deduce that t1+w1=t2, t2+w2=t3, ..., tn-1+wn-1=t1.  In order that the
;--     E-graph get some equalities between terms it already knows about, we take
;--     each of these equalities and find the literal that generated its edge.
;--     Such a literal is either a<b or ~a<b.  In the second case, ~a<b generated
;--     the relation b<=a, b and a were normalized to br+bc<=ar+ac (xr means rest
;--     part of x, xc means const part of x), and an edge br--->ar with weight bc-ac
;--     was generated.  Thus, br+(bc-ac)=ar means br+bc=ar+ac, which in turn means
;--     that b=a.  Similarly, the first form of literal, a<b, generates the equality
;--     a=b-1.
;--
;--     Notes:
;--       - we we have chosen what equalities (among the many possible) to propogate
;--         to the E-graph, and some other choice might be better.
;--
;--       - since every node is equal to itself, and the E-graph already knows this,
;--         we do not propogate such equalities.
;--
;--       - the cycle in which an edge participates has no bearing on what equality
;--         we generate for it, thus below we look for the edges that participate in
;--         zero weight cycles, but don't really find the cycles.  Now, an edge (i,j)
;--         participates in such a cycle iff it can be viewed as the last edge in the
;--         cycle.  This means that j must be a node that occurs in a zero weight cycle.
;--         Given that the graph has no positive weight cycles, a node j occurs in a
;--         zero weight cycle iff A*[j,j]=0.  So we consider those j for which this is
;--         the case.  Now, the edge (i,j) of weight w is the last edge in a path from
;--         j to j iff the max weight path from j to i has weight -w (ie, A*[j,i]=-w),
;--         because if it were greater than -w then there would be a positive weight
;--         path from j to j (which we have forbidden), and if it were less than -w then
;--         the max weight of a path j-->...-->i-->j would be less than zero.  Finally,
;--         if A[i,j]=w and A*[j,i]=-w then A*[j,j]=0, so we needn't check that. Thus,
;--         an edge (i,j) participates in a zero weight cycle iff A[i,j]=-A*[j,i].
;--

(defun propogate-A-equalities-to-E-graph$ ()

    (Ploop
        (local i                        0
               new-equalities-generated nil
        )
        (while (< i A-size$))
        (do
            (Ploop
                (local j   0
                       lit nil
                )
                (while (< j A-size$))
                (do
                    (Pif (and (not (equal i j))
                             (not (eql (aref A*-matrix$ j i)
                                      'minus-infinity
                                  )
                             )
                             (equal (aref A-matrix$ i j)
                                    (- (aref A*-matrix$ j i))
                             )
                        ) -->
                        (<- lit (aref L-matrix$ i j))
                        (Pif (eql (car lit) 'LESS) -->
;-- at this point we would like to assert (cadr lit)+1=(caddr lit)
;-- or (cadr lit)=(caddr lit)-1.  For now, we do nothing.
nil
                         || t -->
                            (<- new-equalities-generated
                                (or (assert-E-graph-equality$
                                        (list (cadr lit)
                                              (caddr lit)
                                        )
                                    )
                                    *-*
                                )
                            )

                         fi)
                     fi)
                    (<- j (1+ j))
                )
            )
            (<- i (1+ i))
        )
        (result new-equalities-generated)
    )
)

;-- 
;-- norm-simplified-term$(q:term)
;--
;--     Given a simplified term q, return a normal form for the term.
;--     The normal form is a list of two elements (const rest), where
;--     const is an integer and rest is a prl term.
;--
;--     Simplified terms are assumed to be prlterms which together with
;--     this function have the property that
;--
;--         for any q,s:term . 
;--             q=s under the ring axioms,
;--             qn=norm-simplified-term$(simplify(q)),
;--             sn=norm-simplified-term$(simplify(s))  ==> 
;--                    const-part(qn)=const-part(sn) &
;--                    equal-term(rest-part(qn),rest-part(sn)).
;--
;--     Also, the normal form has the property that when a term is changed
;--     by adding/subtracting an integer the normal form changes only in
;--     the constant part.  That is,
;--
;--         for any q:term, c:integer .
;--             equal-term(rest-part(norm-simplified-term$(simplify(q))),
;--                        rest-part(norm-simplified-term$(simplify(ADD q c)))
;--                       )
;--

(defun norm-simplified-term$ (q)

    (Pif (eql (kind-of-term q) 'POS-NUMBER) -->
        (list (number-of-pos-number-term q)
              (pos-number-term 'POS-NUMBER nil 0)
        )

     || (and (eql (kind-of-term q) 'MINUS)
             (eql (kind-of-term (term-of-minus-term q)) 'POS-NUMBER)
        ) -->
        (list (- (number-of-pos-number-term (term-of-minus-term q)))
              (pos-number-term 'POS-NUMBER nil 0)
        )

     || (and (eql (kind-of-term q) 'ADD)
             (eql (kind-of-term (leftterm-of-binary-term q)) 'POS-NUMBER)
        ) -->
        (list (number-of-pos-number-term (leftterm-of-binary-term q))
              (rightterm-of-binary-term q)
        )

     || (and (eql (kind-of-term q) 'ADD)
             (eql (kind-of-term (leftterm-of-binary-term q)) 'MINUS)
             (eql (kind-of-term
                      (term-of-minus-term (leftterm-of-binary-term q))
                 )
                 'POS-NUMBER
             )
        ) -->
        (list (- (number-of-pos-number-term
                         (term-of-minus-term (leftterm-of-binary-term q))
                     )
              )
              (rightterm-of-binary-term q)
        )

     || t -->
        (list 0 q)

     fi)

)


;--
;-- add-LE-to-A-graph$(q:norm-arith-term, r:norm-arith-term, lit:literal)
;--
;--     Add the relationship q<=r to the arithmetic graph.
;--
;--     This is done by entering an edge from the rest part of q to the rest
;--     part of r with weight (const part of q)-(const part of r).  The edge
;--     is annotated with lit, the literal that gave rise to the edge.
;--


(defun add-LE-to-A-graph$ (q r lit)

    (Plet (qi (A-node-index$ (cadr q))   ;-- index of rest part of q in A-nodes$
          ri (A-node-index$ (cadr r))   ;-- index of rest part of r in A-nodes$
         )

        (<- A-edges$ (cons (list qi ri (- (car q) (car r)) lit)
                           *-*
                     )
        )

    )
)


;--
;-- A-node-index$(q:term)
;--
;--     Return the index of (the class of) q in A-nodes$ (1,2,...).
;--     If q does not occur in A-nodes$, then add it and return its index.
;--

(defun A-node-index$ (q)

    (Plet (nodes A-nodes$      ;-- nodes of A-nodes$ not yet examined for q
          index 1             ;-- index of (car nodes) in A-nodes$
          class nil           ;-- the class in the E-graph into which q falls
         )

        (<- class (E-graph-class$ q ))

        (Ploop
            (while (and (not (null nodes))
                        (not (eql class (car nodes)))
                   )
            )
            (do
                (<- index (1+ index))
                (<- nodes (cdr nodes))
            )
        )

        (Pif (null nodes) -->
            (<- A-nodes$ (append *-* (list class)))
            (length A-nodes$)

         || t -->
            index

         fi)

    )
)


;--
;-- do-A-disequalities$()
;--
;--     Check whether the disequalities together with the A-graph are satisfiable.
;--     If not, throw 'GOOD to 'arith-result.
;--

(defun do-A-disequalities$ ()

    (Plet (diseq   nil     ;-- a member of A-disequalities$, so a two element list (a,b)
          an      nil     ;-- the normal form of a
          bn      nil     ;-- the normal form of b
          d-edges nil     ;-- the disequality edges built from A-disequalities$
         )

        ;-- build d-edges by turning each member of A-disqualities$, a pair (a,b) of
        ;-- simplified terms, into a edge (ai bi c nil) where ai and bi are the rest
        ;-- parts of the normal forms of a and b, and c is (const a)-(const b).
            (for (diseq in A-disequalities$)
                (do
                    (<- an (norm-simplified-term$ (car diseq)))
                    (<- bn (norm-simplified-term$ (cadr diseq)))
                    (<- d-edges (cons (list (A-node-index$ (cadr an))
                                            (A-node-index$ (cadr bn))
                                            (- (car an) (car bn))
                                            nil  ;-- the literal doesn't matter now
                                      )
                                      *-*
                                )
                    )
                )
            )

        (Pif (not (test-disequality-satisfiability$ d-edges A-edges$)) -->
            ;-- literal set is not satisfiable, so deduction is valid
                (throw 'arith-result 'GOOD)
         fi)

    )
)


;--
;-- test-disequality-satisfiability$(disequality-edges:list, edges:list)
;--
;--     Build a graph of weighted edges from the elements of edges.   Each element
;--     of disequality-edges represents a pair of nodes that are disequal.  For each of
;--     the (exponential number of) possible orderings of these nodes (x<y or y<x)
;--     test if the augmented A-graph is satisfiable and return t if some ordering
;--     Is satisfiable, otherwise return nil.  A graph is satisfiable exactly when
;--     it contains no cycles of weight > 0.
;--

(defun test-disequality-satisfiability$ (disequality-edges edges)

    (Pif (not (null disequality-edges)) -->
        ;-- try each ordering of the first disequality and test satisfiability of
        ;-- the remainder under that ordering.
            (Plet (first-dis (car disequality-edges)
                  rest-dis  (cdr disequality-edges)
                 )

                (or (test-disequality-satisfiability$
                        rest-dis
                        (cons (list (car first-dis)
                                    (cadr first-dis)
                                    (1+ (caddr first-dis))
                                    nil  ;-- the literal is irrelevant now
                              )
                              edges
                        )
                    )
                    (test-disequality-satisfiability$
                        rest-dis
                        (cons (list (cadr first-dis)
                                    (car first-dis)
                                    (- (1- (caddr first-dis)))
                                    nil  ;-- the literal is irrelevant now
                              )
                              edges
                        )
                    )
                )
            )

     || t -->
        ;-- there are no disequalities -- build the graph and check it for positive cycles
        ;-- by building the transitive closure of the graph in a matrix and checking if the
        ;-- diagonal ever has an entry > 0.  If this happens, return nil, else t.
            (not (eql (catch 'arith-result (build-matrices$ edges)) 'GOOD))

     fi)
)



;--------------------------------;
;                                ;
;      E-graph Interface         ;
;                                ;
;--------------------------------;

;--
;-- init-E-graph$()
;--
;--     Initialize the equality box.
;--

(defun init-E-graph$ ()

    (init-equality)

)


;--
;-- assert-E-graph-equality$(termlist:list of prlterms)
;--
;--     Assert the relation t=..=t' in T in the E-graph.  Return t if this was 
;--     not previously known to the E-graph, nil otherwise.
;--

(defun assert-E-graph-equality$ (termlist)
    (Ploop
        (local
	    terms   (cdr termlist)
	    term    (car termlist)
	    rep     (E-graph-class$ (car termlist))
	)
	(while (not (null terms)))
	(do
	    (Pif (not (eql rep (E-graph-class$ (car terms)))) -->
		(return (progn (do-equality (cons term terms)) t))
	     fi)
	    (<- term (car terms))
	    (<- terms (cdr terms))
	)
	(result nil)
    )
)



;--
;-- assert-E-graph-disequality$(termlist:list of prlterms)
;--
;--     Add the knowledge ~(t=..=t' in T) to the E-box.
;--

(defun assert-E-graph-disequality$ (termlist)

    (do-disequality termlist)

)


;--
;-- E-graph-class$(a:term)
;--
;--     Return the representative for a (with type T) in the E-graph.  If a does 
;--     not occur in the E-graph, add it and return its representative.
;--

(defun E-graph-class$ (a)

    (eq-insert a)

)


;--
;-- do-E-disequalities$()
;--
;--     Check whether the E-graph has any conflict with the disequalities
;--     that have been asserted into it.  If so, the literal set is not
;--     satisfiable, so throw 'GOOD to 'arith-result.

(defun do-E-disequalities$ ()

    (for (diseq in A-disequalities$)
	 (do
	   (do-disequality diseq)
	 )
    )
 
    (Pif (unsatisfiable-graph) --> (throw 'arith-result 'GOOD)
     fi)

)
