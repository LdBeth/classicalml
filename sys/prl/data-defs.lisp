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


;------------------------------;
;                              ;
;       Term Definitions       ;
;                              ;
;------------------------------;


;-- Terms are built as a union of the following forms
;--
;--
;--     ('UNIVERSE level)  where level is a positive integer
;--            
;-      ('VOID)
;--          ('ANY term)
;--
;--     ('ATOM)
;--          ('TOKEN atom)  where atom is a list of fixnums
;--                         (parsing "xy" would yield 
;--                                       (TOKEN (Ttree 120 121) (120 121)))
;--
;--     ('INT)
;--          ('POS-NUMBER number) where num is a NON-NEGATIVE number 
;--                               ;;;;;this name obviously should change 
;--          ('MINUS term)
;--          (binary leftterm rightterm)  where binary is 'ADD, 'SUB, 'MUL', 'DIV, 'MOD
;--          ('IND value downterm baseterm upterm)
;--                         
;--     ('LIST type)                                          
;--          ('NIL)
;--          ('CONS head tail) where head and tail are terms                   
;--          ('LIST-IND value baseterm upterm) 
;--                     
;--     ('UNION lefttype righttype)
;--          (injection term)    where injection is 'INL, 'INR
;--          ('DECIDE value leftterm rightterm) where value is a term
;--          
;--     ('PRODUCT bound-id lefttype righttype)
;--          ('PAIR leftterm rightterm)
;--          ('SPREAD value term)
;--                        
;--     ('FUNCTION bound-id lefttype righttype)
;--          ('LAMBDA bound-id term)
;--          ('APPLY function arg) where function and arg are terms
;--
;--	('PARFUNCTION bound-id lefttype righttype)
;--	     ('FIX bound-id-term-list id)
;--	     ('APPLY-PARTIAL function arg)
;--          ('DOM arg)
;--
;--	('RECURSIVE  bound-id-list-term fix-term rec-id term )
;--	     ('REC-IND term  bound-id-list-term id )
;--
;--     ('BOUND-ID-LIST bound-ids term-list)
;--                     used in terms that have a subterm of the form
;--                     f1,y1.b1;....fn,yn.bn where the fi's are bound in every bj.
;--
;--     ('SIMPLE-RECURSIVE bound-id term)
;--          ('SIMPLE-REC-IND  value term)
;--
;--     ('QUOTIENT bound-ids lefttype righttype)
;--
;--     ('SET bound-id lefttype righttype)
;--       
;--     ('EQUAL type (- term -))
;--          ('AXIOM)
;--
;--     ('LESS leftterm rightterm)
;--                                                     
;--     ('VAR id)
;--     ('BOUND-ID-TERM bound-ids term)
;--
;--     ('TERM-OF-THEOREM name)
;--
;--     (decision-kind leftterm rightterm if-term else-term)
;--                                where decision is 'ATOMEQ, 'INTEQ, 'INTLESS
;--
;--     ('TAGGED tag term)
;--               tag is a non-negative integer
;--

						
;-- Each kind of term is described by a tuple definition.	
;-- In addition to the term kind and appropriate additional
;-- information, each term object provides the best Ttree
;-- "it knows about" for displaying it to the user.  If this
;-- is NIL then the term must be displayed by brute force.

(deftuple            term kind Ttree)
(deftuple   universe-term kind Ttree level)
(deftuple       void-term kind Ttree)
(deftuple        any-term kind Ttree term)
(deftuple       atom-term kind Ttree)
(deftuple      token-term kind Ttree atom)
(deftuple        int-term kind Ttree)
(deftuple pos-number-term kind Ttree number)
(deftuple      minus-term kind Ttree term)
(deftuple     binary-term kind Ttree leftterm rightterm)
(deftuple        ind-term kind Ttree value downterm baseterm upterm)
(deftuple       list-term kind Ttree type)
(deftuple        nil-term kind Ttree)
(deftuple       cons-term kind Ttree head tail)
(deftuple   list-ind-term kind Ttree value baseterm upterm)
(deftuple      union-term kind Ttree lefttype righttype)
(deftuple  injection-term kind Ttree term)
(deftuple     decide-term kind Ttree value leftterm rightterm)
(deftuple    product-term kind Ttree bound-id lefttype righttype)
(deftuple       pair-term kind Ttree leftterm rightterm)
(deftuple     spread-term kind Ttree value term)
(deftuple   function-term kind Ttree bound-id lefttype righttype)
(deftuple     lambda-term kind Ttree bound-id term)
(deftuple      apply-term kind Ttree function arg)
(deftuple   quotient-term kind Ttree bound-ids lefttype righttype)
(deftuple        set-term kind Ttree bound-id lefttype righttype)
(deftuple      equal-term kind Ttree type terms)
(deftuple      axiom-term kind Ttree)
(deftuple       less-term kind Ttree leftterm rightterm)
(deftuple        var-term kind Ttree id)
(deftuple   bound-id-term kind Ttree bound-ids term)
(deftuple term-of-theorem-term kind Ttree name)
(deftuple        decision-term kind Ttree leftterm rightterm if-term else-term)
(deftuple     parfunction-term kind Ttree bound-id lefttype righttype)
(deftuple   bound-id-list-term kind Tree bound-ids term-list)
(deftuple             fix-term kind Ttree bound-id-list-term id )
(deftuple             dom-term kind Ttree term)
(deftuple   apply-partial-term kind Ttree function arg)
(deftuple       recursive-term kind Ttree bound-id-list-term fix-term id term)
(deftuple         rec-ind-term kind Ttree term bound-id-list-term id)
(deftuple          tagged-term kind Ttree tag term)  
(deftuple      simple-rec-term kind Ttree bound-id term)
(deftuple  simple-rec-ind-term kind Ttree value term)
(deftuple          object-term kind Ttree)
(deftuple    unknown-type-term kind Ttree number)  ;-- for equality dec. proc.
                                                   ;-- (UNKNOWN-TYPE number)



;---------------------------------------;
;                                       ;
;       Scanner Token Definitions       ;
;                                       ;
;---------------------------------------;


;-- This has to be 1 more than the value of the largest token value.
(constant nbr-token-types 72)

(constant TAny        0)
(constant TArrow      1)
(constant TAt         2)
(constant TAtom       3)
(constant TBADCHAR    4)
(constant TBslash     5)
(constant TColon      6)
(constant TComma      7)
(constant TDecide     8)
(constant TEndInput   9)
(constant TEqual     10)
(constant TFunction  11)  
(constant TGreater   12)
(constant TId        13)
(constant TIn        14)
(constant TInd       15)
(constant TInl       16)
(constant TInr       17)
(constant TInt       18)
(constant TLbrace    19)
(constant TLeft      20)
(constant TLess      21)
(constant TList-ind  22)
(constant TList      23)
(constant TLparen    24)
(constant TMinus     25)
(constant TMod       26)
(constant TNbr       27)
(constant TNew       28)
(constant TNil       29)
(constant TOr        30)
(constant TOver      31)
(constant TPeriod    32)
(constant TPlus      33)
(constant TProduct   34)
(constant TPsign     35)
(constant TQuot      36)
(constant TQuote     37)
(constant TQuotient  38)
(constant TRbrace    39)
(constant TRight     40)
(constant TRparen    41)
(constant TScolon    42)
(constant TShriek    43)
(constant TSlash     44)
(constant TSpread    45)
(constant TStar      46)
(constant TSet       47)
(constant TToken     48)
(constant TUnion     49)
(constant TUniv      50)
(constant TUniverse  51)
(constant TVoid      52)
(constant TAxiom     53)
(constant TUsing     54)    
(constant TTofTh     55)
(constant TAtomeq    56)
(constant TInteq     57)
(constant TIntless   58)
(constant TDquote    59)
(constant TMlchar    60)
(constant TLsqrbrace 61)
(constant TRsqrbrace 62)
(constant TParFunArrow 63)
(constant TTilda     64)
(constant TFix       65)
(constant TRec       66)
(constant Trec-ind   67)
(constant TDom       68)
(constant TDblLsqrbrace 69)
(constant TLet       70)
(constant TObject    71)

;--------------------------------------;
;                                      ;
;       Text Tree Definitions          ;
;                                      ;
;--------------------------------------;


;-- A Ttree is a list, beginning with the atom Ttree, of
;--
;--    1) characters (in numeric form), including NL indicating
;--       a new line.
;--
;--    2) definition references, which have the form
;--
;--         (def-name actual-1 ... actual-n)
;--
;--       where each actual is a Ttree and n is the number of
;--       formal parameters in the template named by def-name.

(defun name-of-def-ref (def-ref) (car def-ref))
(defun actuals-of-def-ref (def-ref) (cdr def-ref))

(constant the-null-Ttree '(Ttree))


;-- In order to speed up display during Ttree editing,
;-- the initial Ttree in raw objects is raw-object-Ttree.
;-- This makes it most likely that a NL-suffix will be
;-- valid during editing.  Since semantics ignore NL,
;-- this object is essentially equivalent to the null-Ttree

(constant raw-object-Ttree '(Ttree 0))

(defun null-Ttree (Tt)
    (or (null (cdr Tt))
        (and (null (cddr Tt))
             (equal (cadr Tt) NL)
        )
    )
)

;-- A cursor into a Ttree is a non-empty list of positive numbers:
;--
;--    1) a single number, n>0, denoting the n'th element of a Ttree
;--       (where the leading atom (Ttree) is numbered 0), thus denoting
;--       either a character, def-ref, or if n is equal to the length
;--       of the list then denoting the 'end-of-list' rather than any
;--       element of the list,
;--
;--    2) a cursor with two more numbers at the end of the list, c, n,
;--       denoting the n'th element of the c'th child of the element
;--       denoted by the initial cursor (where the initial cursor must
;--       denote a def-ref, but n>0 can specify any element of the c'th
;--       child, including end-of-list).
;--
;-- Note that a cursor selects a character, a def-ref, or specifies the
;-- end of a list, but never selects a sequence of elements (i.e., never
;-- selects a Ttree).
;--

;-- A 'generated' Ttree is a list of fixnums.  It is produced from another
;-- Ttree recursively applying all definition references to get their right
;-- hand sides and taking the frontier of the result.

;-- A 'normal' Ttree is one in which all references to formal variables are 
;-- of the form (FORMAL.id) and not of the form <id>. 


;---------------------------------------------------------;
;                                                         ;
;       Proof Tree Definitions                            ;
;            (Rules are in rule-defs)                     ;
;                                                         ;
;---------------------------------------------------------;

;-- Declarations  (these are what appear on the left hand side of goals.)

(deftuple declaration
    Ttree                  ;-- the best Ttree for the declaration
    id                     ;-- the name bound to the term being assumed (id:T)
    type                   ;-- a term, the type being assumed
)


;-- Proof trees

(deftuple proof-tree
    assumptions            ;-- a list of declarations
    conclusion             ;-- a term
    rule-body              ;-- the Ttree for the rule used
    rule                   ;-- the rule used (nil, if bad)
    children               ;-- a list of proof-trees, nil if the rule was bad
    status                 ;-- the status of this proof node
    hidden                 ;-- A list of the (numbers of) the assumptions
                           ;-- that cannot be referenced at this node.
)


;--------------------------------------;
;                                      ;
;       Object Definitions             ;
;                                      ;
;--------------------------------------;


;-- Objects are the values of atoms of the form OBJ-name and
;-- OLDOBJ-name.  The valid names are all those names in the
;-- library together with the names of all functions defined
;-- in good rec-fcn definition blocks.

;--  I M P O R T A N T   N O T E --
;--
;--    Since the 'copy-prlobject' function is capable of copying
;--    only lists, dotted pairs, atoms and hunks, 
;--    any arrays which occur anywhere in prl objects
;--    must be handled as a special case.  Thus,
;--
;--    CHANGES TO THESE OBJECT DEFINITIONS INVOLVING ARRAYS
;--    MAY REQUIRE CORRESPONDING CHANGES IN:
;--        the ARCHIVE command code in prl.l


(Pdeftype object
    (status             ;-- {COMPLETE, PARTIAL, BAD, RAW}
                        ;--   For archived objects, status=RAW.
     kind               ;-- {EXT = extraction, THM = theorem,
                        ;--  DEF = definition, REC = rec-functions
                        ;-- }
     value              ;-- Object with type corresponding to kind.
     referenced-by      ;-- List of names of library objects which
                        ;--   REFERENCE THIS OBJECT.
     references         ;-- List of names of library objects which
                        ;--   THIS OBJECT REFERENCES.
    )
)

(Pdeftype ml-object
    (body               ;-- raw Ttree of object
    )
)

(Pdeftype eval-object
    (body               ;-- raw Ttree of object
    )
)

;-- the next two variables are required to mimic the power of
;-- dependent type definitions in the type 'definition-object'.

(global num-formals)
(eval-when (eval load compile)
    (<- num-formals 1)
)

(Pdeftype definition-object
    (body               ;-- raw Ttree of object

     num-formals        ;-- num of formals in template (each formal
                        ;--   in a template can occur only once)

     formal     array ((1+ num-formals))
         (name          ;-- the name and descriptor for each formal,
          descriptor    ;--   1..num-formals.  Note that num-formals in the
                        ;--   bounds is a global variable that must
                        ;--   be set before each (new ...) evaluation.
                        ;--   Name and descriptor hold strings.
         )

     lhs-text   array ((1+ num-formals))                    
                        ;-- array 0..num-formals of string
                        ;--     the lhs of the template is the sequence of all
                        ;--     lhs-text strings with formal[i] just before
                        ;--     lhs-text[i], for i=1..num-formals

     rhs                ;-- Ttree for rhs - it is in normal form
    )
            ;-- Only the first field is defined unless status=complete
)


(Pdeftype theorem-object
    (goal-body              ;-- the raw Ttree of the top level goal
     proof-rep-type         ;-- 'RULE-BODY-TREE or 'PROOF-TREE
     proof-representation   ;-- Represenation of the proof whose kind is
                            ;-- given by proof-rep-type.  These two fields
                            ;-- should never be directly accessed.  The
                            ;-- functions get-proof-of-theorem-object and
                            ;-- set-proof-of-theorem-object should be used
                            ;-- instead.
     saved-status           ;-- If proof-rep-type is 'RULE-BODY-TREE, then this is
                            ;-- the status the object had when it was squashed.
     extracted-term         ;-- the term extracted from the proof
     conclusion             ;-- the parsed goal body.
    )
            ;-- if goal-body is good, then proof is non-NIL
)



;
;(Pdeftype theorem-object
;    (goal-body              ;-- the raw Ttree of the top level goal
;     proof                  ;-- the refinement tree, of type proof-tree
;     extracted-term         ;-- the term extracted from the proof
;    )
;            ;-- if goal-body is good, then proof is non-NIL
;)




;---------------------------------;
;                                 ;
;       REGION DESCRIPTORS        ;
;                                 ;
;---------------------------------;

              
;-- Part of the display is organized as regions.  The Ttree and 
;-- refinement editors (ted,red) work with entities in regions --
;-- ted has one region showing the Ttree, red has multiple regions
;-- for showing one level of the proof and the Ttree's within that
;-- level.  Regions are rectangular areas within specifed windows.


(constant max-num-regions 40)

(Pdeftype region-array
    array (max-num-regions)
        (obj-name       ;-- library name of object being viewed (or nil
                        ;--   if this is a TTREE region associated with,
                        ;--   and thus subsidiary to, a PROOF region --
                        ;--   or nil if this is an EVAL region)
         obj-kind       ;-- PROOF or TTREE or EVAL (which is identical to
                        ;--   TTREE except that when killed special
                        ;--   processing is done)
         view-kind      ;-- EDIT or SHOW
         window         ;-- number of the window containing this region
         top            ;-- borders of region --
         left           ;--   these are coordinates within the window
         bot            ;--   (somewhere within (0,0) to the other corner)
         right          ;--
         allowed-events ;-- menu events allowed for this region (window),
                        ;--   these are a subset of {KILL,SIZE}
         assoc-region   ;-- the 'other' region # if this is one of a pair of
                        ;--   PROOF region and its subsidiary TTREE region
         descriptor     ;-- the proof/Ttree descriptor for the region contents
         modified       ;-- T iff the entity being viewed has been changed
                        ;--   by edit commands
        )
)

(global region region-array)
(global num-regions)            ;-- 0 <= num-regions <= max-num-regions
(global cur-region-index)       ;-- if num-regions>0 then
                                ;--       0 <= cur-region-index < num-regions
(global free-regions)           ;-- the set {0..max-num-regions-1} is split
(global used-regions)           ;--   into used and free regions -- used
                                ;--   regions contain actively displayed text
(global cur-region)             ;-- cur-region is the cur-region-index'th
                                ;--   element of used-regions
(global view-stack)             ;-- a list of view descriptions for all the
                                ;--   active views.  The list is maintained
                                ;--   in time order of creation, most recent
                                ;--   at the head of the list.

(deftuple view                  ;-- 
    name                        ;-- name of entity being viewed. Names are
                                ;--   either OBJ-name, OLDOBJ-name, or nil
                                ;--   if the view is not of a lib entry
                                ;--   (but is of part of a proof)
    region                      ;-- region of object being displayed.  TTREE
                                ;--   objects have their region number here.
                                ;--   PROOF objects have the region of their
                                ;--   proof part here.
    slot                        ;-- the slot number holding the view.  Slots
                                ;--   are numbered 0..3. They look thus:
                                ;--             -------------
                                ;--             |     |     |
                                ;--             |  0  |  2  |
                                ;--             |     |     |
                                ;--             |-----|-----|
                                ;--             |     |     |
                                ;--             |  1  |  3  |
                                ;--             |     |     |
                                ;--             |-----------|
                                ;--             |           |
                                ;--             |other stuff|
                                ;--             |           |
                                ;--             -------------
)                               ;--

(constant MAXNUMWINDOWS 50)
