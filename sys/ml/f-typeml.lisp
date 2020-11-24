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


;**************************************************************************
;*                                                                        *
;*      Projet     Formel                       LCF    Project            *
;*                                                                        *
;**************************************************************************
;*                                                                        *
;*            Inria                         University of Cambridge       *
;*      Domaine de Voluceau                   Computer Laboratory         *
;*      78150  Rocquencourt                    Cambridge CB2 3QG          *
;*            France                                England               *
;*                                                                        *
;**************************************************************************

; F-typeml.lisp   Original code: typeml (lisp 1.6) part of Edinburgh LCF
;                 by M. Gordon, R. Milner and C. Wadsworth   (1978)
;                 Transported by G. Huet in Maclisp on Multics, Fall 1981
;
; V2.2 :breakout instead of err
; V4.3 : (\x.e)e' typechecks like let x=e' in e    GH
; NOTE:  typechecker is inefficient because it repeatedly constructs
;        constant arguments (mostly for "listtyping")

; the specials that occur in lambda-bodies were necessary when "exists"
; was an expr instead of a macro -- these specials probably should be
; removed.


(declaim (special %mlprindepth %recs %nonrecs %vartypes env tenv asscheck prop
          structcheck glassl %l %env %tyv %ty %recs1 %star %id nonloc
          initial%load type%errors
          ; Globals
          nullty boolty intty tokty objty termty formty %thisdec
          proofty declarationty rulety                   ;-- changed for prl
          %thistydec %deftypes null-sym prod-sym sum-sym
          arrow-sym %emt %temt %sections lastvalname))

; make a circular list (x x x x ...)
(defun twistlist (x) (let ((lx (list x))) (rplacd lx lx)))  ;twistlist

(defun structon (x) (prog2 (setq structcheck t) x))  ;structon

(defun structoff (x) (prog2 (setq structcheck nil) x))  ;structoff


; Generate a type variable
(defun genmlink () (ncons '%MLINK))  ;genmlink

; Check the types of several objects, recording all type errors
; (listtyping (ob1 ... obn) (ty1 .. tyn) ty)
;     unifies the type of each obi with type tyi, finally returns ty
; if type errors occur, return a new type variable to prevent error cascade
(defun listtyping (obl tyl ty)
 (let ((OK t))
  (while obl
    (let ((ty$ (typing (car obl))))
     (cond
      ((and (car tyl) (not (unifyt ty$ (car tyl))))
       (incf type%errors)    (setq OK nil)
       (llterpri)  (llprinc '|ill-typed phrase: |)
       (ppmltext (car obl) %mlprindepth)   (llterpri)
       (let ((%temt tenv))
        (ptoken |has an instance of type|)   (pbreak 2 4)
        (printmty (tidy ty$))   (pnewline)
        (ptoken |which should match type|)   (pbreak 2 4)
        (printmty(tidy (car tyl)))  (pnewline)))))
      (setq obl (cdr obl)) (setq tyl (cdr tyl)))
    (if OK ty (genmlink))))  ; listtyping

; deduce types of ML syntax tree
; also deduces ML types inside quotations, for typing of antiquotations
(defun typing (ob)
 (let ((c (car ob)) (l (cdr ob))  (ty (genmlink)) (ty$ (genmlink)))
   (case  c
    (mk-empty     (cond (structcheck ty)(nullty)))
    (mk-boolconst boolty)
    (mk-intconst  intty)
    (mk-tokconst  tokty)
    (mk-termconst termty)
    (mk-formconst formty)
;--     (MK=VARTYPE  typety)  removed for PRL
;--     ((MK=VAR MK=CONST)   termty)

    (mk-fail  ty)
    (mk-failwith (listtyping l (list tokty) ty))
    (mk-var    (gettype (car l)) )
    (mk-consttyp (cond
      ((checkabst l)
       (cons (gettypet(car l)) (mapcar #'typing (cdr l)))
      )
      ( (gettypet (car l)))
    ))
    (mk-vartyp
     (cond
      ((assoc1 (car l) %vartypes))
      (t (push (cons (car l) ty) %vartypes) ty)
    ))
    ((mk-inttyp mk-booltyp  mk-typetyp 
                                                       ;-- mk-thmtyp mk-objtyp
      mk-termtyp mk-formtyp mk-prooftyp mk-declarationtyp  ;-- PRL.
      mk-ruletyp
      mk-toktyp mk-nulltyp mk-listyp  mk-prodtyp mk-funtyp mk-null-funtyp mk-sumtyp
     )
     (cons c (mapcar #'typing l))
    )
    (mk-straint
     (let ((ty (typing (cadr l))))
       (listtyping (list(car l)) (list ty) ty)))
    (mk-dupl
     (list 'mk-prodtyp (typing(car l)) (typing(cadr l)) )
    )
    (mk-seq (listtyping (car l) (twistlist nil) (typing (cadr l))))
    (mk-list (listtyping l (twistlist ty) (list 'mk-listyp ty)))
    (mk-appn
        (ifn (eql (caar l) 'mk-abstr)
             (listtyping l (list (list 'mk-funtyp ty ty$) ty) ty$)
             (typing `(mk-let ,(cadar l) ,(cadr l)))
             (popenv (typing (caddar l)))))
        ;types (\x.e1)e2 like let x=e2 in e1  [GH]
        ;maybe %pt should be changed accordingly, so that the translator may
        ;take advantage of the transformation too.
    (mk-binop
     (cond
      (structcheck (setq ty$ (list 'mk-listyp ty))
       (listtyping (cdr l) (list ty ty$) ty$)
      )
      ((case (car l)
	 ((|%&| |%or|)
	  (typing
	    `(mk-appn (mk-var ,(car l)) (mk-dupl ,(cadr l) ,(caddr l)))))
	 (otherwise
	  (typing
	    `(mk-appn (mk-appn (mk-var ,(car l)) ,(cadr l)) ,(caddr l))))))))
    (mk-unop
     (typing (list 'mk-appn  (list 'mk-var (car l)) (cadr l)))
    )
    (mk-assign (prog(ty)
      (structon(setq asscheck t))
      (setq ty (typing(car l)))
      (structoff(setq asscheck nil))
      (return (listtyping(cdr l)(list ty)ty))
    ))
    ((mk-test mk-trap)
     (cond ((eql c 'mk-trap)
       (setq l
        (cons (cons (triple 'once '(mk-list)(car l))(cadr l))(cddr l))
       )
     ))
     (listtyping
      (mapcar #'cadr (car l))
      (twistlist (if (eql c 'mk-test) boolty (list 'mk-listyp tokty)))
      nil
     )
     (let ((b nil) (e nil))
       (cond ((cdr l) (setq e (cdadr l))
                  (cond ((atom (setq b (caadr l))))
                        ((setq e
                `(mk-in (mk-let (mk-var ,(cdr b)) (mk-tokconst)) ,e))
                         (setq b (car b))))
                  (setq ty$ (typing e))
                  (if (eql b 'once) (setq ty ty$)))
           ((if (eql c 'mk-test) (setq ty nullty)))
        ))
     (let ((%ty ty))
       (listtyping
        (mapcar #'cddr (car l))
        (mapcar #'(lambda(x)(cond((eq(car x)'once)%ty)))(car l))
        %ty)))
    (mk-null-abstr
       (popenv (list 'mk-null-funtyp (typing (car l))))
    )
    (mk-abstr
     (varbindings (car l) c)
     (popenv (list 'mk-funtyp
               (structoff(typing(structon(car l)))) (typing(cadr l))))
    )
    (mk-in   (typing(car l))  (popenv(typing(cadr l))))
    (mk-ind  (typing(car l))  (poptenv(typing(cadr l))))
    (mk-ina  (typing(car l))
     (absscopechk(popenv(poptenv(typing(cadr l)))))
    )

    ((mk-let mk-letref)
     (let ((ty (typing (cadr l))))
       (prog2
        (varbindings(car l) c)
        (structoff(listtyping (structon(list(car l))) (list ty) ty))
        (if (eql c 'mk-let)(rplaca (car env) 'let))
      )))
    (mk-letrec
      (varbindings(car l) c)
      (rectyping l))

    ((mk-abstype mk-absrectype)
       (prog (tyops isoms eqnl eqn)
           (setq eqnl (car l))
           (setq tyops
             (mapcar #'(lambda(x)
                       (let ((y (gen-external-name (car x))))
                           (eval-remember   `(progn
                       (setf (get (quote ,y) 'arity) (quote ,(length (cadr x))))
                     (setf (get (quote ,y) 'absname) (quote ,(car x)))))
                           (cons (car x) y)))
                 eqnl))
           (and (eql c 'mk-absrectype)(typebindings tyops))
         a (cond (eqnl
                 (setq eqn (car eqnl)) (setq eqnl (cdr eqnl))
                 (prog (%vartypes ty1 ty2)
                       (setq %vartypes
                           (mapcar #'(lambda (v) (cons v (genmlink)))
                             (cadr eqn)))
                       (setq ty2 (typing (cddr eqn)))
                       (cond ((eql (length (cadr eqn))(length %vartypes)))
                           ((llprinc '|free vartype in abstype equation|)
                            (llterpri)(breakout typecheck nil)))
                       (setq ty1 (cons (assoc1 (car eqn) tyops)
                                   (mapcar #'cdr %vartypes)))

                                       (push (list (concat '|rep_| (car eqn))
                                     'mk-funtyp ty1 ty2) isoms)

                                       (push (list (concat '|abs_| (car eqn))
                                     'mk-funtyp ty2 ty1) isoms)
                       (return nil))
                 (go a)))
         (and (eql c 'mk-abstype) (typebindings tyops))
         (push (cons 'abs isoms) env)
         (setq ty (typing (cadr l)))
         (popenv (rplacd (cadr env)(cdar env))))
       ty)

    (mk-deftype
         (typebindings (mapcar #'newdeftype (car l)))
         nullty)

    ((mk-tyquot mk-quot MK=ANTIQUOT MK=TYPE=ANTIQUOT)    (typing (car l)))
;--     (MK=TYPE (listtyping (cdr l) (twistlist typety) typety))
;--     (MK=TYPED   (listtyping l (list termty typety) termty) )
    ((MK=COMB MK=PAIR MK=ABS MK=COND)
     (listtyping l (list termty termty termty ) termty)
    )
    (MK=NEG (listtyping l (list formty) formty))
    ((MK=CONJ MK=DISJ MK=IMP MK=IFF)
     (listtyping l (list formty formty) formty)
    )
    ((MK=FORALL MK=EXISTS) (listtyping l (list termty formty) formty) )
    (MK=PREDICATE  (listtyping (cdr l) (list termty) formty))
    ((MK=EQUIV MK=INEQUIV)
     (listtyping l (list termty termty) formty)
    )

    (otherwise (parserr c))
  )))  ;typing


(defun parserr (c)
  (syserror (concat '|bad parser constructor | c))
)  ;parserr

(defun initmltypenv ()
  (setq nullty '(mk-nulltyp))
  (setq boolty '(mk-booltyp))
  (setq intty '(mk-inttyp))
  (setq tokty '(mk-toktyp))
  (setq objty '(mk-objtyp))   ;obj
;--   (setq typety '(mk-typetyp))
  (setq termty '(mk-termtyp))     ;-- changed for PRL
  (setq formty '(mk-formtyp))
  (setq proofty '(mk-prooftyp))
  (setq declarationty '(mk-declarationtyp))
  (setq rulety '(mk-ruletyp))
;--   (setq thmty '(mk-thmtyp))

  (setq %emt
   (setq %temt
    (setq %deftypes
       nil
  ))))  ;inittmltypenv
     ; Unix -- deleted extra paren here

(cond (initial%load (initmltypenv)))


; Top-level type checker
(defun typecheck (ob)
  (let ((ph (car ob))  (env %emt)  (tenv %temt)  (type%errors 0)
        asscheck structcheck glassl %vartypes)
    (let ((ty (tidy (typing ob))))
         (cond ((not (zerop type%errors))
              (llprinc type%errors) (llprinc '| error|)
              (if (> type%errors 1)(llprinc 's))
              (llprinc '| in typing|) (llterpri)
              (breakout typecheck nil)))
         (absscopechk ty)
         (cond
         ((and (eql ph 'mk-letref) (poly ty))
          (llprinc '|top-level letref has polytype |)
          (printmty ty) (pnewline)
          (breakout typecheck nil)))
         (mapc #'(lambda (x)
                 (cond ((poly (cdr x))
                     (llprinc '|non-local assignment to polytyped variable |)
                     (llprinc (car x)) (llterpri)
                     (breakout typecheck nil))))
             glassl)
         (ifn (eql tenv %temt) (setq %thistydec (car tenv)))
         (ifn (eql env %emt)  (tidycdrs (cdr (setq %thisdec (car env)))))
         ty)))  ; typecheck

(defun tidycdrs (l)
   (mapc #'(lambda(x)(rplacd x (tidy(cdr x)))) l))  ;tidycdrs

(defun putpropl (l prop)
 (mapcar #'(lambda (x) (setf(get (car x) prop)(cdr x))) l)
 )  ;putpropl

(defun updatetypes ()
 (prog()
  (cond (%sections
    (and %thisdec (push %thisdec %emt))
    (and %thistydec (push %thistydec %temt))
    (return nil)
  ))
  (setq %deftypes (append %thistydec %deftypes))
  (cond (%thisdec
    (putpropl (cdr %thisdec) 'mltype)
    (mapc #'(lambda (x)
            (cond
             ((eql 'mk-letref(car %thisdec))(setf(get (car x) 'refvar) t))
             ((remprop(car x)'refvar))))
           (cdr %thisdec)
    )
  ))
 ))  ;updatetypes


; Push a new layer of bindings onto the environment
; "binder" tells how binders were created;   mk-let, mk-letrec, etc.
(defun varbindings (st binder)
 (push (cons binder (layer st)) env))  ;varbindings

(defun layer(st)
 (case (car st)
        (mk-var (list (cons (cadr st) (genmlink))))
        (mk-straint  (layer (cadr st)))
        ((mk-dupl mk-list) (layerl (cdr st)))
        (mk-binop (layerl (cddr st)))
        (otherwise nil)))  ;layer

(defun layerl (stl)
 (cond (stl (append (layer (car stl)) (layerl (cdr stl))))))  ;layerl

; get the type of the identifier
; if unbound, print message and assume identifier is bound by "letref"
(defun gettype (%id)
 (cond
  ((prog(nonloc) (return(gettypeid env) )  ))
  (t (incf type%errors)
     (llterpri)
     (llprinc '|unbound or non-assignable variable | ) (llprinc %id) (llterpri)
     (varbindings (list 'mk-var %id) 'mk-letref)
     (genmlink)
 )))  ; gettype

; Look up "it", "nil", or a dmlc'd constant
(defun get-builtin ()
   (cond ((equal %id '|nil|) '(mk-listyp *))    ;new code for nil
       (t (if (and (eql %id lastvalname)
                   (or (assoc 'mk-abstr env) (assoc 'mk-null-abstr env))
		 )                                ;-- new for PRL
              (progn (llprinc '|May not use "|)
                     (llprinc lastvalname)
                     (llprinc '|" in a function body|)
                     (llterpri)
                     (breakout typecheck nil)))
          (get %id 'mltype))))  ; get-builtin


; Get type type of %id in environment e
;   asscheck is true if this is the left-hand of an assignment
;   nonloc is true if e was found underneath a mk-abstr binding
(defun gettypeid(e)
 (cond
  ((null e)
    (let ((ty (get-builtin)))
     (cond
      ((get %id 'refvar)ty)
      (asscheck nil)
      (ty (mutant ty nil))
    )))
  (t (let ((ty (assoc1 %id (cdar e))))
        (cond ((null ty)
               (cond
		 ((or (eq(caar e)'mk-abstr)
		      (eql (caar e) 'mk-null-abstr))
		  (setq nonloc t)))
               (gettypeid (cdr e))
              )
              ((eql (caar e) 'mk-letref)
               (cond((and asscheck nonloc)(push (cons %id ty) glassl)))
               ty
              )
              (asscheck nil)    ; assignable variable needed?
              ((member(caar e) '(let abs)) (mutant ty (cdr e)))
              (t ty)
       )))))


; Rename type variables for different uses of a let-bound identifier
;    (also abstract type isomorphisms)
(defun mutant (ty %env)
 (cond ((poly ty)(let ((%l nil)) (mutant1 ty)))
       (ty)))  ;mutant

(defun mutant1 (ty)
 (cond
  ((instof ty) (mutant1 (instof ty)) )
  ((or (atom ty) (mlink ty))
      (cond ((assq1 ty %l))
            ((immut ty %env) ty)
            ((cdar (push (cons ty (genmlink)) %l)))))
  ((cons (car ty) (mapcar #'mutant1 (cdr ty))))
  ))  ;mutant1


; A type variable is immutable only if all its uses are in let-bound
;    identifiers (or abstract type isomorphisms)
(defun immut (%tyv e)
 (and e
  (or  (and (not(member(caar e) '(let abs)))
             (exists #'(lambda(x)(occurst %tyv (cdr x))) (cdar e)))
       (immut %tyv (cdr e))
       )))  ;immut


; See if a synonym exists for a given type, returns (tok . ty) or nil
; This test is used to see if the type is monomorphic.  The token returned
; may actually be out of scope.
(defun isdeftype (ty te)
 (cond ((null te) (revassoc ty %deftypes))
       ((revassoc ty (car te)))
       ((isdeftype ty (cdr te)))))     ; isdeftype

; Get the current synonym for type ty in environment te
; Returns nil if none, else (tok . ty)
; "nil" is a legal type name
(defun getdeftype (ty te)
    (let ((typair (isdeftype ty te)))
         (if (and typair (equal ty (gettypetid (car typair) te)))
             typair))) ; getdeftype

(defun rectyping (l)
 (let ((ty (structoff(typing(structon(car l))))))
      (listtyping(cdr l)(list ty) ty)
      (rplaca (car env) 'let)
      ty))  ;retyping

(defun newdeftype (ob)
 (let ((id (car ob)) (ty (typing(cdr ob))))
      (cond ((poly ty) (llprinc '|type variable in DEFTYPE|)(llterpri)
                   (breakout typecheck nil))
          ((cons id (tidy ty))))))  ; newdeftype

; See if the abstract types in ty are still accessible
(defun absscopechk(ty) (prog(%l)(atch ty)(return ty)))  ;absscopechk

(defun atch (ty)
 (cond
  ((assoc ty %l) nil)
  ((instof ty) (atch (instof ty)))
  ((mlink ty) nil)
  ((atom ty) nil)
  (t (push ty %l)
   ; built-in type operator or user-defined abstract type
   (let ((arity (get (car ty) 'arity)) (absname (get (car ty) 'absname)))
        (if (and arity (not (eq(gettypet absname)(car ty))))
            (tyscoperr absname)))
   (exists 'atch (cdr ty))
 )))  ; atch

(defun gettypet (tyid)
 (cond ((gettypetid tyid tenv)) ((tyscoperr tyid))))  ;gettypet

(defun tyscoperr (x)
  (llprinc '|type |)(llprinc x)
  (llprinc '| out of scope|)(llterpri)
  (breakout typecheck nil))  ;tyscoperr

(defun checkabst (idargs)
 (let ((ty (gettypet (car idargs))))
   (cond
    ((atom ty)
     (cond
      ((or (eql (get ty 'arity) (length (cdr idargs)))
         (llprinc '|bad args for abstype |) (llprinc (car idargs)) (llterpri)
         (breakout typecheck nil))
       t))))))  ;checkabst

; Look up the type tyid in environment te or %deftypes
(defun gettypetid (tyid te)
 (cond
  ((null te)(assq1 tyid %deftypes))
  ((assq1 tyid (car te)))
  ((gettypetid tyid (cdr te)))))  ;gettypetid

(defun typebindings (l) (push l tenv))  ;typebindings

(defun popenv (x) (pop env) x)  ;popenv

(defun poptenv (x) (pop tenv) x)  ;poptenv

; Strip out links, replace type variables with stars
(defun tidy (ty) (let ((%l nil)(%star '||)) (tidyup ty)))  ;tidy

(defun tidy1 (ty) (let ((tenv %temt)) (tidy ty))) ;tidy1   NEW used in prlet

(defun tidyup (ty)
 (cond
  ((instof ty)(tidyup (instof ty)))
  ((assq1 ty %l))
  ((or (atom ty) (mlink ty))
     (setq %star (concat '|*| %star))
     (push (cons ty %star) %l)
     %star)
  ((cons (car ty) (mapcar 'tidyup (cdr ty))))
 ))  ;tidyup


; Print (car string) if non-nil, return value of string
(defun condpstring (str)
    (if str (pstring (car str)))
    str)  ;condpstring

(defun printmty (tidyty)
  (cond ((condpstring (getdeftype tidyty %temt)))
        ((atom tidyty) (pstring tidyty))
        ((case (car tidyty)
           (mk-nulltyp (ptoken |void|))
           (mk-inttyp (ptoken |int|))
           (mk-booltyp (ptoken |bool|))
           (mk-toktyp (ptoken |tok|))
           (mk-objtyp (ptoken |obj|))  ;obj
;--        (mk-typetyp (ptoken type))
           (mk-termtyp (ptoken |term|))     ;-- Changed for PRL.
;--        (mk-formtyp (ptoken |formula|))
           (mk-prooftyp (ptoken |proof|))
           (mk-declarationtyp (ptoken |declaration|))
           (mk-ruletyp (ptoken |rule|))
;--        (mk-thmtyp (ptoken thm))
           (otherwise (let ((abs (getdeftype (car tidyty) %temt)))
                (cond
                   (abs (printabstype (cdr tidyty) (car abs)))
                   ((eql (car tidyty) 'mk-listyp)
                    (printabstype (cdr tidyty) '|list|))
                   (t (pbegin 1)
                      (ptoken |(|)
                      (printmty (cadr tidyty))
                      (printtytail (car tidyty) (caddr tidyty))
                      (ptoken |)|)
                      (pend)))))
           ))))         ; printmty

(defun printabstype (args name)
      (pbegin 0)
      (cond ((cdr args)
             (pbegin 1)
             (ptoken |(|)
             (printmty (car args))
             (mapc #'(lambda (arg) (ptoken |,|) (printmty arg)) (cdr args))
             (ptoken |)|)
             (pend)
             (pbreak 1 0))
            (args (printmty (car args))  (pbreak 1 0)))
      (pstring name)
      (pend)
      )  ; printabstype

; supress parentheses in t1 op t2 op t3 op t4, for any one op
(defun printtytail (op ty)
    (case op
       (mk-prodtyp (ptoken | #|))
       (mk-sumtyp  (ptoken | +|))
       (mk-funtyp  (ptoken | ->|))
       (otherwise (syserror '|bad type to print|)))
    (pbreak 1 0)
    (cond ((condpstring (getdeftype ty %temt)))
          ((and (consp ty) (eql op (car ty)))
           (printmty (cadr ty))
           (printtytail op (caddr ty)))
          (t (printmty ty)))
     )  ; printtytail

(defun readty () (makety (read)))  ;readty

; convert a human-readable Lisp form into an ML type
(defun makety (e)
   (cond
     ((null e) nullty)
     ((atom e)  (make-atom-ty e))
     ((member (cadr e) '(|list| LIST) )
      (list 'mk-listyp (makety (car e))))
     ((eql (car e) arrow-sym) (list 'mk-null-funtyp (makety (cadr e))))
     ((eql (cadr e) arrow-sym)
      (list 'mk-funtyp (makety (car e))(makety(caddr e))))
     ((eq(cadr e)sum-sym)
      (list 'mk-sumtyp(makety(car e))(makety(caddr e))))
     ((eq(cadr e)prod-sym)
      (list 'mk-prodtyp (makety (car e)) (makety (caddr e))))
     (t (syserror 'makety))
     ))  ;makety


; look up a type name
(defun make-atom-ty (e)
 (case e
    (|.| nullty)                ; obsolete
    ((|void| VOID) nullty)
    ((|int| INT)  intty)
    ((|bool| BOOL)  boolty)
    ((|tok| TOK |token| TOKEN)  tokty)
    ((|obj| OBJ) objty)     ;obj
;--     (type  typety)     ;-- changed for PRL
    ((|term| TERM)  termty)
;--     (formula  formty)
    ((|proof| PROOF) proofty)
    ((|declaration| DECLARATION) declarationty)
    ((|rule| RULE) rulety)
;--     (thm  thmty)
    (otherwise e)))             ; make-atom-ty


; check for a type variable
(defun mlink (ty) (and (consp ty) (eql (car ty) '%MLINK)))  ;mlink

; See if type variable has been unified with some type
(defun instof (ty) (if (mlink ty) (cdr ty)))  ;instof

(defun prune (ty) (cond  ((instof ty)(prune(instof ty))) (ty)))  ;prune

(defun occurst (v ty) (occursbt v (prune ty)))  ;occurst

(defun occursbt (%tyv bty)
 (cond
  ((mlink bty)(eql %tyv bty))
  ((exists #'(lambda(ty)(occurst %tyv ty))  (cdr bty)  ))
 ))  ;occurstb


; See if the type is polymorphic
(defun poly (ty) (polyb (prune ty)))  ;poly

(defun polyb (bty)
  (cond  ((atom bty))
         ((mlink bty))
         ((exists 'poly (cdr bty)))
         ))  ;polyb


; Return t if types can be unified.
;    side-effect --  link certain type variables to types
(defun unifyt (ty1 ty2) (unifybt (prune ty1) (prune ty2)))  ;unifyt


(defun unifybt (bty1 bty2)
 (cond
  ((eql bty1 bty2))
  ((mlink bty1) (cond  ((occursbt bty1 bty2) nil)
                        (t (rplacd bty1 bty2))))
  ((mlink bty2) (cond  ((occursbt bty2 bty1) nil)
                        (t (rplacd bty2 bty1))))
  ((eql (car bty1) (car bty2)) (unifytl (cdr bty1) (cdr bty2))
)))  ;unifybt


(defun unifytl (tyl1 tyl2)
 (cond
  ((null tyl1))
  ((unifyt (car tyl1) (car tyl2)) (unifytl (cdr tyl1) (cdr tyl2)))
))  ;unifytl


