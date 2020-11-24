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


(defun ml-displace (f newf)
  (rplaca f (car newf))
  (rplacd f (cdr newf))
)

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

; F-dml.lisp      Original code: dml (lisp 1.6) part of Edinburgh LCF
;                 by M. Gordon, R. Milner and C. Wadsworth   (1978)
;                 Transported by G. Huet in Maclisp on Multics, Fall 1981
;
; V2.2 :exit instead of err
; V3.1: exit renamed in breakout
; V4.3: Added fast arithmetic (smallnums)  GC


  ;  Part 1: Representation of tokens
  ;    In general an ml token value tok is represented by
  ;  the lisp atom tok, except
  ;      (a) the empty token, returned by implode[], is special
  ;      (b) the token nil is non-interned (to avoid a stanford
  ;          lisp problem that reentering a core image destroys
  ;          additional properties we might have given to nil).
  ;    In effect, the functions here determine token as an abstract
  ;  type with explode, implode, tok_of_int, and int_of_tok as primitive
  ;  operations.

;  Sets Manifests:  tokempty


(defparameter tokempty '#:|^|)            ; so prints as ^        NEW
                                  ; noninterned, so is # `^`

(defun tokof (x) (cond
  ((numberp x) (implode (explode x)))  ;NEW was (readlist (slashify (explode x
  ((characterp x) (intern (string x) (find-package 'nuprl)))
  ((atom x) x)
  (t (syserror (cons x '(bad arg tokof))))
))

(defun intof (x) 
  (declare (special tokempty))
  (cond
    ((eql x tokempty) (breakout evaluation 'intof))
    ((forall 'digitp (setq x (ml-explode x)))
     (readlist x)
     )
    (t (breakout evaluation 'intof))))

(defun ml-explode (tok) 
  (declare (special tokempty)) 
  (cond
    ((eql tok tokempty) nil)
    (t (mapcar 'tokof (explodec tok)))
    ))	;ml-explode

(defun ml-implode (l) (declare (special tokempty)) (cond
  ((null l) tokempty)
  ((forall #'(lambda (x) (eql (toklength x) 1)) l)
              (implode l))  ; NEW was (readlist (slashify l))
  (t (breakout evaluation 'implode))
))  ;ml-implode

(defun toklength (tok)
       (declare (special tokempty))
       (if (eql tok tokempty) 0 (length (explodec tok))))  ;toklength



  ;  PART 2: functions to set up lisp definitions in ml


; define an ML function in terms of a Lisp function of n arguments
(defun declare-ml-fun (ml-fn n lisp-fn mty)
  (let ((closure-name (gen-runtime-name ml-fn)))
    (setf (symbol-value closure-name)
	  (make-closure (symbol-function lisp-fn) n))
    (setf
      (get ml-fn 'mldescriptor)
      (make-prim-function :id ml-fn
			  :name closure-name
			  :fname lisp-fn
			  :arity n))
    (setf (get ml-fn 'mltype) (makety mty))
    ml-fn))                     ; declare-ml-fun


; define an ML constant in terms of a Lisp constant
(defun declare-ml-const (id exp mty)
  (let ((value-name (gen-runtime-name id)))
    (setf (symbol-value value-name) (eval exp))
    (setf (get id 'mldescriptor) (make-value :id id :name value-name))
    (setf (get id 'mltype) (makety mty))
    id))                        ; declare-ml-const


;  PART 3: defining ml primitives

;  Uses manifests:  tokempty  [Part 1]
;                   initenv  [tml]

;  SETS manifests:  infixables, mlreserved

;  Sets global:  tracelist

;  Special:  %e



(dml |*| 2 * (int -> (int -> int)))
(defmlsubst (|/|  #|||# ml-div) (x y) (int -> (int -> int))
  (cond ((zerop y) (breakout evaluation 'div)) (t (truncate x y))))
(dml |+| 2 + (int -> (int -> int)))
(defmlsubst (|-| ml-difference) (a b)
	  (int -> (int -> int))
  (- a b))
(defmlsubst (|<| ml-less) (a b) (int -> (int -> bool))
  (< a b))
(defmlsubst (|>| ml-greater) (a b) (int -> (int -> bool))
  (> a b))
(dml |%-| 1 - (int -> int))

;-- ML-EQUAL.  If type term, use prl-equal-terms  to check if equal.


(defmlfun (= ml-equal) (x y) (%A -> (%A -> bool))
  (cond
    ((eql x y))					;-- hack for efficient positive check
    ((atom x) nil)				;-- previous should have got it.
    ((atom y) nil)
    ((is-term-type x) (equal-terms (prl-term x) (prl-term y)))	;-- meta type term
    (t (and (ml-equal (car x) (car y))
	    (ml-equal (cdr x) (cdr y))))))


;; And and or have to be treated specially.
(setf (get '|%&| 'mltype) (makety '((bool |#| bool) -> bool)))
(setf (get '|%or| 'mltype) (makety '((bool |#| bool) -> bool)))
;;(defmlsubst |%&| (a b) (bool -> (bool -> bool))
;;  (and a b))
;;(defmlsubst |%or| (a b) (bool -> (bool -> bool))
;;  (or a b))
(defmlsubst |@| (a b) ((%A list) -> ((%A list) -> (%A list)))
  (append a b))
(defmlsubst |.| (a b) (%A -> ((%A list) -> (%A list)))
  (cons a b))

(dml |not| 1 not (bool -> bool))
(dml |null| 1 null ((%A list) -> bool))
(dml |fst| 1 car ((%A |#| %B) -> %A))
(dml |snd| 1 cdr ((%A |#| %B) -> %B))

(defmlsubst (|do| ml-do) (x) (%A -> |.|)
  x						;unused
  nil)						;ml-do

(defmlfun (|hd| ml-hd) (x) ((%A list) -> %A) 
  (if x (car x) (breakout evaluation 'hd)))

(defmlfun (|tl| ml-tl) (x) ((%A list) -> (%A list))
    (if x (cdr x) (breakout evaluation 'tl)))

(defmlsubst (|isl| ml-isl) (x) ((%A |+| %B) -> bool)
  (car x))

(defmlfun (|outl| ml-outl) (x) ((%A |+| %B) -> %A)
  (cond ((car x)(cdr x)) ((breakout evaluation 'outl))))

(defmlfun (|outr| ml-outr) (x) ((%A |+| %B) -> %B)
  (cond ((car x)(breakout evaluation 'outr)) ((cdr x))))

(defmlsubst (|inl| ml-inl) (x) (%A -> (%A |+| %B))
  (cons t x))

(defmlsubst (|inr| ml-inr) (x) (%B -> (%A |+| %B))
  (cons nil x))

(dml |explode| 1 ml-explode (token -> (token list)))
(dml |implode| 1 ml-implode ((token list) -> token))

(dml |tok_of_int| 1 tokof (int -> token))
(dml |int_of_tok| 1 intof (token -> int))


(defparameter tracelist nil)

(defun checktraceable (F)
  (cond
    ((atom  F)
     (llprinc '|closure not traceable: |)
     (llprinc  F) (llterpri)
     (breakout  evaluation 'TRACE))
    (t F)))

(defmlfun (|TRACE| ml-TRACE) (phi)
	  (((%A -> %B) -> ((%A -> %B) |#| %C)) -> ((%A -> %B) -> %C))
 (declare (special tracelist initenv))
 (cons
  #'(lambda (%e)
      (let ((F (checktraceable (car %e)))
	    (Fcopy (cons nil nil))
	    (phi (cadr %e)))
	(ml-displace Fcopy F)
	(let ((x (ap phi Fcopy)))
	  (ml-displace F (car x))
	  (push (cons F Fcopy) tracelist)
	  (cdr x))))
  (cons phi initenv)
 ))  ;ml-TRACE


(defmlfun (|UNTRACE| ml-UNTRACE)  (F) ((%A -> %B) -> bool)
  (declare (special tracelist))
  (let ((x (assoc F tracelist)))
       (if (null x) nil
          (progn (setq tracelist (outq x tracelist))
         (ml-displace F (cdr x))
         t))))  ;ml-UNTRACE


(defparameter infixables  '(gcd |#| |*| |+| |-| |<| |=| |>| |?| |@| |^|))
(defparameter mlreserved (append '(|=| |?|) rsvdwds))


(defun trymlinfix (fun tok sort)
  (declare (special mlreserved infixables))
  (cond ((or (member tok mlreserved)
	     (not (or (idenp tok) (member tok infixables))))
         (ptoken |can't infix |)
         (ml-print_tok tok)(pnewline)
         (breakout evaluation fun)))
  (mlinfix2 tok sort))				;trymlinfix


(defmlfun (|ml_paired_infix| ml-ml_paired_infix)  (tok)  (token -> |.|)
  (trymlinfix 'ml_paired_infix tok 'paired))

(defmlfun (|ml_curried_infix| ml-ml_curried_infix)  (tok) (token -> |.|)
  (trymlinfix 'ml_curried_infix  tok 'curried))
