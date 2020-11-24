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

; F-obj.lisp
; Introduced by GH in V4.1
; LISP objects

; constructors
(dml |objoftok| 1 identity (token -> obj))
(dml |objofint| 1 identity (int -> obj))
(defmlfun |cons| (a b) (obj -> (obj -> obj))
  (cons a b))

; destructors
(defmlfun (|tokofobj| ml-tokofobj) (x) (obj -> token)
       (if (symbolp x) x (breakout evaluation 'tokofobj)))
(defmlfun (|intofobj| ml-intofobj) (x) (obj -> int)
       (if (numberp x) x (breakout evaluation 'intofobj)))
(defmlfun (|left| ml-left) (x) (obj -> obj)
       (if (consp x) (car x) (breakout evaluation 'left)))
(defmlfun (|right| ml-right) (x) (obj -> obj)
       (if (consp x) (cdr x) (breakout evaluation 'right)))

;updators
(defmlfun (|setleft| ml-setleft) (x y) (obj -> (obj -> obj))
       (if (consp x) (rplaca x y)))
(defmlfun (|setright| ml-setright) (x y) (obj -> (obj -> obj))
       (if (consp x) (rplacd x y)))

;equality
(dml |eq| 2 eq (obj -> (obj -> bool)))

;lisp eval, for communication between lisp and ml
;use with caution!
(dml |lisp_eval| 1 eval (obj -> obj))
