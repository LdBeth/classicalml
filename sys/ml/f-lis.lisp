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

; F-lis.lisp      Original code: lis (lisp 1.6) part of Edinburgh LCF
;                 by M. Gordon, R. Milner and C. Wadsworth   (1978)
;                 Transported by G. Huet in Maclisp on Multics, Fall 1981
;
; V2.2: breakout & tag instead of err & errset
; V3.2: cleaning-up of functions


(dml |length| 1 length ((%a list) -> int) )

(dml |rev| 1 reverse ((%a list) -> (%a list)))

(defmlfun |mem| (a l) (%a -> ((%a list) -> bool)) (member a l))

(defmlfun (|flat| ml-flat) (ll)
	  (((%a list) list)->(%a list))
  (apply #'append ll))

(defmlfun (|map| ml-map) (f l)
	  ((%a -> %b) -> ((%a list) -> (%b list)))
  (mapcar #'(lambda (x) (ap f x)) l))

(defmlfun (|exists| ml-exists) (p l)
	  ((%a -> bool) -> ((%a list) -> bool))
  (block found
    (dolist (item l)
      (if (ap p item) (return-from found t)))
    nil))

(defmlfun (|forall| ml-forall) (p l)
	  ((%a -> bool) -> ((%a list) -> bool))
  (block found
    (dolist (item l)
      (ifn (ap p item) (return-from found nil)))
    t))

(defmlfun (|rev_itlist| ml-rev_itlist)  (f l x) 
	  ((%a -> (%b -> %b)) -> ((%a list) -> (%b -> %b)))
  (dolist (item l)
    (setq x (ap f x item)))
  x)

(defmlfun (|find| ml-find)  (p l)
	  ((%a -> bool) -> ((%a list) -> %a))
 (block found
   (dolist (item l)
     (if (ap p item) (return-from found item)))
   (breakout evaluation 'find)))

(defmlfun (|tryfind| ml-tryfind)  (f l)
	  ((%a -> %b) -> ((%a list) -> %b))
  (block found
    (dolist (item l)
      (tag evaluation (return-from found (ap f item))))
    (breakout evaluation 'tryfind)))

(defmlfun (|filter| ml-filter)  (p l)
	  ((%a -> bool) -> ((%a list) -> (%a list)))
  (let ((r nil))
    (dolist (item l)
      (if (ap p item) (push item r)))
    (nreverse r)))

(defun succeeds (f x)
  (block OK
    (tag evaluation (ap f x) (return-from OK t))
    nil))

(defmlfun (|mapfilter| ml-mapfilter)  (f l)
	  ((%a -> %b) -> ((%a list) -> (%b list)))
  (let ((r nil))
    (dolist (item l)
      (tag evaluation (push (ap f item) r)))
    (nreverse r)))
