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

; F-gp.lisp     Original code: gp (lisp 1.6) part of Edinburgh LCF
;               by M. Gordon, R. Milner and C.Wadsworth   (1978)
;               Transported by G. Huet in Maclisp on Multics, Fall 1981
; V2.2 :breakout instead of err in function can
; V3.1 Unix -- added "uniquesym"
;      Changed "can" to avoid non-local "return" from "tag" (caused looping)

(declaim (special %%%fn %%%args initial%load %symcount %timestamp word-sep))


; Manifest constants
(setq word-sep '|%|)            ; word separator for uniquesym


(defun triple (x y z)  (cons x (cons y z)))  ;triple

; A family of "assoc" functions that match the cdr instead of the car
(defun revassoc (x l)
  (prog nil
        (cond ((null l) (return nil)))
   a    (cond ((equal x (cdar l)) (return (car l)))
              ((setq l (cdr l)) (go a)))))   ;revsasoc

(defun revassq (x l)
  (prog nil
        (cond ((null l) (return nil)))
   a    (cond ((eql x (cdar l)) (return (car l)))
              ((setq l (cdr l)) (go a)))))   ;revassq


; "assoc" functions that return only the opposite element of the pair found

(defun revassoc1 (x l) (car (revassoc x l)))  ; revassoc1

(defun revassq1 (x l) (car (revassq x l)))  ;revassq1

(defun assq1 (x l) (cdr (assoc x l)))  ; assq1

(defun assoc1 (x l) (cdr (assoc x l)))  ;assoc1

(defun itlist (fn xl x)
  (prog nil
        (setq xl (reverse xl))
   l    (cond ((null xl) (return x))
              (t (setq x (funcall fn (car xl) x))
                 (setq xl (cdr xl))
                 (go l)))))  ;itlist

(defun addprop (i v p)
       (car (setf (get i p) (cons v (get i p)))))  ;addprop

(defun charseq(ch n)
  (prog (l)
   loop (cond ((eql n 0) (return l)))
        (setq l (cons ch l))
        (setq n (1- n))
        (go loop)))  ;charseq

(defun can (%%%fn %%%args)   ;t iff fn[args] does not fail
       (tag canit
            (tag evaluation (apply %%%fn %%%args) (breakout canit t))
            nil))  ;can


(defun inq (x l) (cond ((member x l) l) ((cons x l))))  ;inq

(defun outq (x l) (cond (l (cond
    ((eql x (car l)) (outq x (cdr l)))
    ((cons (car l) (outq x (cdr l))))
))))  ;outq

(defun qeval (x) (list 'quote x))  ;qeval
