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

; F-mlprin.lisp   Original code: mlprin (lisp 1.6) part of Edinburgh LCF
;                 by M. Gordon, R. Milner and C. Wadsworth   (1978)
;                 Transported by G. Huet in Maclisp on Multics, Fall 1981

(declaim (special %pp %ppl %ppdepth %ex printtable
                pp-sym trap-then-sym trap-loop-sym
                trapif-then-sym trapif-loop-sym
                trapbind-then-sym trapbind-loop-sym))

(setq printtable
 '(nil
  (mk-nulltyp |.|)
  (mk-inttyp |int|)
  (mk-booltyp |bool|)
  (mk-toktyp |tok|)
  (mk-termtyp |term|)        ;-- changed for PRL
;--   (mk-formtyp |formula|)       
  (mk-prooftyp |proof|)
  (mk-declarationtyp |declaration|)
  (mk-ruletyp |rule|)
;--   (mk-typetyp type)
;--   (mk-thmtyp thm)
  (mk-vartyp 1)
  (mk-consttyp
   (cond ((null (cddr %ex)) (llprinc (cadr %ex)))
         ((null (cdddr %ex)) (funcall %pp (caddr %ex)) (llprinc (cadr %ex)))
         (t (funcall %ppl (cddr %ex) '|(| '|,| '|)|)
            (llprinc (cadr %ex)))))
  (mk-listtyp 1 |list|)
  (mk-prodtyp |(| 1 |#| 2 |)|)
  (mk-sumtyp |(| 1 |+| 2 |)|)
  (mk-null-funtyp |( ->| 1 |)|)
  (mk-funtyp |(| 1 -> 2 |)|)
  (mk-boolconst
    (llprinc (cond ((cadr %ex) '|true|)(t '|false|))))
      

  (mk-intconst 1)
  (mk-tokconst |`| 1 |`|)
  (mk-tyquot |"| |:| (llprinc pp-sym) |"|)
  (mk-quot |"| (llprinc pp-sym) |"|)
  (mk-var 1)
  (mk-fail fail)
  (mk-failwith failwith | | 1)
  (mk-empty |()|)
  (mk-dupl |(| 1 |,| 2 |)|)
  (mk-list (funcall %ppl (cdr %ex) '|[| '|;| '|]|))
  (mk-straint |(| 1 |:| 2 |)|)
  (mk-appn |(| 1 | | 2 |)|)
  (mk-binop |(|
            2
            (llprinc
             (cond ((eql (cadr %ex) '%&) '&)
                 ((eql (cadr %ex) '|%or|) '(|"| or |"|))   ;??
                 (t (cadr %ex))))
            3
            |)|)
  (mk-unop (cond ((eql (cadr %ex) '|%-|) (llprinc '|-|))
               (t (llprinc (cadr %ex)) (llprinc '| |)))
           2)
  (mk-do do 1)
  (mk-seq
   (funcall %ppl (append (cadr %ex) (cddr %ex)) '| | '|;| '| |)
  )
  (mk-assign 1 |:=| 2)
  (mk-test (testtrapfn t (cdr %ex)))
  (mk-trap 1 (testtrapfn nil (cddr %ex)))
  (mk-null-abstr |(\\ . | 1)       ;-- new for prl
  (mk-abstr |(\\|  1 |.| 2 |)|)
  (mk-in 1 | in | 2)
  (mk-ind 1 | in | 2)
  (mk-ina 1 | in | 2)
  (mk-let let | | 1 | = | 2)
  (mk-letrec |letrec| | | 1 | = | 2)
  (mk-letref |letref| | | 1 | = | 2)
  (mk-deftype |lettype| | | (llprinc pp-sym))
  (mk-abstype |abstype| | | (llprinc pp-sym))
  (mk-absrectype |absrectype| | | (llprinc pp-sym))
  (mk-begin |begin| | | 1)
  (mk-end |end| | | 1)))



(defun ppmltext (%ex %ppdepth)
    (cond       ((atom %ex) (llprinc %ex))
        (t (ml-pprint %ex (lookup (car %ex)) %ppdepth))))  ;ppmltext

(defun ml-pprint (%ex f %ppdepth)
  (prog (x)
        (cond ((zerop %ppdepth) (return (llprinc pp-sym))))
   loop (cond ((null f) (return nil)))
        (setq x (car f))
        (cond ((numberp x) (ppmltext (getnth x (cdr %ex)) (1- %ppdepth)))
              ((atom x) (llprinc x))
              (t
               ((lambda (%pp %ppl) (eval x))
                #'(lambda (ex) (ppmltext ex %ppdepth))
		#'(lambda (l open sep close)
		    (ppmltextl l %ppdepth open sep close)))))
        (setq f (cdr f))
        (go loop)))  ;pprint

(defun ppmltextl (l %ppdepth open sep close)
  (prog (xl)
        (setq xl l)
        (llprinc open)
        (cond ((null xl) (go end)))
   loop (ppmltext (car xl) %ppdepth)
        (setq xl (cdr xl))
        (cond ((null xl) (go end)) (t (llprinc sep) (go loop)))
   end  (llprinc close)))  ;ppmltextl

(defun lookup (mkx)
  (prog (pt)
        (setq pt printtable)
   loop (cond ((null pt) (return '(|"| (llprinc pp-sym) |"|)))
              ((eql mkx (caar pt)) (return (cdar pt)))
              (t (setq pt (cdr pt)) (go loop)))))  ;lookup

(defun getnth  (n l)
  (cond ((or (zerop n) (null l)) (syserror '(bad arg getnth)))
        ((eql n 1) (car l))
        (t (getnth (1- n) (cdr l)))))  ;getnth

(defun testtrapfn (istest f)
  (prog (xl x)
        (setq xl (car f))
   l1   (cond ((null xl) (cond ((null (cdr f)) (return nil))
                           (t (setq x (cadr f)) (go l2)))))
          (setq x (car xl))
        (llprinc
         (cond (istest '"if ")
               (t (cond ((eql (car x) 'once) trapif-then-sym)
                      (t trapif-loop-sym)))))
        (ppmltext (cadr x) %ppdepth)
        (cond (istest
               (llprinc (cond ((eql (car x) 'once) '" then ")
                        (t '" loop "))))
              (t (llprinc '| |)))
        (ppmltext (cddr x) %ppdepth)
        (setq xl (cdr xl))
        (go l1)
   l2   (cond (istest
               (llprinc (cond ((eql (car x) 'once) '" else ")
                        (t '" loop "))))
              (t (cond ((atom (car x))
                      (llprinc (cond ((eql (car x) 'once) trap-then-sym)
                                 (t trap-loop-sym))))
                     (t (llprinc (cond ((eql (caar x) 'once) trapbind-then-sym)
                                 (t trapbind-loop-sym)))
                        (llprinc (cdar x))
                        (llprinc '| |)))))
   (ppmltext (cdr x) %ppdepth)))  ;testtrapfn

