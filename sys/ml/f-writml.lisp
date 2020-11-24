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

; F-writml.lisp   Original code: writml (lisp 1.6) part of Edinburgh LCF
;                 by M. Gordon, R. Milner and C. Wadsworth   (1978)
;                 Transported by G. Huet in Maclisp on Multics, Fall 1981
;
; Changed top level declaration printing.  8/27 MB

(declaim (special  tokempty ))

(defun prlet (descriptors)
  (dolist (desc descriptors)
    (pstring (desc-id desc))
    (ptoken | = |) (pbreak 0 0)
    (prvalty (symbol-value (desc-name desc))
	     (tidy1 (get (desc-id desc) 'mltype)))))

; Print value, type of top-level expression
(defun prvalty (x ty)
  (prinml x ty nil)
  (pbreak 1 0)
  (ptoken |: |)
  (printmty ty)
  (pnewline))  ;prvalty

; Print result of "lettype"
(defun prdefty (idtyl)
  (ptoken |type |)
  (mapc #'(lambda (idty) (pstring (car idty))(pbreak 1 0)) idtyl)
  (ptoken |defined|)(pnewline))  ;prdefty


(defmlfun (|print_int| ml-print_int) (n) (int -> |.|)
  (pstring n))


(defmlfun (|print_tok| ml-print_tok) (tok) (token -> |.|)
   (if (eql tok tokempty) (ptoken |^|)
       (progn (ptoken |`|)(pstring tok)(ptoken |`|))))


(defmlfun (|print_string| ml-print_string)  (tok) (tok -> |.|)
  (ifn (eql tok tokempty)(pstring tok)))


(defmlfun (|print_bool| ml-print_bool) (b) (bool -> |.|)
  (if b (ptoken true) (ptoken false)))


(defmlfun (|print_void| ml-print_void) (ignore) (|.| -> |.|)
  (ptoken |()| ))

#|
(defmlfun (|term_to_tok| ml-term_to_tok) (x) (term -> tok)
  (implode
    (Ttree-to-list
      (term-to-Ttree (prl-term x)))))

(defmlfun (|print_term| ml-print_term) (x) (term -> void)
  (pstring (ml-term_to_tok x)))

(defmlfun (|rule_to_tok| ml-rule_to_tok) (x) (rule -> tok)
  (implode
    (Ttree-to-list
      (get-rule-body (cdr x) (car x)))))

;;; Return tokens corresponding to the lines of the
;;; displayed Ttree.
(defun Ttree-to-toks (Ttree)
  (labels
    ((get-segments (chs)
       (let* ((first-NL-pos (position NL chs)))
	 (cond (first-NL-pos
		(cons (subseq chs 0 first-NL-pos)
		      (get-segments (nthcdr (1+ first-NL-pos) chs))))
	       (chs
		(list chs))
	       (t
		nil)))))
    (mapcar #'implode
	    (get-segments (Ttree-to-list Ttree)))))

(defmlfun (|rule_to_toks| ml-rule_to_toks) (x) (rule -> (tok list))
  (Ttree-to-toks (get-rule-body (cdr x) (car x))))

(defmlfun (|term_to_toks| ml-term_to_toks) (x) (term -> (tok list))
  (Ttree-to-toks (term-to-Ttree (prl-term x))))


(defun Ttree-to-toks-for-print (Ttree)
  (labels
    ((get-segments (chs)
       (let* ((first-NL-pos (position NL chs)))
	 (cond (first-NL-pos
		(cons (subseq chs 0 first-NL-pos)
		      (get-segments (nthcdr (1+ first-NL-pos) chs))))
	       (chs
		(list chs))
	       (t
		nil)))))
    (mapcar #'implode-for-print
	    (get-segments (ttree-to-list Ttree)))))

(defmlfun (|rule_to_toks_for_print| ml-rule_to_toks_for_print) (x) (rule -> (tok list))
  (Ttree-to-toks-for-print (get-rule-body (cdr x) (car x))))

(defmlfun (|term_to_toks_for_print| ml-term_to_toks_for_print) (x) (term -> (tok list))
  (Ttree-to-toks-for-print (term-to-Ttree (prl-term x))))


(defmlfun (|print_rule| ml-print_rule) (x) (rule -> void)
  (pstring (ml-rule_to_tok x)))

(defmlfun (|declaration_to_tok| ml-declaration_to_tok) (x) (declaration -> tok)
  (implode (Ttree-to-list (declaration-to-Ttree x))))

(defmlfun (|print_declaration| ml-print_declaration) (x) (declaration -> void)
  (pstring (ml-declaration_to_tok x)))
|#
; needs better treatment of tuples
; the parameter "cl" requests surrounding parentheses
(defun prinml (x ty cl)
  (if (atom ty)(ptoken |-|)
      (case (car ty)
         (mk-nulltyp (ml-print_void x))
         (mk-inttyp (ml-print_int x))
         (mk-toktyp (ml-print_tok x))
         (mk-booltyp (ml-print_bool x))

         ;(mk-termtyp (ml-print_term x))
;--      (mk-prooftyp (...))             ;-- fill in later.
         ;(mk-declarationtyp (ml-print_declaration x))
         ;(mk-ruletyp (ml-print_rule x))

         (mk-listyp (print_list x (cadr ty)))
         (mk-sumtyp (print_sum x ty cl))
         (mk-prodtyp (print_prod x ty cl))
         (otherwise (ptoken |-|))
  )))  ;prinml



; Print a list x whose ELEMENTS have type ty
(defun print_list (x ty)
    (pbegin 1)
    (ptoken |[|)
    (cond (x
            (prinml(car x) ty nil)
            (mapc #'(lambda (y) (ptoken |;|) (pbreak 1 0) (prinml y ty nil))
               (cdr x))))
    (ptoken |]|)
    (pend))     ; print_list



; Print value x of sum type ty
(defun print_sum (x ty cl)
    (if cl (ptoken |(|))
    (cond
     ((car x)(ptoken |inl |)(prinml (cdr x)(cadr ty) t))
     (t (ptoken |inr |)(prinml (cdr x)(caddr ty) t)))
    (if cl (ptoken |)|)))



; Print value x of product type ty
(defun print_prod (x ty cl)
    (if cl (ptoken |(|))
    (prinml(car x)(cadr ty) t)
    (ptoken |,|) (pbreak 0 0)
    (prinml (cdr x)(caddr ty) nil)
    (if cl (ptoken |)|)))


;--
;-- A couple of commands to allow output to snapshot file.
;-- N.B., will only allow one file open at a time.  It is up
;-- to the user to close the file.  To really do this correctly would
;-- require adding a type for output file descriptors to ml -- too much for
;-- what we need.
;--

(defvar %ml-out-file)

(defmlfun (|open_snapshot_file| ml-open-snapshot-file) (ignore) (void -> void)
  (unless *snapshot-file*
    (breakout evaluation '|No snapshot file.  Use set_snapshot_file.|))
  (setq %ml-out-file (outfile *snapshot-file*)))

(defmlfun (|print_to_snapshot_file| ml-print-to-snapshot-file) (string) (tok -> void)
  (princ string %ml-out-file))

(defmlfun (|print_return_to_snapshot_file| ml-print-return-to-snapshot-file) (ignore) (void -> void)
  (terpri %ml-out-file))

(defmlfun (|close_snapshot_file| ml-close-snapshot-file) (ignore) (void -> void)
  (close %ml-out-file))
