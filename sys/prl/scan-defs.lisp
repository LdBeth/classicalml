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


;--      SCAN-DEFS.L
;-- 
;-- Definition of the global variables used to communicate between the
;-- parser and the scanner.
;-- 
;-- 

(defvar token-type)         ;-- The kind of token (E.g., TAll for 'All', etc.)

(defvar token-val)          ;-- The print name of an identifier or keyword
                            ;-- token.  The numeric value of a number token.
                            ;-- The universe level for a universe token.
                            ;-- The list of (integer representations of)
                            ;-- characters for a token token.  Nil for any
                            ;-- other token.

(constant white-space (list #.(ichar #\space) NL))
(defun token-is$  (x) (= token-type x))
