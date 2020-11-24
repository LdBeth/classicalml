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

;
; F-iox.lisp      Original code: din,iox (lisp 1.6) part of Edinburgh LCF
;                 by M. Gordon, R. Milner and C. Wadsworth   (1978)
;                 Transported by G. Huet in Maclisp on Multics, Fall 1981
;                 Modified to do i/o using virtual ports by T.B. Knoblock,
;                 Fall, 1983.
;
; V1.4: nextch imported from F-parser, digitp,etc. exported to F-parser
; V2.2: part 4 imported from F-tml
;       local variables in protectio and syserror


(declaim (special tokempty ml-lf
            %directory fin-ligne prompt-char outfiles
            inputstack piport poport *print-level* *print-length*
            output-list poport-before-prl ))

;-- Part 0:  Modifications to allow i/o using vitual ports --
;-- which are lists.  When this mode of i/o is in use, then
;-- piport will a non-nil atom.  Input is done using the PRL scanner.
;-- Note that lisp will take piport=nil to mean 
;-- that the standard-input is to be used.  The output, while
;-- in this mode, goes into a list "output-list" in fixnum form,
;-- in the reverse order as it is generated.  Note, trying to
;-- do a readc (readch) durring this mode will cause input
;-- from stand-in to be used -- so do not do a read durring this mode.


(defun init-prl-io (input)
    (push piport inputstack)        ;-- save the old piport
    (setq piport 'prl-io-mode)      ;-- flag list-io
    (setq poport-before-prl poport) ;-- save the old poport
    (setq poport 'prl-io-mode)      ;-- flag list-io
    (prl-scanner-initialize input)  ;-- set up PRL scanner.
    (setq output-list nil)          ;-- initialize to nil.
)

;-- are we in the list-io mode?
(defun is-prl-io-mode (port)
  (and
    (atom port)          ;-- Make sure this is not a port
    (eql port 'prl-io-mode)))     ;-- check that it is not nil.


;-- end-prl-io -- turn the mode off.  Assumes are already in mode.

(defun end-prl-io ()
  (setq piport (pop inputstack))		;-- get the old value of piport
  (setq poport poport-before-prl))

; print on an output file, setting output parameters properly
(defun print-file (f x)
  (let ((*print-level* nil) (*print-length* nil))
    (print x f) (terpri f)))


;  Part 1: protectio  formerly in module din

(defun protectio (fn args)
  (let ((inputstack inputstack) (outfiles outfiles)
	(piport piport) (poport poport))
    (apply fn args)))				;NEW protectio


;  Part 2: Predicates on tokens

(defun idenp (tok)
  (let ((letters (ml-explode tok)))
    (and (letterp (car letters))
	 (forall #'alphanump (cdr letters)))))


(defun nump (tok)
 (can #'intof (list tok)))  ;nump

;                Part 3 : terminal input

(defun prompt (n) (setq prompt-char n))  ;prompt


;-- ;--  Get char.  If it is PRL-SCANNER-EOF-CHAR then do end stuff.

(defun nextch ()
  (if (is-prl-io-mode piport)
      (let ((next-char (prl-scanner-get-char))) ;-- get the char.
	(when (eql next-char 'PRL-SCANNER-EOF-CHAR)
	  (breakout eoftag t))
	next-char)
      (progn
	(ifn piport
	     (cond (fin-ligne (write-char prompt-char) (setq fin-ligne nil))))
	(let ((c (ml-readch piport nil)))
	  (ifn c (breakout eoftag nil))
	  (if (eql c ml-lf) (setq fin-ligne t))	;newline: arm prompt
	  c))))

  ;  Part 4:  file token handling and file opening, closing, etc
;(defun fileexists (kind tok)
;  (protectio #'(lambda (kind tok)
;                (search-path (fileof kind tok)))   ;NEW   sets %directory
;           (list kind tok)))  ;fileexists

(defun abs-path (path) (string (uconcat %directory path)) )  ;abs-path

(defun init-io ()
  ; #+Multics (eoffn nil 'eof-mac)
  (setq piport nil poport nil outfiles nil inputstack nil))  ; init-io

; Re-direct input from terminal to given file
; inputstack holds all previous values of piport
(defun infilepush (filespec)
       (push piport inputstack)
       (setq piport (filein filespec)))  ; infilepush

; Restore previous input file after closing current one
(defun infilepop ()
    (close piport)
    (setq piport (pop inputstack)))    ; infilepop


;(defun filedelete (kind tok) ;-- Is this used??? --- No
; (and (eql kind 'draft)
;      (protectio #'(lambda (kind tok)
;                        (delete-file (fileof kind tok))         ;NEW
;                        (terpri)(llprinc (list kind tok 'deleted))(terpri)
;                        )
;               (list kind tok))))  ;filedelete

 ;  Part 5:  output for terminal.

(defun llterpri ()
  (if (is-prl-io-mode poport)
      (push CR output-list)
      (prog1
        (terpri)
	(force-output))
))

(defun llprinc (expr)
  (if (is-prl-io-mode poport)
      (let ((string (princ-object-to-string expr)))
	(dotimes (i (length string))
	  (push (char->ichar (aref string i) LF) output-list)))
      (prog1
        (princ expr)
	(force-output))
))

(defun llprint (expr)
  (if (is-prl-io-mode poport)
      (let ((string (print-object-to-string expr)))
	(dotimes (i (length string))
	  (push (char->ichar (aref string i) LF) output-list)))
      (prog1
        (print expr)
	(force-output))
))


;-- prin1 is the same as print.
(defun llprin1 (expr)  
       (llprint expr))  ;llprin1
