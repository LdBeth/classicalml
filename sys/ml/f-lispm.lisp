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


(declaim
 (special  %pt %ty %pr %val %compfns
           %thisdec %thistydec
           %head initial%load  %timestamp  %symcount
           %ctime
           prflag *read-base* *print-base*
           prompt-char piport poport
           *print-level* *print-length*
           msgflag lastvalname eof nullty output-list))

; LISP MACHINE compatibility package.
; All Lisp Machine dependent functions reside here

;;; type-specifier is one of '(:bin :ml :lisp).  
(defun make-ml-filename (name type-specifier)
  (let* ((name (string name))
         (filename-extension
           (case type-specifier
             (:ml "ml")
             (:lisp *lisp-file-extension*)
             (:bin *bin-file-extension*))))
    (concatenate 'string name "." filename-extension))) 

; Returns (jobtime . gctime) where jobtime does not include gctime
; Unix -- return current runtime in milliseconds (rounded)
; Depends on line frequency
(defun runtimems ()
  (cons (truncate (get-internal-run-time) 100) 0)) ; get time in microsec and div by 100.

; get absolute time for time-stamps
(defun clock () (get-universal-time)) 

; record when system was built
(setq %ctime (get-decoded-time))

(defun banner ()
       (declare (special %version experimental))
       (terpri)
       (princ '|Cambridge ML modified for PRL, version |)
       (princ %version)
       (cond (experimental (princ '|Experimental system!|) (terpri)))
 )  ;banner

(defun ml-save (tok)
  tok
  (error "Tried to do a dump-lisp.  No such thing on lisp machine."))

; Lisp machine will accept anything (at this stage) for a path
(defun filetokp (kind tok)
  kind tok
   t)

(defmacro uconcat (&rest atoms)
  `(concat ,@atoms))
(defmacro concatlist (&rest atoms)
  `(concat ,@atoms))

(defun bigger (obj size)  (> (length (princ-to-string obj)) size))  ;bigger

; Turn off debugging switches and set top level to (tml)
(defun setup ()

    (declare (special experimental initial%load prflag fin-ligne))

    (cond (experimental
              (princ "Version experimentale")  (terpri)
              (experimental-init)))

    (setq initial%load nil)   ; patching does not cause re-initialization
    (setq prflag t)
    (setq fin-ligne nil)

    (setdebug nil)
    (tml)
)           ;-- changed from a reset to a direct call to tml.
            ;-- it was the case that setdebug set the top level to tml,
            ;-- so the reset did a tml.  This has been changed.



; Turn debugging on/off
; sets Lisp debugging switches, interrupt handler, and top-level
(defun setdebug (flag)
 (declare (special $gcprint))
 (cond
  (flag
     (setq $gcprint t)          ; monitor garbage collections
     (setq *print-length* 6)        ; control printing of circular lists
     (setq *print-level* 4))
  (t (setq $gcprint nil)
     (setq *print-length* nil)
     (setq *print-level* nil)
     )))  ;setdebug

  
; initialize system in experimental mode
; turn debug options on
(defun experimental-init ()
     (setdebug t))      ; experimental-init


; Function called before returning to Lisp
; Clears user-top-level to prevent automatic re-entry to ML
(defun finalize-tml ()
   (setdebug t))                ; finalize-tml

(defmacro genprefix (&rest args)
  (declare (ignore args))
  nil)

(defmacro filein (file)
        `(infile ,file))

(defmacro tag (name &body body)
  `(catch ',name (progn ,@body)))

(defvar %breakout-tag '(BREAKOUT-TAG))

(defmacro breakout (name &body body)
  `(throw ',name (values (progn ,@body) %breakout-tag)))

(defmacro while (test &body body)
  `(prog () etiq
	 (cond (,test ,@body (go etiq))
	       (t (return ())))))		;while

(defmacro ifn (test then . else)
  `(cond ((not ,test) ,then) (t nil ,@else)))	;ifn


;;; Following is a gross hack.  There was a problem with reading ML
;;; files: if there were no characters after the last ";;", then the
;;; last ML form would not be processed (its processing was interrupted
;;; by eof).  Since ML io is mixed together with prl-io and the Ttree
;;; crap, it appeared to me that it would take a long time to track down
;;; the real source of the problem.  Hence the hack:  ml-readch, upon
;;; seeing an eof, will return a blank, saving the eof till its next
;;; call.  It works, eh.
(defvar *eof-pending?* nil)

(defun ml-readch (port eof)
  (if *eof-pending?*
      (or (setf *eof-pending?* nil) eof)
      (let ((ch (read-char port nil eof)))
	(if (equal ch eof)
	    (and (setf *eof-pending?* t) '| |)
	    (implode (list (char->ichar ch LF)))))))

(declaim (special initial%load experimental %debug %version %mlprindepth))

               ; (3 . 2)    1st October 1982       The portable LCF
               ; 4          1st November 1982      LCF with full PPLAMBDA
               ; (4 . 1)    1st December 1982      Emacs Formel
               ; (4 . 2)    1st March 1983         revised theory package


(setq %version '(4 . 3))        ;
(setq %debug nil)

(setq experimental nil)

(setq eof '$eof$)
(setq prflag nil)
(setq %mlprindepth 3)

(setq initial%load t)   ; allow modules to initialize themselves


