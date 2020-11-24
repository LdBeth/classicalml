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

;-- File of the communication stuff between PRL and CML.

;-- INIT-ML  -- Call this only once per sesion.

(defun INIT-ML ()
    (setq initial%load nil)
    (setq eof '$eof$)
    (setq fin-ligne nil)
    (setdebug nil)
    (setq prflag t)
    (setq %mlprindepth 3)
    (init-io)
)


;-- This is a modification of the tml function in F-tml.
;;; Append an NL to the input; this is a hack to avoid
;;; having to find the real source of the problem.
(defun ML (input)
  (declare (special MLinput))
  (let ((input (append input (list LF))))
    (prog (*print-base* *read-base* prompt-char okay %ty)
        (setq MLinput input)
        (setq *print-base* 10.)
        (setq *read-base* 10.)
        (setq prompt-char (getascii '|#|))

        (init-prl-io input)     ;-- skip the Ttree token.
        (setq okay nil)               ;-- not okay yet.
        (tag tml-error-tag
            (tag eoftag
                (tag tmltag
                    (prl-mlloop)
                )
                (setq okay t)
            )
            (if (not okay) (llprinc '|Error:  Premature end of input.|))
        )
        (end-prl-io)
        (cond (okay (return (cons 'SUCCESS (nreverse output-list))))
              (t (return (cons 'FAILURE (nreverse output-list)))) 
        )          
    ))
)




(defun prl-mlloop ()
     (while t           ;-- will be stoped with a breakout.
        (tag tmllooptag
;--         (and prflag (top%f) (llterpri))   ;-- not so many ml-lf's
            (let ((%thisdec nil)
		  (%thistydec nil)
		  (%compfns nil))
                (initlean)
                (prl-okaypass 'parse)
                (setq %head (car %pt))
                (if (istmlop) (prl-okaypass 'evtmlop)
                  (progn  (prl-okaypass 'typecheck)
                    (prl-okaypass 'translation)
                    (let ((init-time (runtimems)))
                        (prl-okaypass 'evaluation)
                        (let ((final-time (runtimems)))
                            (updatetypes) ;Uses %thisdec, %thistydec [typeml]
                            (updatevalues)
                            (printresults)
                            (printtime final-time init-time)))
                ))
            )
        )
     )
     (breakout tmltag nil)
)
      



;-- modified version of prl-okaypass in F-tml.l

(defun prl-okaypass (pass)
 (tag ok        ; prog/return does not work in Franzlisp
   (let ((b (case pass
       (parse (tag parse (setq %pt (parseml0)) (breakout ok t)))
       (typecheck (tag typecheck
                       (setq %ty (typechpt)) (breakout ok t)))
       (translation (tag translation
                         (setq %pr (tranpt)) (breakout ok t)))
       (evaluation (tag evaluation
                        (setq %val (evalpr)) (breakout ok t)))
       (evtmlop (tag evaluation
                     (setq %val (evtmlop %pt)) (breakout ok t)))
       (otherwise (syserror (cons pass '(unknown pass)))))))
    ; Fall through here if pass failed
    (llprinc pass)(llprinc '| failed     |)(if b (llprinc b))(ml-space)
    (llterpri)
    (setq %it nil)
;   (putprop lastvalname nil 'mlval)     ;to prevent abscope type
    (setf (get lastvalname 'mltype) nullty) ;problems on automatic ending
;    (end-prl-io)                        ;-- terminate list-io
    (breakout tml-error-tag nil)         ;-- prl break-out
   )
 )
)




