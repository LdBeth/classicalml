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

; F-tml.lisp      Original code: tml (lisp 1.6) part of Edinburgh LCF
;                 by M. Gordon, R. Milner and C. Wadsworth   (1978)
;                 Transported by G. Huet in Maclisp on Multics, Fall 1981
;
; V2.1 : begin and end renamed as ml-begin and ml-end
; V2.2 : errset and err replaced with tag and breakout
;        top1, ctrlgfn no more used
; V2.3 : compiler added  July 82   GH
; V3.1 : optimization of lisp code L. Paulson
; V3.2 : compatibility VAX-Unix/Multics
; V4.2 : message functions gone
; to do:  in load/compile, close input file in a clean way
;         put infilepop where it will always be executed, despite errors
;
; 2/87  Changed to work with the new compiler.  MB

(declaim (special %f %dev %pt %ty %pr %val %compfns global%env
             %sections %dump %emt %temt
             %p %lb %e %thisdec %thistydec tenv
             %compfile %head %time %debug
             ; Globals
                 initial%load  %timestamp  %symcount
                 prflag *read-base* *print-base*
                 prompt-char piport poport 
                 *print-level* *print-length*
                 msgflag initsection initenv nosecname nill
                 lastvalname eof nullty %it))



;  Uses Manifests:  eof  [iox/din]
;                   nullty  [typeml]
;                   nill  [tran]

;  Sets Manifests:  initsection, initenv, nosecname, lastvalname

;  Uses Globals:  %f  [iox/din]
;                 %emt, %temt  [typeml]
;                 prflag  [System load]
;                 ibase, base, prompt-char [lisp/tmml]
; Globals:  %pt, %ty, %pr, %val  [in top1/okpass]
;                 %sections, %dump

;  Specials:  %p, %e, %thisdec, %thistydec, tenv



(prog ()                              ;  Manifests
 (setq lastvalname '|it|)
)

(cond (initial%load                          ;  Globals
 (setq global%env nil)
 (setq %f nil)
 (setq %sections nil)
 (setq %dump nil)
 (setq %time 10000.)                ;NEW
 (setq %compfile nil)               ;NEW
 ))


;                  Error and message functions

(defun syserror (x)
       (let ((poport nil))
          (llterpri)(llprinc '|??? |)(llprinc x)(llterpri)
          (llprinc '| error in LCF or ML system, please report it|)
          (llterpri)
;--       (baktrace)
          (error %f)
          ))  ;syserror

(defun ml-space nil (llprinc '| |))

;                  Top level of ml interpreter

(defun top%f () (member %f '(nil load compile)))  ;top%f

(defun istmlop () (member %head '(mk-begin mk-end)))  ;istmlop

(defun isdefty () (eql %head 'mk-deftype))  ;isdefty

(defun isdecl ()
 (member %head '(mk-let mk-letref mk-letrec mk-abstype mk-absrectype)))  ;isdecl

(defun okpass (pass)
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
    (ifn (member %f '(load compile))(breakout tmllooptag %f))
    ; propagate failure if performing load or compile
    (setq %it nil)			 ;to prevent abscope type
;   (putprop lastvalname nil 'mlval)     ;to prevent abscope type
    (setf (get lastvalname 'mltype) nullty) ;problems on automatic ending
    (infilepop) ;flush input file
    (breakout loaderror nil))))  ;okpass  ;new look

(defun parseml0 () (gnt) (parseml 0))  ;parsml0

(defun typechpt () (typecheck %pt))  ;typechpt

(defun tranpt () (let ((%p nil)) (tran %pt)))  ;tranpt  new look


(defun evalpr ()
  (when  (neq %f 'compile)
    ;; These definitions have already been compiled.
    (dolist (defun-form %compfns)
      ;; Compile any function definitions.  The interpreter appears to exhibit
      ;; exponential behavior on complicated function definitions.
      (compile-lisp-form (second defun-form) (cons 'lambda (cddr defun-form)))))

  (breakout evaluation 		; breakout executed only when a process-err thrown.
    (cadr (catch 'process-err 
	    (return-from evalpr (eval %pr))))))

; Top-level entry to ML
; Sets time stamp to allow the generation of symbols unique to this session
; Necessary to avoid conflict when loading ML code
;    compiled in different sessions
(defun tml ()
   (let ((*print-base* 10.)
         (*read-base* 10.)
         (prompt-char #\#))
    (init-io)
    (banner)
    (tag eoftag (tag tmltag (tmlloop)))   ;so as to implement exit in ml
;;    (llterpri)(llprinc '|Back to lisp, folks!|)(llterpri) Not that for video
    (finalize-tml)              ; prepare Lisp re-entry (system dependent)
    ))  ;tml newlook

(defun tmlloop ()                               ; Also used by load
 (while t
  (tag tmllooptag
    (and prflag (top%f) (llterpri))
    (let ((%thisdec nil)
	  (%thistydec nil)
	  (%compfns nil))
      (initlean)
      (okpass 'parse)
      (setq %head (car %pt))
      (if (istmlop) (okpass 'evtmlop)
       (progn (okpass 'typecheck)
        (okpass 'translation)
        (let ((init-time (runtimems)))
          (okpass 'evaluation)
          (let ((final-time (runtimems)))
            (updatetypes) ;Uses %thisdec, %thistydec [typeml]
            (updatevalues)
            (printresults)
            (printtime final-time init-time)))
        ;New, force emacs to display results while loading.
        ;-- (if (status feature Emacs) (redisplay))
        ))))))  ;tmlloop

(defun extend-env (descriptors)
  (setf global%env (append descriptors global%env)))

; Enter bindings in environment.
(defun updatevalues ()
       (cond
         ((isdefty))
         ((isdecl)
	  (extend-env %val)
	  (dolist (desc %val)
	    (when (is-function desc)
	      (setf (symbol-value (name-for-desc desc))
		    (make-closure (symbol-function (name-for-desc desc))
				  (function-arity desc))))))
         (t (setq %it %val)
	    (setf (get lastvalname 'mltype) %ty))
         ))  ;updatevalues

(defun printresults ()
       (cond ((not prflag) (llprinc '|.|))
           ((isdefty) (prdefty %thistydec))
           ((isdecl) (prlet %val))
           (t (prvalty %val %ty))))  ;printresults


; Print runtime and GC time if either exceeds the threshhold %time
(defun printtime (final-times init-times)       
   (cond 
     (prflag
        (let ((runtime (- (car final-times) (car init-times)))
              (gctime (- (cdr final-times) (cdr init-times))))
          (cond ((> runtime %time)
                 (llprinc '|Runtime: |)(llprin1 (truncate runtime 10))
                 (llprinc '| ms|)(llterpri)))
          (cond ((> gctime %time)
                 (llprinc '|GC: |)(llprin1 gctime)
                 (llprinc '| ms|)(llterpri))))))
 )              ; printtime

(defun evtmlop (pt)
  (case (car pt)
    (mk-begin (ml-begin (if (cdr pt) (cadr pt) nosecname)))
    (mk-end
      (ml-end (cond
          ((null (cdr pt)) (if %dump (car %dump)
            (msg-failwith 'end " not in a section")))
          ((assoc (cadr pt) %dump))
          (t (msg-failwith 'end "no section " (cadr pt)))
          )))
    (otherwise (syserror (cons (car pt) '(not a tmlop))))
    ))  ;evtmlop

(defun ml-begin (tok)
  (push (list tok %sections global%env %emt %temt %dump) %dump)
  (setq %sections t)
  (cond (prflag (llprinc '|Section |)(llprinc tok)(llprinc '| begun|)(llterpri)))
       )        ;ml-begin


; Unix -- used Franz Lisp "varstruct" in let
(defun ml-end (x)
  (let ((tok (car x))
        (new-sections (cadr x))
        (new-global-env (caddr x))
        (new-emt (cadddr x))
        (new-temt (car (cddddr x)))
        (new-dump (cadr (cddddr x)))
        (tenv nil))
       (setq tenv new-temt)  ;  for absscopechk
       (ifn (tag typecheck (absscopechk (get lastvalname 'mltype)))
          (failwith 'end)) ; prevents result of section of local type
       (setq %sections new-sections)
       (setq global%env new-global-env)
       (setq %emt new-emt)
       (setq %temt new-temt)
       (setq %dump new-dump)
       (cond (prflag (llprinc '|Section |)(llprinc tok)(llprinc '| ended|)(llterpri)))
       ))  ;ml-end


(defmlfun (|load| ml-load)  (name prflag)  (token -> (bool -> void))
  (let ((oldpiport piport)
	(%f 'load)
	(%dump nil))
    (let* ((ml-file (let ((f (make-ml-filename name :ml)))
		      (unless (probe-file f)
			(msg-failwith 'load f))
		      f))
	   (bin-file (make-ml-filename name :bin)))
      (tag eoftag
	(tag loaderror				; catch failures inside load
	  (when (and (probe-file bin-file)
		     (> (file-write-date bin-file)
			(file-write-date ml-file)))
	    (breakout eoftag (load-lisp-file bin-file)))
	  (infilepush ml-file)
	  (let (%pt %ty %pr %val %head)
	    (tmlloop)))
	                                        ;an error occurred during file load
	(if %dump (ml-end (car (last %dump))))	;close dangling sections
	(msg-failwith 'load ml-file))
						;reached end of file without errors
      (if %dump (ml-end (car (last %dump))))	;close dangling sections
      (ifn (eql piport oldpiport) (infilepop))
      (when prflag
	(llterpri) (llprinc '|File |) (llprinc name) (llprinc '| loaded|) (llterpri)))))

;;; First do a regular load.  If it is successful, for each object added to the environment (the value
;;; env global%env, i.e. typedefs and dml'd objects are not included) overwrite the most recent previous
;;; definition (if it exists) with the newest one.  Return a list of the names of the objects
;;; overwritten.  If the load is not successful, roll back the environment (see above restriction) to
;;; what is was before load was called.  The function is uncurried for historical reasons.
(defmlfun (|overwriting_load| ml-overwriting-load) (fname-flag-pair) 
     ( (tok |#| bool) -> (tok list) )
  (let* ((fname (car fname-flag-pair))
	 (flag (cdr fname-flag-pair))
	 (starting-properties (get-ML-properties))
         (starting-env global%env))
    ;; Load the file normally, rolling things back if the load fails
    (let ((unwindabortflag t))
      (unwind-protect 
	  (progn
	    (ml-load flag fname)	; reversed since ml-load defmlfun'd
	    (setf unwindabortflag nil))
      (when unwindabortflag
        (remove-ML-properties)
        (setq global%env starting-env)
        (put-ML-properties starting-properties))))
    (let* ((number-of-additions (- (length global%env) (length starting-env)))
	   (env-additions (subseq global%env 0 number-of-additions))	   
	   (overwritten-object-names nil))
      ;; Check that all redefinitions respect types, etc.
      (mapc #'(lambda (p)
		(if (and (assoc (car p) starting-env)
			 (not (equal (mapcar #'(lambda (prop) (get (car p) prop)) *ML-object-property-names*)
				     (cdr (assoc (car p) starting-properties)))))
		    (progn
		      (remove-ML-properties)
		      (setq global%env starting-env)
		      (put-ML-properties starting-properties)
		      (breakout evaluation '|overwriting_load: new version of object has different type.|))))
	    env-additions)
      (setq global%env starting-env)
      ;; For each new item, overwrite the old version, or, if it's new, add it to the current
      ;; environment.
      (mapc #'(lambda (item)
		(let* ((old-item (assoc (car item) starting-env)))
		  (if old-item
		      (progn (set (third old-item) (symbol-value (third item)))
			     (if (eql (second old-item) 'ML-FUNCTION)
				 (setf (symbol-function (third old-item)) (caar (symbol-value (third item)))))
			     (push (car item) overwritten-object-names))
		      (push item global%env))))
	    (reverse env-additions))
      overwritten-object-names)))

(defmlfun (|timer| ml-timer) (thresh) (int -> void)
  (setq %time thresh))

(defmlfun (|lisp| ml-lisp) (tok) (token -> void)
  (errortrap
    '(lambda (errtok) (msg-failwith 'lisp errtok))
    (eval (with-input-from-string (*standard-input* (symbol-name tok))
	    (read)))))
