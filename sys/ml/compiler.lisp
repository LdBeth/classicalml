;;; -*- Syntax: Common-lisp; Base: 10.; Package: Nuprl; -*-
;;;
;;; Contains the top level of the compiler and the interface to the
;;; "outside" world.  There are two independent versions here.  The
;;; first half of the file is a "generic" version, and the second is
;;; tailored to Symbolics machines.

#-(or 3600 imach)
(in-package "NUPRL")

#-(or 3600 imach)
(progn

(defvar *lisp-intermediate-stream*)

(defmlfun |compile| (name prflag)
	  (token -> (bool -> void))
  (let ((piport piport)
	(%f 'compile))
    (let* ((ml-file (make-ml-filename name :ml))
	   (lisp-file (make-ml-filename name :lisp))
	   (bin-file (make-ml-filename name :bin))
	   (error-occured t))
      (when (null (probe-file ml-file))
	(msg-failwith 'compile ml-file '(ml file not found)))
      (tag loaderror
        (infilepush ml-file)
	(with-open-file (*lisp-intermediate-stream*
			  lisp-file
			  :direction :output :if-exists :supersede)
	  (write '(in-package "NUPRL") :stream *lisp-intermediate-stream*)
	  (let (%pt %ty %pr %val %head)
	    (compiloop))
	  (setq error-occured nil))
	(compile-lisp-file lisp-file)
	(delete-file lisp-file)
	(load-lisp-file bin-file))
      (when error-occured
	(msg-failwith 'compile ml-file))
      (infilepop)
      (when prflag
	(llterpri)(llprinc '|File |)(llprinc name)(llprinc '| compiled|)(llterpri)))))

(defun compiloop ()
  (tag eoftag
    (while t
      (let ((%thisdec nil)
	    (%thistydec nil)
	    (%compfns nil))
	(initlean)
	(okpass 'parse)
	(setq %head (car %pt))
	(okpass 'typecheck)
	(okpass 'translation)
	(dolist (fn %compfns)
	  (eval fn)
	  ;; pretty should be nil, orelse intermediate lisp files written
	  ;; by KCL may be huge.
	  (write (fix-uninterned-t fn) :stream *lisp-intermediate-stream*
		:gensym nil :pretty nil :escape t :level nil :length nil))
	(let ((execute-form 
	  `(execute ',(if (isdecl) %thisdec %ty) ',%thistydec ',%head ',%pr)))
	  (eval execute-form)
	  (write (fix-uninterned-t execute-form)
		:stream *lisp-intermediate-stream*
		:gensym nil :pretty nil :escape t :level nil :length nil)
		)))))


; Execute a statement and store in the output file if compiling
; For example, the putprops used to store abstract type information
(defun eval-remember (x)
  (if (eql %f 'compile)
      (write (fix-uninterned-t x) :stream *lisp-intermediate-stream*
		:gensym nil :pretty nil :escape t :level nil :length nil)
      (eval x)))


; Execute a compiled ML statement
(defun execute (%ty %thistydec %head %pr)
  (and prflag (top%f) (llterpri))
  (let ((init-time (runtimems))
	(%compfns nil))
       (okpass 'evaluation)
       (let ((final-time (runtimems)))
	 (let ((%thisdec (if (isdecl) %ty nil)))
	   (updatetypes))
         (updatevalues)
         (printresults)
         (printtime final-time init-time))))


; Fix up the particularly bad variable T, which is ok while uninterned,
; but has rather specific meanings when read back
(defun fix-uninterned-t (x)
	(subst-if '|rEpLaCeMeNt-for-T|
		#'(lambda (y) (and (symbolp y) (null (symbol-package y))
			(string= (symbol-name y) "T")))
		x
	)
)

)


;;; The Symbolics 3600 version

#+(or 3600 imach)

(progn

(defvar *binary-output-stream*)

(defmlfun |compile| (name prflag)
	  (token -> (bool -> void))
  (let ((piport piport)
	(%f 'compile))
    (let* ((ml-file (make-ml-filename name :ml))
	   (bin-file (make-ml-filename name :bin))
	   (error-occured t))
      (when (null (probe-file ml-file))
	(msg-failwith 'compile ml-file '(ml file not found)))
      (tag loaderror
        (infilepush ml-file)
	(let ((compiler:*compile-function* 'compile-to-core-and-file)
	      (compiler:suppress-compiler-warnings t))
	  (compiler:compiler-warnings-context-bind
	    (si:writing-bin-file (*binary-output-stream* bin-file)
	      (funcall compiler:*compile-function* :initialize
		       *binary-output-stream* name)
	      (let ((%pt) (%ty) (%pr) (%val) (%head))
		(compiloop))
	      (setq error-occured nil)))))
      (when error-occured
	(msg-failwith 'compile ml-file))
      (infilepop)
      (when prflag
	(llterpri)(llprinc '|File |)(llprinc name)(llprinc '| compiled|)(llterpri)))))

(defun compiloop ()
  (tag eoftag
    (while t
      (let ((%thisdec nil)
	    (%thistydec nil)
	    (%compfns nil))
	(initlean)
	(okpass 'parse)
	(setq %head (car %pt))
	(okpass 'typecheck)
	(okpass 'translation)
	(dolist (fn %compfns)
	  (compiler:compile-from-stream-1 fn))
	(compiler:compile-from-stream-1
	  `(execute ',(if (isdecl) %thisdec %ty) ',%thistydec ',%head ',%pr))))))


; Execute a statement and store in the output file if compiling
; For example, the putprops used to store abstract type information
(defun eval-remember (x)
  (if (eql %f 'compile)
      (compiler:compile-from-stream-1 x)
      (eval x)))


; Execute a compiled ML statement
(defun execute (%ty %thistydec %head %pr)
  (and prflag (top%f) (llterpri))
  (let ((init-time (runtimems))
	(%compfns nil))
       (okpass 'evaluation)
       (let ((final-time (runtimems)))
	 (let ((%thisdec (if (isdecl) %ty nil)))
	   (updatetypes))
         (updatevalues)
         (printresults)
         (printtime final-time init-time))))

(scl:defselect (compile-to-core-and-file compiler:compile-process-default)
  (:dump-definition (exp)
   (multiple-value-bind (definition fspec)
       (compiler:compile-definition exp t nil)
     (scl:fdefine fspec definition t)
     (si:dump-function-definition fspec definition *binary-output-stream*)))
  (:dump-lambda-expression (fspec lambda-exp)
   (multiple-value-bind (definition fspec)
       (compiler:compile-lambda-exp fspec
			   ;; Convert function-cell-contents to lambda-expression
			   (cond ((eql (first lambda-exp) 'special)
				  (or (third lambda-exp) (second lambda-exp)))
				 ((eql (car lambda-exp) 'macro)
				  (cdr lambda-exp))
				 (t lambda-exp))
			   t
			   `((:interpreted-definition ,lambda-exp)))
     ;; Convert lambda-expression back to function-cell-contents
     (cond ((eql (first lambda-exp) 'special)
	    (setq definition (if (third lambda-exp)
				 (list 'special (second lambda-exp) definition)
				 (list 'special definition))))
	   ((eql (car lambda-exp) 'macro)
	    (setq definition (cons 'macro definition))))
     (cond ((null fspec)
	    definition)
	   (t
	    (scl:fdefine fspec definition t)
	    fspec))
     (si:dump-function-definition fspec definition *binary-output-stream*)))
  (:dump-form (form)
	      (eval form)
	      (si:dump-form-to-eval form *binary-output-stream*)))

)
