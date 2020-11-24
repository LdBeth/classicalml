;;; -*- Syntax: Common-lisp; Base: 10.; Package: Nuprl -*-
;;;
;;; Functions for dealing with closures.  The format of a closure and the
;;; implementation of ap below should probably be reexamined for each system on
;;; which this is to run.  They depend on factors such as the efficiency of &rest
;;; arguments and the ability to call a function with a runtime variable number
;;; of arguments without consing an argument list.
;;;
;;; The implementation given here is of course tuned for Lisp Machines.  It
;;; exploits cdr-coding to use the smallest possible amount of space for
;;; closures.  It is implemented under the assumption that &rest arguments are
;;; cheap ie not consed.  It exploits the ability to call a function with a
;;; runtime variable number of arguments without consing an argument list.
;;;
;;; In this implentation there are two parts to a closure:
;;;   1) A pair containing the lisp function and its arity.
;;;   2) A list of the previously collected arguments.
;;;
;;; In a system where &rest arguments are consed, there should probably be a
;;; separate ap function for each of the common cases of 1, 2 or 3 arguments.
;;; Also in such a case, there isn't the need for runtime variable number of
;;; arguments function calling as the &rest argument list can be destructively
;;; modified instead.  Also, there isn't the need to cons up the closure; the
;;; argument list can be incorporated.

(in-package "NUPRL")

(declaim (inline closure-func closure-arity closure-fdescriptor closure-env))

(defun closure-func (c) (car (first c)))
(defun closure-arity (c) (cdr (first c)))
(defun closure-fdescriptor (c) (first c))
(defun closure-env (c) (cdr c))

(defmacro fast-length (l)
  ;; A version of length which avoids a function call for lists of length < 5.
  `(block length
     (let ((length 0)
	   (l ,l))
       ,@(macrolet ((inc-and-check ()
		      ''((setf l (cdr l))  (incf length)
			 (when (null l) (return-from length length)))))
	   `((when (null l) (return-from length length))
	     ,@(inc-and-check) ,@(inc-and-check)
	     ,@(inc-and-check) ,@(inc-and-check)
	     ,@(inc-and-check)
	     ;; If the end hasn't been reached yet, default to the
	     ;; standard length function.
	     (return-from length (+ length (length l))))))))

(defun ap (f &rest args)
  ;; Apply an ML closure to arguments and return the result.
  (prog (func arity Penv nargs env-length args-needed)
	(setf nargs (fast-length args))
     again
	(setf func (closure-func f))
	(setf arity (closure-arity f))
	(setf Penv (closure-env f))
	(setf env-length (fast-length Penv))
	(setf args-needed (- arity env-length))
	(if (< nargs args-needed)
	    ;; Build and return a closure containing the new arguments.  The
	    ;; closure is cdr-coded except for the last "cons" which needs to
	    ;; have a cdr-normal so it can be rplacd'd to the rest of the
	    ;; environment.
	    (let* ((c (make-list (+ nargs (if (null Penv) 1 2))))
		   (p c))
	      (setf (first p) (closure-fdescriptor f))
;	      (dolist (arg args) (setf p (cdr p)) (setf (first p) arg))
	      (dotimes (i nargs)
		 (setf p (cdr p))
		 (setf (first p) (car args))
		 (setf args (cdr args)))
	      (when (not (null Penv))
		;; Undo lispm cdr-coding.
		#+3600
		(sys:%change-list-to-cons p)
		(rplacd p Penv))
	      (return c))
	    ;; Apply the lisp function to the arguments storing the result in
	    ;; f.
	    (progn
	      (decf nargs args-needed)
	      (let ((argp args)
		    ;; Don't need arglist when not doing special lispm hacks.
		    #-(or imach 3600)
                    arglist)
		;; The argument list is reversed, so the arguments for this call
		;; are at the end of the list.
		(dotimes (i nargs) (setf argp (cdr argp)))
		;; Use Lisp Machine subprimitives to call the function, popping
		;; the needed arguments from argp.  (See manual 8).
		#+(or imach 3600)
		(sys:%start-function-call func t arity nil)
		(do () ((zerop args-needed))
		  #+(or imach 3600)
		  (sys:%push (pop argp))
                  ;; If not Lisp Machine, do something general and inefficient
		  #-(or imach 3600)
		  (push (pop argp) arglist)
		  (decf args-needed))
		(do () ((zerop env-length))
		  #+(or imach 3600)
		  (sys:%push (pop Penv))
		  #-(or imach 3600)
		  (push (pop Penv) arglist)
		  (decf env-length))
		#+(or imach 3600)
		(setf f (sys:%finish-function-call func t arity nil))
		#-(or imach 3600)
		(setf f (apply func (nreverse arglist))))
	      (if (zerop nargs)
		  (return f)
		  ;; If there are still arguments to process, make a tail
		  ;; recursive call of ap.  The type system guarantees that f will
		  ;; be a closure.
		  (go again))))))


