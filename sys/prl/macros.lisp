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

;;; Base level macros of the prl system.
;;;

;;; Give an alternative to defsubst for vanilla common lisp

;
;  Definitions to make Common-lisp look like Franz
;

(defun getd (x) (symbol-function x))
(defun putd (name func) (setf (symbol-function name) func))
(defun dtpr (x) (consp x))
(defun aexploden (x) (map 'list #'char-code (string x)))
(defun get_pname (x) (symbol-name x))
(defun patom (x) (print x))
(defun copy (x) (copy-tree x))
(defun make-cdr-coded (x) (copy-list x))
(defmacro Pmod (&body l) `(rem ,@l))
(defmacro add (&body l) `(+ ,@l))
(defmacro diff (&body l) `(- ,@l))
(defmacro product (&body l) `(* ,@l))

(defun readlist (x) (read-from-string (string (implode x))))
(defun catch-error (x &optional y) (declare (ignore y)) (list x))
(defun ncons (x) (cons x nil))
(defun neq (x y) (not (eql x y)))
(defun rot (x b)
  (logand #xffffffff
	  (if (minusp b)
	      (let ((b1 (logand #x1f (- b))))
		(dpb x (byte b1 (- 32 b1)) (ash x (- b1))))
	      (let ((b1 (logand #x1f b)))
		(logior (ash x b1) (ldb (byte b1 (- 32 b1)) x))))))

(defun ascii (x) (intern (string (code-char x)) (find-package 'nuprl)))

(defun Pboundp (name)
    (cond ((boundp name) (cons nil (symbol-value name))) (t nil)))
(defun append1 (l x) (append l (list x)))

(setq *read-base* 10.)  ;-- make the reader/printer work in decimal
(setq *print-base* 10.)

(defun istring (stringable)
  (aexploden stringable))

(defun ichar (character)
  (car (aexploden character)))

(defun fill-byte-vector (vec index count value)
    (fill-vector vec index count value))

(defun onep (x)
    (= x 1))

(defun nthelem (index list) (nth (1- index) list))

(defun exploden (x)
  (map 'list #'char-code (princ-object-to-string x)))

(defun explode (x)
  (map 'list #'(lambda (y) (intern (string y) (find-package 'nuprl)))
       (coerce (print-object-to-string x) 'list)))

(defun implode (x)
  (intern (apply #'concatenate
		 (cons 'string (map 'list
				    #'(lambda (y)
					(if (integerp y)
					    (string (code-char y))
					    (string y))) x)))
	  (find-package 'nuprl)))

(defun explodec (x)
  (coerce (princ-object-to-string x) 'list))

(defvar *object-string* (make-array 100 :element-type 'string-char :fill-pointer 0
				    :adjustable t))

(defun print-object-to-string (obj)
  (setf (fill-pointer *object-string*) 0)
  (with-output-to-string (s *object-string*)
    (prin1 obj s))
  *object-string*)

(defun princ-object-to-string (obj)
  (setf (fill-pointer *object-string*) 0)
  (with-output-to-string (s *object-string*)
    (princ obj s))
  *object-string*)

(defun concat (&rest x) (implode (mapcan #'exploden x)))
(defun infile (file) (open file :direction :input))
(defun outfile (file) (open file 
			    :direction :output
			    :if-exists :append
			    :if-does-not-exist :create))

(defun divide (x y) (list (truncate x y) (rem x y)))

(defun fill-vector (vec index count value)
    (dotimes (i count) (setf (aref vec (+ index i)) value)))

(defun prl-every (l &optional (f #'(lambda (x) x)))
  (every f l))

(defun Pevery (f l)
  (every f l))

