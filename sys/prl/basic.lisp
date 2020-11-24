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

(declaim (special *output-for-latexize* *nonstandard-graphic-ichars*
                  *nonstandard-graphic-ichar->string*))

(defun getd (x) (symbol-function x))
(defun putd (name func) (setf (symbol-function name) func))
(defun dtpr (x) (consp x))
(defun get_pname (x) (symbol-name x))
(defun patom (x) (print x))
(defun copy (x) (copy-tree x))
(defun make-cdr-coded (x) (copy-list x))

(defun implode (x)
  (intern (apply #'concatenate
		 (cons 'string (map 'list
				    #'(lambda (y)
					(if (integerp y)
					    (string (ichar->char y))
					    (string y)))
				    x)))
	  (find-package 'nuprl)))

(defun implode-for-print (x)
  (intern (apply #'concatenate
		 (cons 'string (map 'list
				    #'(lambda (y)
					(if (integerp y)
					    (if *output-for-latexize*
						(string (ichar->char-for-latexize y))
						(string (ichar->char-or-string y)))
					    (string y)))
				    x)))
	  (find-package 'nuprl)))

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

(defun Pboundp (name)
    (cond ((boundp name) (cons nil (symbol-value name))) (t nil)))
(defun append1 (l x) (append l (list x)))

(setq *read-base* 10.)  ;-- make the reader/printer work in decimal
(setq *print-base* 10.)

(defun fill-byte-vector (vec index count value)
    (fill-vector vec index count value))

(defun onep (x)
    (= x 1))

(defun nthelem (index list) (nth (1- index) list))

(defun explode (x)
  (map 'list #'(lambda (y) (intern (string y) (find-package 'nuprl)))
       (coerce (print-object-to-string x) 'list)))

(defun explodec (x)
  (coerce (princ-object-to-string x) 'list))

(defvar *object-string* (make-array 100 :element-type 'character :fill-pointer 0
				    :adjustable t))

(defun print-object-to-string (obj)
  (prin1-to-string obj))

;(defun print-object-to-string (obj)
;  (setf (fill-pointer *object-string*) 0)
;  (with-output-to-string (s *object-string*)
;    (prin1 obj s))
;  *object-string*)

(defun princ-object-to-string (obj)
  (princ-to-string obj))

;(defun princ-object-to-string (obj)
;  (setf (fill-pointer *object-string*) 0)
;  (with-output-to-string (s *object-string*)
;			 (princ obj s))
;  *object-string*)

(defun concat (&rest x) (implode (mapcan #'istring x)))
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


(defun set-equal (x y &key (test #'eql))
  (labels ((f (x y)
	     (if (null x)
		 (null y)
		 (and (member (car x) y :test test)
		      (f (cdr x)
			 (remove-if #'(lambda (z) (funcall test (car x) z)) 
				    y))))))
    (f x y))) 

;;; Assumption: char-code is ascii.

;;; An internal character in Nuprl is a non-negative integer or a
;;; one-element list of symbols.
(deftype ichar () '(or fixnum list))

(defun ichar= (ch1 ch2) (equal ch1 ch2))

(defconstant BACKSPACE 8)
(defconstant LF 10)
(defconstant CR 13)
(defconstant NL 0)
(defconstant *newline-ichars* '(0 10 13))
(defconstant SPACE 32)
(defconstant TAB 9)
(defconstant *ispace* SPACE)
(defconstant *idelete* '(DEL))
(defconstant *i-kill-line* '(KILL-LINE))

(defvar SCRHEIGHT 60)
(defvar SCRWIDTH 120)

;;; Lisp characters are converted to prl characters using char-code,
;;; except that character codes less than 32 must be shifted in order
;;; not to clash with existing prl characters.  For historical reasons,
;;; codes are shifted up by 142.  

(defun shift-code (x)
  (if (and (numberp x) (<= 0 x 31))
      (+ x 142)
      x))

(defun unshift-code (x)
  (if (and (numberp x) (<= 142 x 173))
      (- x 142)
      x))

(defun ichar->char (ich)
  (cond ((not (numberp ich))
	 #\space)
	((member ich *newline-ichars*)
	 #\newline)
	((eql ich TAB)
	 #\tab)
	((code-char (unshift-code ich)))))
  
(defun char->ichar (ch &optional (newline-ichar NL))
  (cond ((char= ch #\newline)
	 newline-ichar)
	((char= ch #\tab)
	 TAB)
	((shift-code (char-code ch)))))

(defun graphic-ichar? (ich)
  (and (numberp ich)
       (or (let ((ch (code-char (unshift-code ich))))
	     (graphic-char-p ch))
	   (member ich *nonstandard-graphic-ichars*))))

;;; For a reasonable print representation.
(defun ichar->char-or-string (ich)
  (let ((ch (ichar->char ich)))
    (if (or (graphic-char-p ch)
	    (standard-char-p ch))
	ch
	(or (cdr (assoc ich *nonstandard-graphic-ichar->string*))
	    #\space))))

(defun ichar->char-for-latexize (ich)
  (if (and (numberp ich) (<= 142 ich 173))
      (nonstandard-graphic-ichar->latexizable-char ich)
      (let ((ch (ichar->char ich)))
	(if (or (graphic-char-p ch)
		(standard-char-p ch))
	    ch
	    #\space))))

(defun istring (x)
  (map 'list #'char->ichar (princ-object-to-string x)))

(defun ichar (ch) (char->ichar ch))

(defvar *snapshot-file* nil)

