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


;;; Latex gags on large paragraphs.
(defparameter *max-paragraph-length* 100)	; in lines

(defconstant *latex-preamble* 
"\\documentstyle{article}

{\\obeyspaces\\global\\let =\\ }

\\newenvironment{bogustabbing}{\\begin{tabbing}\\=\\hspace{2em}\\=\\=\\=\\kill}%
{\\end{tabbing}}

% program is indented 2em
\\newenvironment{program}{\\tt\\obeyspaces\\begin{bogustabbing}\\+\\kill}{\\end{bogustabbing}}
\\newenvironment{program*}{\\tt\\obeyspaces\\begin{bogustabbing}}{\\end{bogustabbing}}

\\newcommand{\\mcap}{{\\boldmath$\\cap$}}
\\newcommand{\\muparrow}{{\\boldmath$\\uparrow$}}
\\newcommand{\\mdownarrow}{{\\boldmath$\\downarrow$}}
\\newcommand{\\minfty}{{\\boldmath$\\infty$}}
\\newcommand{\\mleftarrow}{{\\boldmath$\\leftarrow$}}
\\newcommand{\\mrightarrow}{{\\boldmath$\\rightarrow$}}
\\newcommand{\\mrightleftharpoons}{{\\boldmath$\\rightleftharpoons$}}
\\newcommand{\\mexists}{{\\boldmath$\\exists$}}
\\newcommand{\\mpartial}{{\\boldmath$\\partial$}}
\\newcommand{\\mwedge}{{\\boldmath$\\wedge$}}
\\newcommand{\\mcup}{{\\boldmath$\\cup$}}
\\newcommand{\\msubset}{{\\boldmath$\\subset$}}
\\newcommand{\\mforall}{{\\boldmath$\\forall$}}
\\newcommand{\\mvee}{{\\boldmath$\\vee$}}
\\newcommand{\\msupset}{{\\boldmath$\\supset$}}
\\newcommand{\\malpha}{{\\boldmath$\\alpha$}}
\\newcommand{\\mbeta}{{\\boldmath$\\beta$}}
\\newcommand{\\mdelta}{{\\boldmath$\\delta$}}
\\newcommand{\\mepsilon}{{\\boldmath$\\epsilon$}}
\\newcommand{\\mgamma}{{\\boldmath$\\gamma$}}
\\newcommand{\\mlambda}{{\\boldmath$\\lambda$}}
\\newcommand{\\mpi}{{\\boldmath$\\pi$}}
\\newcommand{\\mleq}{{\\boldmath$\\leq$}}
\\newcommand{\\mgeq}{{\\boldmath$\\geq$}}
\\newcommand{\\mint}{{\\boldmath$\\int$}}
\\newcommand{\\mcdot}{{\\boldmath$\\cdot$}}
\\newcommand{\\mneg}{{\\boldmath$\\neg$}}
\\newcommand{\\mneq}{{\\boldmath$\\neq$}}
\\newcommand{\\mequiv}{{\\boldmath$\\equiv$}}
\\newcommand{\\mpm}{{\\boldmath$\\pm$}}
\\newcommand{\\moplus}{{\\boldmath$\\oplus$}}
\\newcommand{\\motimes}{{\\boldmath$\\otimes$}}
\\newcommand{\\mdiamond}{{\\boldmath$\\diamond$}}
\\newcommand{\\msim}{{\\boldmath$\\sim$}}
\\newcommand{\\mbackslash}{{\\boldmath$\\backslash$}}

\\oddsidemargin 0in
\\evensidemargin 0in
\\topmargin -.5in
\\headheight 0in
\\headsep 0in
\\textwidth 6.5in
\\textheight 9.5in 

\\begin{document}

"
)

(defparameter *special-standard-char->latex-macro* 
	      '((#\# . "\\#")
		(#\$ . "\\$")
		(#\% . "\\%")
		(#\& . "\\&")
		(#\~ . "\\msim{}")
		(#\_ . "\\_")
		(#\^ . "\\^")
		(#\{ . "\\{")
		(#\} . "\\}")
		(#\\ . "\\mbackslash{}")))


(defun new-line-and-latex-string (line out terminate-current-line?)
  (when terminate-current-line?
    (princ "\\\\" out))
  (terpri out)
  (princ "\\>" out)
  (map nil
       #'(lambda (ch) 
	   (princ (if (alphanumericp ch)
		      ch
		      (or (cdr (assoc ch *nonstandard-graphic-code->latex-macro*
				      :test #'char=))
			  (cdr (assoc ch *special-standard-char->latex-macro*
				      :test #'char=))
			  ch))
		  out))
       line))
     
(defun string-of-blanks? (string)
  (every #'(lambda (ch) (char= ch #\space)) string))

(defun latex-paragraph (in out)
  (let ((non-blank-line-read? nil)
	(lines 0))
    (do ((l (read-line in nil) (read-line in nil)))
	((or (null l)
	     (and non-blank-line-read?
		  (string-of-blanks? l))
	     (>= lines (1- *max-paragraph-length*)))
	 (when (and l (not (string-of-blanks? l)))
	   (new-line-and-latex-string l out t))
	 (when non-blank-line-read?
	   (terpri out)
	   (latex-paragraph-conclusion out))
	 (and l t))
      (unless (string-of-blanks? l)
	(incf lines)
	(cond (non-blank-line-read?
	       (new-line-and-latex-string l out t))
	      (t
	       (setf non-blank-line-read? t)
	       (latex-paragraph-intro out)
	       (new-line-and-latex-string l out nil)))))))

(defun latex-paragraph-conclusion (out)
  (princ "\\end{program*}" out)
  (terpri out)
  (terpri out))

(defun latex-paragraph-intro (out)
  (princ "\\begin{program*}" out))

(defun latex-preamble (out)
  (princ *latex-preamble* out))

(defun latex-postamble (s)
  (format s "~%\\end{document}"))

(defun latexize-file (input-file output-file
		      &optional (nonstandard-chars-only? nil))
  (with-open-file (in
		    input-file
		    :direction :input)
    (with-open-file (out
		      output-file
		      :direction :output
		      :if-exists :new-version
		      :if-does-not-exist :create)
      (cond (nonstandard-chars-only?
	     (do ((ch (read-char in nil nil) (read-char in nil nil)))
		 ((null ch))
	       (if (alphanumericp ch)
		   (write-char ch out)
		   (let ((macro
			   (cdr (assoc ch *nonstandard-graphic-code->latex-macro*))))
		     (if macro
			 (princ macro out)
			 (write-char ch out))))))				
	    (t
	     (latex-preamble out)
	     (do ((paragraph? (latex-paragraph in out)
			      (latex-paragraph in out)))
		 ((not paragraph?)))
	     (latex-postamble out)))))
  (values))


(defmlfun |latexize_file| (input-file output-file) (tok -> (tok -> void))
  (latexize-file input-file output-file))

(defun latexize-nonstandard-chars-in-file (input-file output-file)
  (latexize-file input-file output-file t))

(defmlfun |latexize_nonstandard_chars_in_file|
	  (input-file output-file) (tok -> (tok -> void))
  (format t "~%Warning: macro definitions not being added.  ~
                             Use latexize_file to get them.~%")
  (latexize-nonstandard-chars-in-file input-file output-file))



;;;---------------------------------------------------------------------------

(defvar *indentation*)
(defvar *output-stream*)

;; these functions affect the output for print-library and snapshot.
(defvar *output-for-latexize* t)

(defun set-output-for-latexize (x)
  (setf *output-for-latexize* x))

(defmlfun (|set_output_for_latexize| ml-set-output-for-latexize) (x)
	  (bool -> void)
  (set-output-for-latexize x))


(defun new-line (&optional (n 1))
  (dotimes (i n) (terpri *output-stream*)))

(defun print-string (str)
  (print-space *indentation*)
  (princ str *output-stream*))

;;; ch not a newline.
(defun print-ichar (ch)
  (if *output-for-latexize*
      (princ (ichar->char-for-latexize ch) *output-stream*)
      (princ (ichar->char-or-string ch) *output-stream*)))

;;; Assume printing is starting on a new line.
(defun print-istring (str)
  (print-space *indentation*)
  (do* ((str str (cdr str)))
       ((null str))
    (cond ((member (car str) *newline-ichars*)
	   (new-line)
	   (print-space *indentation*))
	  (t
	   (print-ichar (car str))))))

(defun print-space (&optional (n 1))
  (dotimes (i n) (print-ichar *ispace*)))

(defun with-indentation (incr f &rest args)
  (let* ((*indentation* (+ incr *indentation*)))
    (apply f args)))

;;; Strip all trailing new-lines.
(defun print-Ttree (Ttree)
  (let* ((istring (Ttree-to-list Ttree))
	 (length
	   (1+ (or (position-if-not
		     #'(lambda (ich) (member ich *newline-ichars*))
		     istring :from-end t)
		   (1- (length istring))))))
    (print-istring (subseq istring 0 length))))

(defun print-term (term)
  (print-Ttree (term-to-Ttree term)))

(defun status-string (status)
  (case status
    (PARTIAL "#")
    (BAD "-")
    (RAW "?")
    (COMPLETE "*")))
	      
(defun is-name-of-ext-theorem (name)
  (= (length (string-right-trim '(#\_) (string name)))
     (1- (length (string name)))))  

(defun print-extraction (name)
  (let* ((ext-term (catch 'process-err
			  (evaluable-term-of-theorem name))))
    (cond ((not (null ext-term))
	   (print-string "Extraction:")
	   (new-line)
	   (print-term ext-term)))))

(defun print-library (first-object last-object filename)
  (unless (null library$)
    (let ((start (if (eq first-object '|first|)
		     0
		     (position first-object library$)))
	  (end (if (eq last-object '|last|)
		   (1- (length library$))
		   (position last-object library$))))
      (unless (and start end) (error "Objects not in library."))
      (with-open-file (*output-stream* (string filename)
				       :direction :output
				       :if-exists :new-version
				       :if-does-not-exist :create)
	(let* ((*indentation* 0))
	  (for (name in (subseq library$ start (1+ end)))
	       (do
		 (let* ((obj (library-object name))
			(val (sel (object obj) value))
			(status (sel (object obj) status))
			(kind (sel (object obj) kind)))
		   (format *output-stream* "~A ~A ~A~%"
			   (status-string status) (string kind) (string name))
		   (case kind 
		     (THM
		       (with-indentation
			 2 #'print-Ttree (sel (theorem-object val) goal-body))
		       (when (is-name-of-ext-theorem name)
			 (new-line)
			 (with-indentation 2 #'print-extraction name)))
		     (ML
		       (with-indentation
			 2 #'print-Ttree (sel (ml-object val) body)))
		     (EVAL
		       (with-indentation
			 2 #'print-Ttree (sel (eval-object val) body)))
		     (DEF
		       (with-indentation
			 2 #'print-Ttree (sel (definition-object val) body))))
		   (new-line 2)))))))))

(defmlfun |print_library| (first last filename) (tok -> (tok -> (tok -> void)))
  (unless (and (or (member first '(|first| |last|))
		   (member first library$))
	       (or (member last '(|first| |last|))
		   (member last library$)))
    (breakout evaluation '|print_library: start or end not in library.|))
  (print-library first last filename))



;;; ********************************************************************************

;;; Following is an experimental pretty printer.  So far, it is only implemented
;;; for the function subset of prl plus pairing.  

;;; ********************************************************************************

(defun pretty-print-ml-term (ml-term &optional (output-file nil))
  (if output-file
       (with-open-file (s output-file 
			  :direction :output
			  :if-exists :append
			  :if-does-not-exist :create)
	 (terpri s) (terpri s)
	 (pprint (prl-term-to-sexpr (prl-term ml-term)) s))
       (pprint (prl-term-to-sexpr (prl-term ml-term))))
  nil)

(defmlfun (|pretty_print_term_to_file| ml-pretty-print-term-to-file) (ml-term fname)
	  (term -> (tok -> void))
  (pretty-print-ml-term ml-term (symbol-name fname))
  nil)

;;; Collapses right associated pairing, left associated application, and lambda sequences.  
(defun prl-term-to-sexpr (term)
  (case (kind-of-term term)
    (VAR (id-of-var-term term))
    (APPLY (reverse (get-reversed-application-sequence term)))
    (LAMBDA `(LAMBDA ,(get-lambda-vars term) ,(get-lambda-body term)))
    (PAIR `(TUPLE ,@(get-tuple-body term)))
    (TERM-OF-THEOREM (name-of-term-of-theorem-term term))
    (TOKEN (atom-of-token-term term))
    (otherwise '|<type>|)))

(defun get-tuple-body (term)
  (if (eql (kind-of-term term) 'PAIR)
       (cons (prl-term-to-sexpr (leftterm-of-pair-term term))
	     (get-tuple-body (rightterm-of-pair-term term)))
       (list (prl-term-to-sexpr term))))

(defun get-lambda-vars (term)
  (if (eql (kind-of-term term) 'LAMBDA)
       (cons (bound-id-of-lambda-term term)
	     (get-lambda-vars (term-of-lambda-term term)))
       ()))

(defun get-lambda-body (term)
  (if (eql (kind-of-term term) 'LAMBDA)
       (get-lambda-body (term-of-lambda-term term))
       (prl-term-to-sexpr term)))

(defun get-reversed-application-sequence (term)
  (if (eql (kind-of-term term) 'APPLY)
       (cons (prl-term-to-sexpr (arg-of-apply-term term))
	     (get-reversed-application-sequence (function-of-apply-term term)))
       (list (prl-term-to-sexpr term))))


;;; --------------------------------------------------------------------------------


(defun get-write-char (output-stream line-width)
  (let ((current-column 0))
    (when (< line-width 1)
      (error "line width must be >0"))
    #'(lambda (ch indentation)
	(when ch
	  (cond ((and (equal ch :freshline)
		      (= current-column 0)))
		((member ch '(#\newline #\return :freshline) :test #'equal)
		 (terpri output-stream)
		 (setf current-column 0))
		(t
		 (when (= current-column line-width)
		   (terpri output-stream)
		   (setf current-column 0))
		 (dotimes (i (- indentation current-column))
		   (write-char #\space output-stream)
		   (incf current-column))
		 (write-char ch output-stream)
		 (incf current-column)))
	  t))))

  
