;;; -*- Package: Nuprl; Syntax: Common-Lisp; Base: 10.; Mode: Lisp -*-

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

;;; Used in compiling ML files.
(defun compile-lisp-file (input-file &key output-file)
  (cond (output-file
	 #+lucid
	 (let ((b (getf (user::compiler-options) :fast-entry)))
	   (unwind-protect 
		(progn (user::compiler-options :fast-entry t)
		       (compile-file input-file :output-file output-file 
				     :messages nil :warnings nil))
	     (user::compiler-options :fast-entry b)))
	 #+3600
	 (let ((compiler:suppress-compiler-warnings t))
	   (compile-file input-file :output-file output-file ))
	 #-(or 3600 lucid)
	 (compile-file input-file :output-file output-file ))
	(t
	 #+lucid
	 (let ((b (getf (user::compiler-options) :fast-entry)))
	   (unwind-protect 
		(progn (user::compiler-options :fast-entry t)
		       (compile-file input-file :messages nil :warnings nil))
	     (user::compiler-options :fast-entry b)))
	 #+3600
	 (let ((compiler:suppress-compiler-warnings t))
	   (compile-file input-file))
	 #-(or 3600 lucid)
	 (compile-file input-file))))

;;; Used in loading compiled ML files.
(defun load-lisp-file (filename)
  #+symbolics 
  (load filename :package (find-package 'nuprl))               ;package necessary.
  #+lucid
  (let ((system::*redefinition-action* :quiet))
    (load filename :verbose nil))
  #-(or lucid symbolics)
  (load filename :verbose nil))

(defun compile-lisp-form (function-spec &optional lambda-exp)
  #+3600
  (let ((compiler:suppress-compiler-warnings t))
    (compile function-spec lambda-exp))
  #+lucid
  (let ((b (getf (user::compiler-options) :fast-entry)))
    (unwind-protect
	 (progn (system::compiler-options :messages nil :warnings nil)
		(user::compiler-options :fast-entry t)
		(compile function-spec lambda-exp))
      (system::compiler-options :messages t :warnings t)
      (user::compiler-options :fast-entry b)))
  #-(or 3600 lucid)
  (compile function-spec lambda-exp))

;;; E.g. on the symbolics codes 0-31 are greek letters etc obtaining via
;;; the SYMBOL key.  These characters will be allowed in identifiers.
(defparameter *nonstandard-graphic-ichars*
              (mapcar
                #'shift-code
                (or
                  #+symbolics
                  '(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18
                      19 20 21 22 23 24 25 26 27 28 29 30 31)
                  #+(or (and lucid sun windows) xlib)
                  '(0 1 2 3 4 5 6 7 8 9 11 12 13 14 15 16 17 18 19
                      20 21 22 23 24 25 26 27 28 29 30 31))))

#+symbolics
(cp:define-command
  (com-nuprl :name "Nuprl"
             :command-table (si:find-comtab 'global)
             :provide-output-destination-keyword nil)
    (&key
      (character-size 'scl:symbol
                      :name "Character Size"
                      :default (third *nuprl-character-style*)
                      :mentioned-default :normal
                      :prompt "A character size"
                      :documentation
                      "One of :very-small, :small, :normal, :large, or :very-large")
      (character-face 'scl:symbol
                      :name "Character Face"
                      :default (second *nuprl-character-style*)
                      :mentioned-default :roman
                      :prompt "A character style face"
                      :documentation "One of :roman, :bold, :italic, or :bold-italic")
      (label-character-face 'scl:symbol
                            :name "Heading Character Face"
                            :default (second *nuprl-label-char-style*)
                            :mentioned-default :roman
                            :prompt "A character style face for headings"
                            :documentation "One of :roman, :bold, :italic, or :bold-italic"))
   (let ((style-changed? (change-nuprl-character-styles
                           (list :fix character-face character-size)
                           (list :fix label-character-face character-size))))
     (when (and prl-initialized$  style-changed?)
       (reset)))
   (in-package "NUPRL")
   (prl)
   (values))


;;; Roughly the lispm's "symbol" characters.  The macros get defined
;;; in a header put out by functions in io.lisp.  
(defparameter *nonstandard-graphic-code->latex-macro*
              #+symbolics
              `((,(code-char 18) . "\\mcap{}")
                (,(code-char 11) . "\\muparrow{}")
                (,(code-char 1) . "\\mdownarrow{}")
                (,(code-char 14) . "\\minfty{}")
                (,(code-char 24) . "\\mleftarrow{}")
                (,(code-char 25) . "\\mrightarrow{}")
                (,(code-char 23) . "\\mrightleftharpoons{}")
                (,(code-char 21) . "\\mexists{}")
                (,(code-char 15) . "\\mpartial{}")
                (,(code-char 4) . "\\mwedge{}")
                (,(code-char 19) . "\\mcup{}")
                (,(code-char 16) . "\\msubset{}")
                (,(code-char 20) . "\\mforall{}")
                (,(code-char 31) . "\\mvee{}")
                (,(code-char 17) . "\\msupset{}")
                (,(code-char 2) . "\\malpha{}")
                (,(code-char 3) . "\\mbeta{}")
                (,(code-char 10) . "\\mdelta{}")
                (,(code-char 6) . "\\mepsilon{}")
                (,(code-char 9) . "\\mgamma{}")
                (,(code-char 8) . "\\mlambda{}")
                (,(code-char 7) . "\\mpi{}")
                (,(code-char 28) . "\\mleq{}")
                (,(code-char 29) . "\\mgeq{}")
                (,(code-char 127) . "\\mint{}")
                (,(code-char 0) . "\\mcdot{}")
                (,(code-char 5) . "\\mneg{}")
                (,(code-char 26) . "\\mneq{}")
                (,(code-char 30) . "\\mequiv{}")
                (,(code-char 12) . "\\mpm{}")
                (,(code-char 13) . "\\moplus{}")
                (,(code-char 22) . "\\motimes{}")
                (,(code-char 27) . "\\mdiamond{}"))
              #-symbolics
              `((,(code-char 127) . "\\mint{}")         ;; symbolics 127
                (,(code-char 142) . "\\mcdot{}")        ;; symbolics 0
                (,(code-char 143) . "\\mdownarrow{}")   ;; symbolics 1
                (,(code-char 144) . "\\malpha{}")       ;; symbolics 2
                (,(code-char 145) . "\\mbeta{}")        ;; symbolics 3
                (,(code-char 146) . "\\mwedge{}")       ;; symbolics 4
                (,(code-char 147) . "\\mneg{}")         ;; symbolics 5
                (,(code-char 148) . "\\mepsilon{}")     ;; symbolics 6
                (,(code-char 149) . "\\mpi{}")          ;; symbolics 7
                (,(code-char 150) . "\\mlambda{}")      ;; symbolics 8
                (,(code-char 151) . "\\mgamma{}")       ;; symbolics 9
                (,(code-char 152) . "\\mdelta{}")       ;; symbolics 10
                (,(code-char 153) . "\\muparrow{}")     ;; symbolics 11
                (,(code-char 154) . "\\mpm{}")          ;; symbolics 12
                (,(code-char 155) . "\\moplus{}")       ;; symbolics 13
                (,(code-char 156) . "\\minfty{}")       ;; symbolics 14
                (,(code-char 157) . "\\mpartial{}")     ;; symbolics 15
                (,(code-char 158) . "\\msubset{}")      ;; symbolics 16
                (,(code-char 159) . "\\msupset{}")      ;; symbolics 17
                (,(code-char 160) . "\\mcap{}")         ;; symbolics 18
                (,(code-char 161) . "\\mcup{}")         ;; symbolics 19
                (,(code-char 162) . "\\mforall{}")      ;; symbolics 20
                (,(code-char 163) . "\\mexists{}")      ;; symbolics 21
                (,(code-char 164) . "\\motimes{}")      ;; symbolics 22
                (,(code-char 165) . "\\mrightleftharpoons{}")   ;; symbolics 23
                (,(code-char 166) . "\\mleftarrow{}")   ;; symbolics 24
                (,(code-char 167) . "\\mrightarrow{}")  ;; symbolics 25
                (,(code-char 168) . "\\mneq{}")         ;; symbolics 26
                (,(code-char 169) . "\\mdiamond{}")     ;; symbolics 27
                (,(code-char 170) . "\\mleq{}")         ;; symbolics 28
                (,(code-char 171) . "\\mgeq{}")         ;; symbolics 29
                (,(code-char 172) . "\\mequiv{}")       ;; symbolics 30
                (,(code-char 173) . "\\mvee{}")         ;; symbolics 31
                ))


;; coordinates with *non-standard-graphic-code->latex-macro* to 
;;  map prl internal chars 127,142-173 to a latex macro.
(defun nonstandard-graphic-ichar->latexizable-char (ich)
  #-symbolics
  (code-char ich)
  #+symbolics
  (code-char (unshift-code ich)) )





(defparameter *nonstandard-graphic-ichar->string*
              (mapcar
                #'(lambda (x) (cons (shift-code (car x))
                                    (cdr x)))
                `((18 . "[intersect].")
                  (11 . "[up]")
                  (1 . "[down]")
                  (14 . "[infinity]")
                  (24 . "<-")
                  (25 . "->")
                  (23 . "<->")
                  (21 . "E")
                  (15 . "[di]")
                  (4 . "[wedge]")
                  (19 . "U")
                  (16 . "[subset]")
                  (20 . "A")
                  (31 . "V")
                  (17 . "[supset]")
                  (2 . "[alpha]")
                  (3 . "[beta]")
                  (10 . "[delta]")
                  (6 . "[in]")
                  (9 . "[gamma]")
                  (8 . "\\")
                  (7 . "[pi]")
                  (28 . "<=")
                  (29 . ">=")
                  (127 . "[integral]")
                  (0 . ".")
                  (5 . "-")
                  (26 . "~=")
                  (30 . "==")
                  (12 . "+-")
                  (13 . "[oplus]")
                  (22 . "[otimes]")
                  (27 . "[lozenge]"))))




#+symbolics
(defun ML-top-loop ()
  (format t "~2%Terminate ML forms with ”.  Do not use `;;'.  ‘ to quit.~3%")
  (do () (nil)
    (let* ((input-string
             (scl:prompt-and-read
               '(:delimited-string :delimiter nil
                                   :visible-delimiter nil)
               "ML> ")))
      (terpri)
      (princ (ML-string input-string))))
  (values))

#+symbolics
(scl:define-cp-command
  (com-ml :name "ML"
          :command-table (si:find-comtab "User"))
  (&key)
  (ml-top-loop)
  (values))

;;; If this can't be implemented, then prl won't be able to directly
;;; read (very) old prl library files.  However, there is a conversion
;;; function---see the release notes.
(defmacro with-reader-character-conversion-disabled (&body body)
  #+symbolics
  `(let ((lcase "abcdefghijklmnopqrstuvwxyz"))
     (unwind-protect
         (progn
           (map nil
                #'(lambda (ch) (scl:set-character-translation ch ch))
                lcase)
           ,@body)
       (map nil
            #'(lambda (ch) (scl:set-character-translation ch (char-upcase ch)))
            lcase)))
  #-symbolics
  `(progn ,@body))

;;; NIL if not supported by Lisp.
(defun unix-environment-variable (str)
  nil
  #+(or lcl3.0 lcl4.0) (user::environment-variable str)
  #+ccl (ccl:getenv str)
  #+allegro (system:getenv str))

;;; may return NIL
(defun local-host ()
  (unix-environment-variable "HOST"))

;;; may return NIL.  A flaky function.  Use at your own risk.
(defun X-host ()
  (let ((display (unix-environment-variable "DISPLAY")))
    (when display
      (let ((str (string-right-trim '(#\0 #\. #\:) display)))
	(if (or (string-equal str "unix") (string-equal str ""))
	    (unix-environment-variable "HOST")
	    str)))))

(defconstant *herald-format-string*
"~%


		   The Nuprl Proof Development System
			      Version 3.1


Nuprl 3.1 is the result of a seven year effort involving about a dozen
people.  Funding was provided in large measure by the National Science
Foundation and the Office of Naval Research.  Most participating individuals
influenced many areas of the project, but the primary contributions were:

    Overall conception -- J. Bates, R. Constable
    System architecture and management of the implementation -- J. Bates
    System implementation -- J. Bates, M. Bromley, F. Corrado
                             J. Cremer, T. Knoblock, J. Sasaki
    System extensions -- R. Eaton, T. Griffin, D. Howe, D. Krafft, E. Steeg
    Logic design -- R. Constable, J. Bates, S. Allen, R. Harper, 
                    D. Howe, N. Mendler 
    Release 3.1 preparation -- R. Eaton, D. Howe
    Project support -- D. Isenbarger, E. Maxwell

Nuprl incorporates an ML implementation derived from code developed at the
University of Edinburgh, Cambridge University, and INRIA.  Permission is
granted to use and modify Nuprl 3.1 provided this paragraph is
retained.~4%")

(defun show-prl-herald ()
  (declare (special *nuprl-frame*))
  #+symbolics
  (tv:with-terminal-io-on-typeout-window (*nuprl-frame* t)
    (format t *herald-format-string*))
  #-symbolics
  (format t *herald-format-string*))


;;; Extend the X-server's font path with the directory formed by 
;;; concatenating Nuprl's path prefix, "sys/x-fonts" and the
;;; subdirectory argument.  Lucid and Allegro 
;;; only.  Use only in nuprl-init files.
(defun add-nuprl-font-directory (subdirectory)
  #-(or lucid allegro kcl)
  (error "Error in setting font path: not implemented for this Common Lisp")
  (unless (get-option :host)
     (error "Error in setting font path: the :host option is not set."))
  (add-nuprl-font-directory$
   (concatenate 'string *nuprl-path-prefix* "sys/x-fonts/" subdirectory)))

(defun add-nuprl-font-directory$ (path)
  (let* ((display (concatenate 'string (get-option :host) ":0.0")))
    #+kcl
    (progn (system (concatenate 'string "xset fp+ " path " -display " display))
	   (system (concatenate 'string "xset fp rehash -display " display)))
    #+lucid
    (progn (user::run-program 
	    "xset" 
	    :arguments `("fp+" ,path "-display" ,display))
	   (user::run-program
	    "xset" 
	    :arguments `("fp" "rehash" "-display" ,display)))
    #+ccl
    (progn (ccl:run-program
            "xset"
            `("fp+" ,path "-display" ,display))
           (ccl:run-program
            "xset" 
            `("fp" "rehash" "-display" ,display)))
    #+allegro
    (progn (excl:run-shell-command
	    (concatenate 'string "xset fp+ " path " -display " display))
	   (excl:run-shell-command
	    (concatenate 'string "xset fp rehash -display " display))))
  nil)



