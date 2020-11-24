;;; -*- Syntax: Common-Lisp; Package: (nuprl lisp); Base: 10 -*-

(unless (find-package "NUPRL")
  (make-package "NUPRL" :use '("LISP")))

(in-package "NUPRL")  


(defparameter *lisp-file-extension* "lisp")

;;; -----------------------------------------------------------------------
;;; SITE-DEPENDENT DEFINITIONS.
;;; The following 2 parameter definitions may need to be changed,
;;; depending on the Common Lisp used and the name of Nuprl's main
;;; directory.  The third definition may also be changed if desired: replace 
;;; "nuprl-init" by the desired name of the init file.

;;; The filename extension added to compiled Lisp files.
(defparameter *bin-file-extension* "sbin")

;;; Nuprl's home directory.  Note the trailing "/" in the Unix pathname.
(defparameter *nuprl-path-prefix* 
    #+symbolics "nuprl:" 
    ;;; change the string below to the root directory for Nuprl
    #+(or unix mach) "/usr/fsys/nori/a/nuprl/")  ;change this string

;;; The name of Nuprl's init file is *init-file-name* followed by ".lisp"
(defparameter *init-file-name*
              (concatenate 'string "nuprl-init" "." *lisp-file-extension*))

;;; -----------------------------------------------------------------------


#-3600
(unless (find-package "ML-RUNTIME")
  (make-package "ML-RUNTIME" :nicknames '("mlr") :use '("LISP")))

#+3600
(scl:defpackage ml-runtime
  (:use)
  (:colon-mode :internal)   ; This is a gross hack.   See the ML section
			    ; of nuprl:doc;known-bugs for a description
 			    ; of the problem this "fixes".
  (:nicknames mlr))

#+lucid
(proclaim '(optimize (safety 3) (speed 3) (compilation-speed 0)))

#+allegro
(proclaim '(optimize (safety 3) (speed 3)))

;;; copy-seq is the name of the structure for the ML "sequence"
;;; expression.  trap is the structure for ML trap expressions.
;;; substitute is term substitution.
(shadow '(copy-seq substitute trap function))

(defvar *do-initializations?* t)

(when (and (find-package 'xlib) (not (member :xlib *features*)))
  (push :xlib *features*))

(when (and (find-package 'windows) (not (member :windows *features*)))
  (push :windows *features*))

#-(or symbolics xlib (and sun windows))
(format t "~2%*** Nuprl requires CLX or SunView or Symbolics windows. ***~2%")

;;; complete-nuprl-path takes a list of symbols representing directory
;;; names and symbol representing a file name and produces a symbol
;;; representing the "completion" of the pathname.  It allows one to
;;; write relatively host-independent ML "scripts" for loading
;;; collections of ML files.  For unix (or mach) hosts, the new path is relative
;;; to lisp's working directory, which is assumed to be the root of the
;;; nuprl subtree of the file system (usual "nuprl").  On a Symbolics,
;;; the completion of ("x","y"), "foo" is the logical pathname
;;; "nuprl:x;y;foo".  The path prefix is settable from ML using
;;; set_nuprl_path_prefix.  The ML version of this function is
;;; complete_nuprl_path.
(defun complete-nuprl-path (directories file)  
  #+(or symbolics unix mach)
  (flet ((add-separator (x) (concatenate 'string x #+symbolics ";" #+(or unix mach) "/")))
    (reduce #'(lambda (x y) (concatenate 'string x y))
	    `(,*nuprl-path-prefix*
	      ,@(mapcar #'add-separator (mapcar #'string directories))
	      ,(string file))))
  #-(or symbolics unix mach)
  file)

#+symbolics
(user::defsystem Nuprl
    (:pretty-name "Nuprl Proof Development System"
     :short-name "Nuprl"
     :default-package nuprl
     :default-pathname "nuprl:sys;"
     :advertised-in (:herald :finger)
     :bug-reports (:mailing-list "nuprlbugs")
     :before-patches-initializations
     (when *do-initializations?*
       (unwind-protect
	   (progn (initialize)
		  (format t
			  "~2%Loading tactics.  This will take a while if the tactic files~%~
                         are uncompiled.  If you abort now (c-ABORT) you can run Nuprl~%~
                         without tactics.")
		  (ml-load nil (complete-nuprl-path '(|ml|) '|load|)))
	 (setf *do-initializations?* nil)
	 (establish-initial-state)
	 (format t
		 "~2%To invoke Nuprl, use the `Nuprl' command.  ~%~
                To return to Nuprl, use SELECT U.~2%"))))

  (:module nuprlsys (nuprlsys) (:type :system))

  (:module mlbase (mlbase) (:type :system)
	   (:uses-definitions-from nuprlsys))
  (:module mlsys (mlsys) (:type :system)
	   (:uses-definitions-from mlbase)
	   (:in-order-to (:compile) (:load nuprlsys)))
  (:module mlprl (mlprl) (:type :system)
	   (:uses-definitions-from mlbase)
	   (:in-order-to (:compile) (:load nuprlsys))))

#+symbolics
(user::defsubsystem nuprlsys
    (:default-pathname "nuprl:sys;prl;")
  (:serial
    "basic"
    "dependent"
    "lispm-win" 
    (:definitions "control"		  ; control, type, and vector have no 
     (:definitions "type"		  ; interdependencies.
      (:definitions "vector"			
       (:definitions "data-defs"
	(:parallel
	  ;; scanning and parsing
	  (:definitions "scan-defs"	  ; neither do scan-defs and 
	   (:definitions "action-buf"	  ; action-buf.
	    (:parallel "scan" "ttree-gen" "best-ttree" "ttree-maint"
		       "parse" "defn" "parse-goal")))
	  ;; rules
	  (:definitions "rule-defs"
	   (:serial
	     "ref"
	     "ref-support"
	     (:parallel "ruleparser" "parse-eq" "parse-comp"
			"extract" "disp-rule"
			"rules" "rules-elim" "rules-intro"
			"rules-eq1" "rules-eq2" "tactic" "monot-aux"
			"monot" "division" "rules-comp")))
	  ;; decision procedures
	  (:parallel "arith" "simplify" "equality")
	  ;; miscellaneous
	  (:parallel "prl" "eval" "theorem-obj")
	  ;; editors-and-display
	  (:serial
	    "red-defs"
	    (:definitions "disp-defs"
	     (:parallel "red-status" "lib" "red" "ted" "disp-Ttree"
			"disp-proof"))))))))))

#+symbolics
(user::defsubsystem mlbase
    (:default-pathname "nuprl:sys;ml;")
  (:definitions "f-lispm"
   (:parallel "f-macro" "dolists" "descriptor" "node-defs" "runtime-defs")))

#+symbolics
(user::defsubsystem mlsys
    (:default-pathname "nuprl:sys;ml;")
  (:parallel "f-gp" "f-parser" "f-parsml" "f-mlprin" "f-typeml" "f-dml" 
	     "f-format" "f-writml" "f-tml" "f-lis" "f-obj"
	     "compiler" "convert" "runtime" "translate"))

#+symbolics
(user::defsubsystem mlprl
    (:default-pathname "nuprl:sys;ml;")
  (:parallel "f-iox-prl" "ml-refine" "ml-rule" "ml-term"
	     "ml-prl" "primitives" "io" "new-rules"))

(defparameter *nuprl-files*
	      '((("sys" "prl") . "basic")
		(("sys" "prl") . "dependent")
		#+xlib (("sys" "prl") . "x-win")
		#+symbolics (("sys" "prl") . "lispm-win")
		#+(and sun windows (not xlib)) (("sys" "prl") . "sun-win")
		(("sys" "prl") . "control")
		(("sys" "prl") . "type")
		(("sys" "prl") . "vector")

		(("sys" "prl") . "data-defs")
		(("sys" "prl") . "scan-defs")
		(("sys" "prl") . "action-buf")
		(("sys" "prl") . "scan")
		(("sys" "prl") . "ttree-gen")
		(("sys" "prl") . "best-ttree")
		(("sys" "prl") . "ttree-maint")
		(("sys" "prl") . "parse")
		(("sys" "prl") . "defn")
		(("sys" "prl") . "parse-goal")

		(("sys" "prl") . "rule-defs")
		(("sys" "prl") . "ref")
		(("sys" "prl") . "ref-support")
		(("sys" "prl") . "ruleparser")
		(("sys" "prl") . "parse-eq")
		(("sys" "prl") . "parse-comp")
		(("sys" "prl") . "extract")
		(("sys" "prl") . "disp-rule")
		(("sys" "prl") . "rules")
		(("sys" "prl") . "rules-elim")
		(("sys" "prl") . "rules-intro")
		(("sys" "prl") . "rules-eq1")
		(("sys" "prl") . "rules-eq2")
		(("sys" "prl") . "tactic")
		(("sys" "prl") . "monot-aux")
		(("sys" "prl") . "monot")
		(("sys" "prl") . "division")
		(("sys" "prl") . "rules-comp")

		(("sys" "prl") . "arith")
		(("sys" "prl") . "simplify")
		(("sys" "prl") . "equality")

		(("sys" "prl") . "prl")
		(("sys" "prl") . "eval")
		(("sys" "prl") . "theorem-obj")

		(("sys" "prl") . "red-defs")
		(("sys" "prl") . "disp-defs")
		(("sys" "prl") . "red-status")
		(("sys" "prl") . "lib")
		(("sys" "prl") . "red")
		(("sys" "prl") . "ted")
		(("sys" "prl") . "disp-ttree")
		(("sys" "prl") . "disp-proof")

		(("sys" "ml") . "f-lispm")
		(("sys" "ml") . "f-macro")
		(("sys" "ml") . "dolists")
		(("sys" "ml") . "descriptor")
		(("sys" "ml") . "node-defs")
		(("sys" "ml") . "runtime-defs")
		(("sys" "ml") . "f-gp")
		(("sys" "ml") . "f-parser")
		(("sys" "ml") . "f-parsml")
		(("sys" "ml") . "f-mlprin")
		(("sys" "ml") . "f-typeml")
		(("sys" "ml") . "f-dml")
		(("sys" "ml") . "f-format")
		(("sys" "ml") . "f-writml")
		(("sys" "ml") . "f-tml")
		(("sys" "ml") . "f-lis")
		(("sys" "ml") . "f-obj")
		(("sys" "ml") . "compiler")
		(("sys" "ml") . "convert")
		(("sys" "ml") . "runtime")
		(("sys" "ml") . "translate")
		(("sys" "ml") . "f-iox-prl")
		(("sys" "ml") . "ml-refine")
		(("sys" "ml") . "ml-rule")
		(("sys" "ml") . "ml-term")
		(("sys" "ml") . "ml-prl")
		(("sys" "ml") . "primitives")
		(("sys" "ml") . "io")

		(("sys" "ml") . "new-rules")))

(defun load-nuprl-file (file)
  (load (complete-nuprl-path (car file) (cdr file))))

(defun compile-nuprl-file (file &optional (always? t) (and-load? t))
  (let* ((dirs (car file))
	 (name (cdr file))
	 (source (complete-nuprl-path dirs (concatenate 'string
							name "." *lisp-file-extension*)))
	 (binary (complete-nuprl-path dirs (concatenate 'string
							name "." *bin-file-extension*))))
    (when (or always?
	      (not (probe-file binary))
	      (> (file-write-date source)
		 (file-write-date binary)))
      #+lucid (compile-file source :messages nil)	
      #-lucid (compile-file source)
      (when and-load? (load-nuprl-file file)))))

(defun compile-nuprl (&optional (compile-tactics? t))
  (dolist (file *nuprl-files*)
    (compile-nuprl-file file))
  (unwind-protect
      (progn (initialize)
	     (when compile-tactics?
	       (format t
		       "~2%Compiling tactics.  This will take a while.  If you abort now~%~
                        you can run Nuprl without tactics.")
	       (ml-load nil (complete-nuprl-path '(|ml|) '|compile|))))
    (setf *do-initializations?* nil)
    (establish-initial-state)
    (format t #+xlib "~2%To invoke Nuprl evaluate (nuprl \"<host-name>\")~2%"
	      #-xlib "~2%To invoke Nuprl evaluate (nuprl)~2%")))

;;; assumes the system is already loaded.
(defun incrementally-compile-nuprl ()
  (format t "~2%Ignoring ML code files.~%")
  (dolist (file *nuprl-files*)
    (compile-nuprl-file file nil)))

(defun load-nuprl (&optional (load-tactics? t) (compile-newer-sources? nil)) 
  (dolist (file *nuprl-files*)
    (when compile-newer-sources? (compile-nuprl-file file nil nil))
    (load-nuprl-file file))
  (unwind-protect
      (progn (initialize)
	     (when load-tactics?
	       (format t
		       "~2%Loading tactics.  This will take a while if the tactic files~%~
                        are uncompiled.  If you abort now you can run Nuprl without tactics.")
	       (ml-load nil (complete-nuprl-path '(|ml|) '|load|))))
    (setf *do-initializations?* nil)
    (establish-initial-state)
    (format t #+xlib "~2%To invoke Nuprl evaluate (nuprl \"<host-name>\")~2%"
	      #-xlib "~2%To invoke Nuprl evaluate (nuprl)~2%")))

#-symbolics
(format t 
	"~2%To compile (or load) Nuprl, first evaluate (in-package \"NUPRL\"), then~%~
          evaluate (compile-nuprl) (or (load-nuprl)).  This will also compile (load)~%~
          the tactic collection; to skip this, give nil as an argument.~2%")
