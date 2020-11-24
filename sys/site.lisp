(in-package "NUPRL")


(defparameter *lisp-file-extension* "lisp")

;;; -----------------------------------------------------------------------
;;; SITE-DEPENDENT DEFINITIONS.
;;; The following 2 parameter definitions may need to be changed,
;;; depending on the Common Lisp used and the name of Nuprl's main
;;; directory.  The third definition may also be changed if desired: replace 
;;; "nuprl-init" by the desired name of the init file.

;;; The filename extension added to compiled Lisp files.
(defparameter *bin-file-extension*
  #+ccl
  (pathname-type ccl:*.fasl-pathname*))

;;; Nuprl's home directory.  Note the trailing "/" in the Unix pathname.
(defparameter *nuprl-path-prefix*
  #+symbolics "nuprl:" 
    ;;; change the string below to the root directory for Nuprl
  #+(or unix mach) "/usr/fsys/nori/a/nuprl/")  ;change this string

;;; The name of Nuprl's init file is *init-file-name* followed by ".lisp"
(defparameter *init-file-name*
  (make-pathname :name "nuprl-init" :type *lisp-file-extension*))

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
    (reduce #'(lambda (x y) (merge-pathnames y x))
	    `(,*nuprl-path-prefix*
	      ,@(mapcar #'add-separator (mapcar #'string directories))
	      ,(string file))))
  #-(or symbolics unix mach)
  file)
