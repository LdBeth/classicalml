;;; Some of the customizations in this file may not work in some Common
;;; Lisps or with some machine configurations.


(in-package "NUPRL") ; initializations use functions in the Nuprl package.


;;; Use a nice font from Nuprl's font directory.  Lucid, Sun and Allegro
;;; Common Lisp only.  The :host option must be set at this
;;; point.  This can be done either by using change-options earlier in
;;; this file, or by giving a host argument to the function "nuprl" that
;;; invokes Nuprl.  The string "sun-mit" below may need to be replaced by the 
;;; the name of the subdirectory of "nuprl/sys/x-fonts" that
;;; contains the version of the fonts for your particular X window
;;; server.  
;;; To give a full pathname, use add-nuprl-font-directory$.
;;; See the document installing-nuprl for some details on Nuprl's fonts.
#+(or allegro lucid)
(progn
  (add-nuprl-font-directory "sun-mit")
  (change-options :font-name "fg-13"))


;;; Immediately hog a big chunk of virtual memory to reduce the number
;;; of garbage collections.  (Lucid only.)
#+lucid
(user::change-memory-management :growth-limit 1500 :expand 400)


;;; Enable mouse-pointer warping, so that Nuprl retains input focus
;;; when windows are closed (if input focus is determined by pointer 
;;; location).
(change-options :no-warp? nil)


;;; Add a new key binding: ctrl-' ---> `
(define-key-binding :control #\' (ichar #\`))


;;; Define a function in the Nuprl package to quit Lisp (Lucid only)
#+lucid
(defun quit () (user::quit))
