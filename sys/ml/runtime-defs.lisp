;;; -*- Syntax: Common-lisp; Base: 10.; Package: Nuprl -*-

(in-package "NUPRL")

;;; Macro definitions needed for the runtime system.
;;;
(defun make-closure (f arity &rest args)
  (cons (cons f arity) (copy-list args)))

(defmacro update-closure (closure &rest args)
  (let ((cname (gensym)))
    `(let ((,cname ,closure))
       (list* (first ,cname) ,@args (cdr ,cname)))))

