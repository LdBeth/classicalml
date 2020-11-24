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


;**************************************************************************
;*                                                                        *
;*      Projet     Formel                       LCF    Project            *
;*                                                                        *
;**************************************************************************
;*                                                                        *
;*            Inria                         University of Cambridge       *
;*      Domaine de Voluceau                   Computer Laboratory         *
;*      78150  Rocquencourt                    Cambridge CB2 3QG          *
;*            France                                England               *
;*                                                                        *
;**************************************************************************

; F-macro       Macros for the LCF system

(eval-when (compile load eval)
    ; expand a function call
    ;   #'f   --->    (f arg1 ... argn)
    ;   others      --->    (funcall fun arg1 ... argn)
    (defun call-fun (fun args)
      (cond ((or (atom fun) (not (member (car fun) '(function quote))))
             `(funcall ,fun ,@args))
            (t `(,(cadr fun) ,@args)))) ; call-fun


)   ; eval-when


; Print a constant string, computing length at compile-time
(defmacro ptoken (str)
  `(pstringlen (quote ,str) ,(length (princ-to-string str))))


(defmacro failwith (tok) `(breakout evaluation ,tok))


; fail with appended error message
(defmacro msg-failwith (tok . msgs)
   `(breakout evaluation (concat ,tok " -- " . ,msgs))
)                               ; msg-failwith


; fail if any of the error messages are not nil
(defmacro cond-failwith (tok . code)
    `(let ((msg (or . ,code)))
        (cond (msg (breakout evaluation (concat ,tok " -- " msg)))))
)                               ; cond-failwith

; Lisp error trapping 
(defmacro errortrap (errorfun . trycode)
   (let ((x (gen-temp-name)))
      `((lambda (,x)
           (cond ((atom ,x) ,(call-fun errorfun (list x)))
                 (t (car ,x))))
        (catch-error (progn . ,trycode))))
)               ; errortrap



; Apply the function to successive list elements
; and return the first non-nil value
; if none, return nil
(defmacro exists (fun . lists)
  (let ((vars (mapcar #'(lambda (ignore) (gen-temp-name)) lists)))
   (let ((inits (mapcar #'(lambda (v l) `(,v ,l (cdr ,v))) vars lists))
         (args (mapcar #'(lambda (v) `(car ,v)) vars)))
    `(do ,inits ((null ,(car vars)) nil)
          (cond (,(call-fun fun args) (return (list ,@args)))))))
)   ; exists



(defmacro forall (fun . lists)
  (let ((vars (mapcar #'(lambda (ignore) (gen-temp-name)) lists)))
   (let ((inits (mapcar #'(lambda (v l) `(,v ,l (cdr ,v))) vars lists))
         (args (mapcar #'(lambda (v) `(car ,v)) vars)))
    `(do ,inits ((null ,(car vars)) t)
          (cond (,(call-fun fun args)) ((return nil))))))
)   ; forall

(defmacro defmlfun (name args type &body body)
  (let ((arity (length args))
	ml-name
	lisp-name)
    (if (symbolp name)
	(setf ml-name (setf lisp-name name))
	(setq ml-name (first name) lisp-name (second name)))
    `(progn
       (defun ,lisp-name ,(reverse args) ,@body)
       (declare-ml-fun ',ml-name ,arity ',lisp-name ',type))))

(defmacro defmlsubst (name args type &body body)
  (let ((arity (length args))
	ml-name
	lisp-name)
    (if (symbolp name)
	(setf ml-name (setf lisp-name name))
	(setq ml-name (first name) lisp-name (second name)))
    `(progn
       (defun ,lisp-name ,(reverse args) ,@body)
       (declare-ml-fun ',ml-name ,arity ',lisp-name ',type))))

(defmacro dml (ml-fn n lisp-fn mty)
  `(declare-ml-fun ',ml-fn ',n ',lisp-fn ',mty))

(defmacro dmlc (id exp mty)
    `(declare-ml-const (quote ,id) (quote ,exp) (quote ,mty)))

;; Some of these functions are used at macro expansion time so must be present here.
(defvar *temp-symbol-counter* 0)

(defun gen-temp-name (&optional prefix)
  ;; Returns a symbol whose print name includes the print name of prefix if
  ;; provided.
  ;; The type of symbol returned by this function depends on the way ml
  ;; compilation is handled.  If the intermediate lisp code is written out to a
  ;; file then the symbol must be interned.  If not, then gensym suffices.
  (when (and prefix (symbolp prefix))
    (setf prefix (symbol-name prefix)))
  (make-symbol (concatenate 'string (if (null prefix) "ml-" prefix)
			      (format nil "~D" (incf *temp-symbol-counter*)))))

(defun gen-internal-name (name)
  (when (symbolp name) (setf name (symbol-name name)))
  (make-symbol name))

(defvar *timestamp* (format nil "~D" (mod (clock) 10000)))
(defvar *external-symbol-counter* (mod (clock) 127))

(defun gen-external-name (name)
  (when (symbolp name) (setf name (symbol-name name)))
  (intern (concatenate 'string name "%" (string *timestamp*) "%"
			 (format nil "~D" (incf *external-symbol-counter*)))
	  'ml-runtime))

(defun gen-runtime-name (name)
  (when (symbolp name) (setf name (symbol-name name)))
  (intern name 'ml-runtime))
