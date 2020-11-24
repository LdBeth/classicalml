;;; -*- Package: Nuprl; Syntax: Common-lisp; Base: 10. -*-

(in-package "NUPRL")


;;; F-descriptor
;;;
;;; Contains the definition of descriptors and various functions for dealing with
;;; them.

;;; The descriptors have the following form:
;;;
;;;    (id 'VALUE name)
;;;
;;;         The identifier id denotes a non function value.  The value is the
;;;         value of name.
;;;
;;;    (id 'FUNCTION name arity fname all-uses-full-appl
;;;                  params tail-recursion-happened)
;;;
;;;         The identifier id denotes an internal function.  The closure is the
;;;         value of name and the associated lisp function is the function value
;;;         of fname (or name if fname is nil).  The lisp function expects arity
;;;         arguments.  The all-uses-full-appl field is t if in every application
;;;         of this function there are arity arguments.  The following two fields
;;;         are for optimizing tail recursion.  The params field is the list of
;;;         parameter names for the function, and tail-recursion-happened is set
;;;         to true during the processing of the body if any tail recursive call
;;;         of this function was optimized.
;;;
;;;    (id 'ML-FUNCTION name arity)
;;;
;;;         The identifier id denotes a global function (ie one defined by let or
;;;         letrec at the top level).  The closure is the value of name, and the
;;;         associated lisp function is the function value of name.  The number
;;;         of arguments expected by the lisp function is given by arity.
;;;
;;;    (id 'PRIM-FUNCTION name arity fname)
;;;
;;;         The identifier id denotes a primitive function.  The closure is the
;;;         value of name and the associated lisp function is the function value
;;;         of fname.  The lisp function expects arity arguments.
;;;
;;;    (id 'ISOM)
;;;         The id is an isomorphism function for an abstract data type.

(defstruct (desc
		 (:type list))
  id
  kind
  name)

(defstruct (value (:include desc (kind 'VALUE)) (:type list))
)

(defstruct (ml-function
	     (:include desc (kind 'ML-FUNCTION))
	     (:type list)
	     (:conc-name function-))
  arity)

(defstruct (prim-function
	     (:include ml-function (kind 'PRIM-FUNCTION))
	     (:type list)
	     (:conc-name function-))
  fname)

(defstruct (function (:include prim-function (kind 'function)) (:type list))
  (all-uses-full-appl t)
  params
  (tail-recursion-happened nil))

(defstruct (isom (:include desc (kind 'ISOM)) (:type list))
)

;;; Some useful access functions for descs

(defun is-ml-function (desc) (eql (desc-kind desc) 'FUNCTION))
(defun is-internal-function (desc)
  (eql (desc-kind desc) 'FUNCTION))
(defun is-function (desc)
  (member (desc-kind desc) '(FUNCTION PRIM-FUNCTION ML-FUNCTION)))
(defun is-isom (desc) (eql (desc-kind desc) 'ISOM))

(defun name-for-desc (desc)
  (desc-name desc))

(defun name-for-function (desc)
  (if (eql (desc-kind desc) 'ML-FUNCTION)
      (desc-name desc)
      (or (function-fname desc) (desc-name desc))))

;;; Some functions to hide the details of constructing descs.

(defun mk-value-desc (id)
  (make-value :id id :name (gen-internal-name id)))

(defun mk-function-desc (id arity)
  (let ((name (gen-internal-name id)))
    (make-function :id id :arity arity :name name :fname name)))

(defun mk-isom-desc (id)
  (make-isom :id id))
