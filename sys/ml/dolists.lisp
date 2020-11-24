;;; -*- Syntax: Common-lisp; Base: 10.; Package: Nuprl-*-

(in-package "NUPRL")

(defmacro prllambda (parameters &body body)
  `#'(lambda ,parameters ,@body))

(defmacro dolists (iterators declarations value &body body)
  ;; A call to dolists is of the form
  ;;
  ;;  (dolists ((vari listi)*)
  ;;           (declaration*)
  ;;           result-form
  ;;     body)
  ;;
  ;; This expands into a do form, which iterates over each of the lists, with
  ;; vari being bound to successive elements of listi.  The auxiliary
  ;; declarations are simply added to the declaration list of the resulting do,
  ;; ie they can be anything acceptable as a do declaration.  The forms in body
  ;; are evaluated at each iteration.  The iteration is terminated when the end
  ;; of any of the listi is reached.  The result is the result of evaluating
  ;; result-form.
  (when (not (every (prllambda (x) (and (consp x) (= (length x) 2) (symbolp (first x))))
		  iterators))
    (error "Incorrect iterator list for dolists ~A" iterators))
  (let* ((list-names (mapcar (prllambda (ignore) (gensym)) iterators))
	 (var-names (mapcar #'first iterators))
	 (list-initializers (mapcar (prllambda (name iterator) `(,name ,(second iterator)))
				    list-names
				    iterators))
	 (list-declarations (mapcar (prllambda (name) `(,name (cdr ,name) (cdr ,name)))
				    list-names))
	 (var-declarations (mapcar (prllambda (var-name list-name)
				     `(,var-name (car ,list-name) (car ,list-name)))
				   var-names
				   list-names))
	 (end-test `(not (and ,@list-names)))
	 (end-test-result-name (gensym)))
    `(let ,list-initializers
       (do ,(nconc
	      var-declarations
	      list-declarations
	      (list (list end-test-result-name end-test end-test))
	      ;; This must come last to avoid problems with destructive modification.
	      declarations)
	   (,end-test-result-name ,value)
	 ,@body))))

(defmacro hack-list (function list)
  (let ((var (gensym)))
    `(do ((,var ,list (cdr ,var)))
	 ((null ,var))
       (setf (car ,var) (funcall ,function (car ,var))))))
