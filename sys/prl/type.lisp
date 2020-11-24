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

(defmacro deftuple (name &rest fields)
  (let ((field-names (mapcar #'(lambda (x) (concat x '-of- name)) fields)))
    `(defstruct (,name
		 (:type list)
		 (:conc-name nil)
		 (:constructor ,name ,field-names))
       ,@field-names)))


(defmacro Pdeftype (name &rest typedef)
  ;; Define a type and bind it to a typename.
  ;;
  ;; Form: (Pdeftype typename struct)
  ;;   1. Syntax check struct according to the following:             
  ;;         struct --> 'array' (-bounds-) struct
  ;;                --> (-name struct-)
  ;;                --> 'type' typename
  ;;                --> 'vector' (length) struct
  ;;                --> 'int-vector' (length)
  ;;                --> 'byte-vector' (length)
  ;;                -->
  ;;   2. Put the value struct on the property list for typename under
  ;;         the indicator 'typedef'
  ;;   3. put the value 'TYPE' under indicator 'type' on the
  ;;         property list for typename. 
  (if (null (extracttype-deftype typedef))
      `(eval-when (eval load compile)
	 (setf (get ',name 'typedef) ',typedef)
	 (setf (get ',name 'type) 'TYPE))
      (error "~a~^ ~a" '|DEFTYPE: Syntax error.|)))

(defun extracttype-deftype (defn)
  ;;  Returns the suffix of defn after a valid type has been  extracted
  ;;  from the front.
  (cond ((null defn) nil)
	((atom (car defn))
	 (case (car defn)
	   (type
	    (unless (and (not (null (cdr defn))) (atom (cadr defn)))
	      (error "~a~^ ~a" '|DEFTYPE: A typename must follow TYPE.| defn))
	    (cddr defn))
	   (array
	    (unless (and (not (null (cdr defn)))
			 (numberlistp-deftype (mapcar 'eval (cadr defn))))
	      (error "~a~^ ~a" '|DEFTYPE: Array bounds must be list of nums.| defn))
	    (extracttype-deftype (cddr defn)))
	   ((vector int-vector byte-vector)
	    (unless (and (= (length (cadr defn)) 1)
			 (numberlistp-deftype (mapcar 'eval (cadr defn))))
	      (error "~a~^ ~a" '|DEFTYPE: Vector length must be list of 1 number| defn))
	    (if (eql (car defn) 'vector)
		(extracttype-deftype (cddr defn))
		(cddr defn)))
	   (otherwise
	    defn)))
	(t
	 ;; It must be a record.
	 (do ((remlist (car defn)))
	     ((null remlist) (cdr defn))
	   (when (not (atom (car remlist)))
	     (error "~a~^ ~a" '|DEFTYPE: A record must be a list of name - type pairs.|))
	   (setf remlist (extracttype-deftype (cdr remlist)))))))

(defun numberlistp-deftype (lis)
  (every #'numberp lis))


(defmacro new (type)
    ;
    ;  Form:  (new typename)
    ;
    ;  Create a new object of type typename, where typename has been
    ;   defined previously by 'deftype'.  The new object created is the
    ;   result returned by the 'new' function.
    ;
  (unless (eql (get type 'type) 'TYPE)
      (error "~a~^ ~a" '|NEW: Typename must be defined in a DEFTYPE.| type))
  `(newstruct-new ',(get type 'typedef)))

(defun newstruct-new (struct)
  (cond ((null struct) nil)
	((atom (car struct))
	 (case (car struct)
	   (type
	    (if (eql (get (cadr struct) 'type) 'TYPE)
		(newstruct-new (get (cadr struct) 'typedef))
		(error "~a~^ ~a" '|NEW: TYPE is not followed by proper typename.| (cadr struct))))
	   (array
	    (let* ((bounds (mapcar 'eval (cadr struct)))
		   (array (make-array bounds)))
	      (initarray-new array bounds (cddr struct))
	      array))
	   (vector
	    (let* ((size (eval (caadr struct)))
		   (vec (make-array size)))
	      (initvector-new vec size (cddr struct))
	      vec))
	   (int-vector
	    (make-array (eval (caadr struct))))
	   (byte-vector
	    (make-array (eval (caadr struct)) :element-type '(unsigned-byte 8)))))
	(t (do ((record nil)
		(remlist (car struct)))
	       ((null remlist)
	        (make-array (length record) :initial-contents (nreverse record)))
	     (push (newstruct-new (cdr remlist)) record)
	     (setf remlist (extracttype-deftype (cdr remlist)))))))

(defun initarray-new (array bounds struct)
  (declare (ignore bounds))
  ;; Initialize the elements of the array to (new struct).
  (let* ((length (array-total-size array) )
	 (indirect (make-array length :displaced-to array)))
    (dotimes (i length)
      (setf (aref indirect i) (newstruct-new struct)))))

(defun initvector-new (vector size struct)
  (dotimes (i size)
    (setf (aref vector i) (newstruct-new struct))))


(defmacro sel (thing &rest selectexpr)
  ;;  Form:  A) (sel variable selectexpr)
  ;;   or    B) (sel (typename expr) selectexpr)
  ;;      where
  ;;         selectexpr --> fieldname selectexpr
  ;;                   --> (- array-index -)
  ;;                    --> vector-index
  ;;                    -->
  ;;
  ;;  This macro generates the code necessary to select any field from a
  ;;  variable (or expr) of type typename, where typename is defined in
  ;;  a DEFTYPE macro.
  ;;
  ;;  If form A, verify that the variable was declared in a GLOBAL macro
  ;;  and get its type from its property list.  If form B, verify that
  ;;  the typename has been defined in a DEFTYPE macro.  Then call
  ;;  SELEXP to build an expression which when evaluated will return the
  ;;  value of the selected field.
  (if (and (not (null thing)) (atom thing))
      ;; a simple variable
      (progn
	(when (null (get thing 'type))
	  (error "~a~^ ~a" '|SEL: Variable not declared in a GLOBAL.| thing))
	(selexp-sel thing selectexpr (get (get thing 'type) 'typedef)))
      ;; explicitly typed (form B)
      (let ((typename (first thing))
	    (expr (second thing)))
          (when (neq (get typename 'type) 'TYPE)
              (error "~a~^ ~a" '|SEL: Typename not specified in a DEFTYPE| typename ))
	  (selexp-sel expr selectexpr (get typename 'typedef)))))

(defun selexp-sel (varexpr sellist typestruct)
  ;;  Given varexpr, an expression whose type is represented by
  ;;  typestruct (defined by DEFTYPE), and sellist, a list of fieldnames
  ;;  and array subscript selectors, return the expression which when
  ;;  evaluated will yield the selected component of the varexpr.
  (do ((selexpr varexpr))
      ((null sellist) selexpr)
    ;; Check for type keyword at the front of the typestruct and merge the type
    ;; definition back into typestruct.
    (do ()
	((not (and (not (null (car typestruct)))
		   (atom (car typestruct))
		   (eql (car typestruct) 'type))))
      (when (neq (get (cadr typestruct) 'type) 'TYPE)
	(error "~a~^ ~a" '|SEL: Type not defined in a DEFTYPE.| (cadr typestruct)))
      (setf typestruct
	    (append (get (cadr typestruct) 'typedef) (cddr typestruct))))
    (cond ((atom (car sellist))
	   ;; A field reference.
	   (when (atom (car typestruct))
	     (error "~a~^ ~a" '|SEL: Not a field name of a record.| (car sellist)))
	   (setf typestruct (car typestruct))
	   (unless (member (car sellist) typestruct)
	     (error "~a~^ ~a" '|SEL: Not a fieldname in type specified.| (car sellist)))
	   ;; Build the correct selector for the field and prepend it to
	   ;; selector.
	   (do ((n 0 (1+ n)))
	       ((eql (car sellist) (car typestruct))
		(pop typestruct)
		(setf selexpr `(aref ,selexpr ,n)))
	     (setf typestruct (extracttype-deftype (cdr typestruct)))))
	  ((member (car typestruct) '(array vector int-vector byte-vector))
	   ;;  An array (vector) subscripting.
	   (unless (= (length (car sellist)) (length (cadr typestruct)))
	     (error "~a~^ ~a" '|SEL: Improper array subscripting.| (car sellist)))
	   (setq selexpr `(aref ,selexpr ,@(car sellist))
		 typestruct (cddr typestruct)))
	  (t (error "~a~^ ~a" '|SEL: Untimely subscripting.| (car sellist))))
    (pop sellist)))


(defmacro fluid (var)
  ;  Declare a variable to have a fluid binding (for the compiler).
  ;   
  ;   Form:   (fluid variable)
  `(defvar ,var))

(defmacro global (var &optional type)
     ; 
     ;  Declare a variable to be global and possibly of a specific type.
     ;   
     ;   Form:   (global variable typename)
     ;        where typename (if specified) is defined by a 'deftype' macro.
  (if (null type)
      `(defvar ,var)
      `(eval-when (load compile eval)
	 (setf (get ',var 'type) ',type)
	 (defvar ,var))))

(defmacro constant (name value)
  `(eval-when (compile eval load)
     (defvar ,name)
     (setq ,name ,value)))
