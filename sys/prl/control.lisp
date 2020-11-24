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

; 
;  P L E T  --  Form: (Plet (-atom exp1-) -exp2-)
;
;            Evaluates a list of expressions (-exp2-) after local
;            bindings have been established.
  
(defmacro Plet (bindings &body body)
  (let1-let bindings body))

(defun let1-let (l body)
  (do ((vars nil (cons (car l) vars))
       (vals nil (cons (cadr l) vals))
       (l l (cddr l)))
      ((null l) `((lambda ,vars ,@body) ,@vals))))

;
;  V E C T O R   T Y P E  manipulating operations
;
;           (fill-vector vector-name index count value)
;
;               Set count successive cells of vector-name, starting
;               at index, to the integer value (0..255).
;
;           (put-vector vector-name index count)
;
;               Print count successive cells of the vector (starting
;               at index) on the std output.
;

(defun fillbyte-vector (vector index count value)
         (fill-byte-vector vector index count value))

(defmacro <- (ref val)
  (setf val (subst ref '*-* val))
  `(setf ,ref ,val))


;
;   F O R  --  Form:  (for -(variable in list)- 
;                          (when exp1)
;                          (do | save | filter | splice exp2)  )
;

(defmacro for (&body l)
  (let ((vars (vars-for l))
	(args (args-for l))
	(test (test-for l))
	(type (type-for l))
	(body (body-for l)))
    (cons (make-mapfn-for vars test type body)
	  (cons `#',(make-lambda-for 
		     vars vars
		     (add-test-for test
				   (make-body-for vars test type body)))
		args))))
  
(defun type-for (l)
  (let ((item (item-for '(do save splice filter) l)))
    (if item (car item) (error "~a~^ ~a" "No body in for loop"))))

(defun vars-for (m)
  (mapcan #'(lambda (x) (cond ((is-var-form x) (list (var-var-form x))))) m))

(defun args-for (n)
  (mapcan #'(lambda (x) (cond ((is-var-form x) (list (args-var-form x))))) n))

(defun is-var-form (x)
  (and (not (atom x))(equal (length x) 3) (eql (cadr x) 'in)))

(defun var-var-form (x) (car x))

(defun args-var-form (x) (caddr x))

(defun test-for (o)
  (let ((item (item-for '(when) o)))
    (cond (item (cadr item)))))

(defun body-for (p)
  (let ((item (item-for '(do save splice filter) p)))
    (cond ((not item) (error "~a~^ ~a" '"No body in for loop"))
	  ((equal (length (cdr item)) 1) (cadr item))
	  ((cons 'progn (cdr item))))))
  
(defun item-for (keywords l)
  (do ((item (assoc (car keywords) (cdr l)) (assoc (car remlist) (cdr l)))
       (remlist keywords (cdr remlist)))
      ((or item (null remlist)) item)))

(defun make-mapfn-for (vars test type body)
  (cond ((equal type 'do) 'mapc)
	((not (equal type 'save)) 'mapcan)
	((null test) 'mapcar)
        ((subset-test-for vars body) 'remove-if-not)
	(t 'mapcan)))
  
(defun subset-test-for (vars body)
  (and (not (atom vars)) (equal (length vars) 1) (equal (car vars) body)))
  
(defun make-body-for (vars test type body)
  (let ((var (gensym)))
    (cond ((equal type 'filter)
	   `(let ((,var ,body)) (cond (,var (list ,var)))))
	  ((or (not (equal type 'save)) (null test)) body)
	  ((subset-test-for vars body) nil)
	  (t (list 'list body)))))
  
(defun add-test-for (test body)
  (cond ((null test) body)
	((null body) test)
	(t `(cond ,(if (eql (car body) 'progn)
		       (cons test (cdr body))
		       (list test body))))))
  
(defun make-lambda-for (var vars body)
  (cond ((equal var (cdr body)) (car body))
	((eql (car body) 'progn) (cons 'lambda (cons vars (cdr body))))
	((list 'lambda vars body))))

 
;
;  S O M E  --  Form: (Psome function list)
;                   Applies function to successive elements of list,
;                   until one of them returns a non-nil value.  If this
;                   happens, then SOME returns the elements of list from
;                   that point on.  Otherwise it returns nil.
 
(defun Psome (f l)
  (do ((l l (cdr l)))
      ((null l) nil)
    (when (funcall f (car l)) (return l))))
  
;
;  S U B S E T  --  Form:  (subset function list)
;                     Applies function to successive elements of list
;                     and returns a list of the elements that returned
;                     non-nil values.

(defun Psubset (f l)
  (mapcar #'(lambda (ele)
	      (if (funcall f ele) (ncons ele) nil))
	  l))

;
;  P L O O P  --  Form:  (Ploop (local -var exp-)
;                            (while exp)
;                            (do -exp-)
;                            (until exp)
;                            (result exp)
;                      )
  
(defmacro Ploop (&body l)
  `(prog ,(var-list-loop (get-keyword-loop 'local l))
	 ,@(delete-if-not #'caddr
		   (setq-steps-loop (get-keyword-loop 'local l)))
      loop
	 ,@(apply #'append
		  (mapcar #'do-clause-loop l))
	 (go loop)
      exit (return ,@(let ((values (get-keyword-loop 'result l)))
		       (if values
			   values
			   '((values)))))))

(defun do-clause-loop (clause)
  (cond ((member (car clause) '(local result)) nil)
	((eql (car clause) 'while)
	 `((or ,(cadr clause) (go exit))))
	((eql (car clause) 'do) (cdr clause))
	((eql (car clause) 'until)
	 `((and ,(cadr clause) (go exit))))
	(t (error "~a~^ ~a" '"LOOP: Unknown keyword clause"))))

(defun get-keyword-loop (key l)
  (condcdr-loop (assoc key l)))

(defun var-list-loop (r)
  (and r (cons (car r) (var-list-loop (cddr r)))))

(defun setq-steps-loop (s)
  (and s (cons (list 'setq (car s) (cadr s))
	       (setq-steps-loop (cddr s)))))

(defun condcdr-loop (l)
   (if l (cdr l) nil))


(defmacro Pif (&body lis)
  ;;  Form:  (Pif exp --> -exps- 
  ;;          || exp --> -exps-    !
  ;;              . . .            ! These are optional
  ;;          || exp --> -exps-    !
  ;;          fi)
  ;;  Translates to cond in the obvious way.
  (do ((condlist (list 'cond)))
      ((eql (car lis) 'fi) (nreverse condlist))
    (unless (eql (second lis) '-->)
      (error "~a~^ ~a" '|Missing --> in an IF construct.|))
    (push
      (cons (car lis)
	    (progn
	      (setf lis (cddr lis))
	      (do ((consequent nil))
		  ((or (null lis) (member (car lis) '(fi ||)))
		   (when (null lis) (error "~a~^ ~a" '|Missing FI.|))
		   (when (eql (car lis) '||) (pop lis))
		   (nreverse consequent))
		(push (pop lis) consequent))))
      condlist)))

(defun o (f g)
  #'(lambda (x) (funcall f (funcall g x))))


