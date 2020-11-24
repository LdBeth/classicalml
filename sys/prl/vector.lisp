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

    
;--        VECTOR
;-- 
;-- Provides a machine independent interface to vectors.
;-- The operations provided are:
;-- 
;--    (new-vector size)          
;--          Returns a new vector of the given size.
;-- 
;--    (vector-set vec index exp)
;--          Sets the index'th element of vec to the value of exp and
;--          returns the value of exp.
;-- 
;--    (vector-ref vec index)
;--          Returns the value stored at the index'th element of vec.
;-- 
;--    (vector-length vec)
;--          Returns the length of the vector. 
;-- 
;--    (grow-vector vec length)
;--          Returns a vector whose length is at least length and whose
;--          first (vector-length vec) are eq to the elements of vec.
;-- 


(defun new-vector (size) (make-array size :adjustable t))

(defun vector-set (vec index exp)
    (setf (aref vec index) exp))

(defun vector-ref (vec index)
    (aref vec index))

(defsetf vector-ref (vec index) (exp) `(setf (aref  ,vec ,index) ,exp))

(defun vector-length (vec)
    (array-total-size vec))

(defun grow-vector (vec length)
    (adjust-array vec (max length (* 2 (array-total-size vec)))))

;;;        EVECTOR
;;; 
;;; Provides an extensible vector.  The constructor is:
;;; 
;;;    (new-evec size)          
;;;          Returns a new extensible of the given size.
;;; 
;;; The operations are:
;;; 
;;;    (evec-set evec index exp)
;;;          Sets the index'th element of evec to the value of exp and
;;;          returns the value of exp.  If index is larger than the current
;;;          length of the vector, the vector is grown so that index will
;;;          reference storage in the vector.
;;; 
;;;    (evec-ref evec index)
;;;          Returns the value stored at the index'th element of evec.
;;; 
;;;
 
(defsetf evec-ref (evec index) (exp) `(funcall ,evec :set ,index ,exp))

;;; IMPLEMENTATION
;;; 
;;; The extensible vector is represented by a closure over a vector (as
;;; defined in vector.l) and a function which interprets the following
;;; messages:
;;; 
;;;      :set index exp
;;;      :ref index
;;; 
;;; (The obvious action is performed.)
;;; 

(defun new-evec (size)
  (let ((TheVec (new-vector size)))
    #'(lambda (type index &optional exp)
	(case type
	  (:set
	   (when (>= index (vector-length TheVec))
	     (setf TheVec (grow-vector TheVec index)))
	   (<- (vector-ref TheVec index) exp))
	  (:ref (vector-ref TheVec index))))))

;;; Interface functions

(defun evec-ref (evec index)
    (funcall evec ':ref index))

(defun evec-set (evec index exp)
    (funcall evec ':set index exp))

;;;         STACK
;;; 
;;; Defines a generic stack.  The constructor for a stack is:
;;; 
;;;      (make-stack size new-element-allocator element-updater)
;;;           Returns a stack which initially can hold size elements.  It
;;;           automatically extends itself as necessary.  The
;;;           new-element-allocator should be a lambda of no arguments which
;;;           returns space for a new element of the stack.  The
;;;           element-updater should be a lambda of two arguments.  It
;;;           should initialize the first argument using the value of the
;;;           second type and then return the initialized value.
;;;           (For stacks of constants, the new-element-allocator should
;;;           probably return nil or 0, and element-updater should simply
;;;           return the second argument.)
;;; 
;;; The operations that can be performed on these stacks are:
;;; 
;;;      (stack-push stack value)
;;;           Push the value on the stack using the element updater.
;;; 
;;;      (stack-pop stack)
;;;           Pop the top element off the stack and return it.  Return nil
;;;           if the stack is empty.
;;; 
;;;      (current-size stack)
;;;           Return the number of elements currently on the stack.
;;; 
;;;      (ith-element stack i)
;;;           Returns the i'th from the top element of the stack.  Return
;;;           nil if there aren't that many elements in the stack. 
;;; 
;;;      (make-empty-stack stack)
;;;           Resets the stack to be empty
;;; 
;;; This should be all you need to know to use these stacks.

;;; IMPLEMENTATION
;;; 
;;; The elements of the stack are held in extensible vectors (as defined in
;;; evector.l).
;;; A stack is a closure over an evector, the index of the next available slot
;;; in the stack, the new element allocator and the element updater.
;;; The function of the closure interprets messages of the following form:
;;; 
;;;       ':push         value
;;;       ':pop
;;;       ':current-size
;;;       ':ith-element  i
;;;       ':mk-empty
;;; 
;;; (The action indicated above is performed.)
;;;

(defun make-stack (size new-element-fcn element-updater)
  ;; Make a new stack of initial size size, whose elements are to be allocated
  ;; by new-element-fcn and updated by element-updater.
  (let ((Svec (new-evec size))
	(Snext 0)
	(Snew new-element-fcn)
	(Supdate element-updater)
	(Sinit 0))
    (flet ((push-in-stack (value)
	     (let ((element (if (= Snext Sinit)
				(progn (incf Sinit) (funcall Snew))
				(evec-ref Svec Snext))))
	       (<- (evec-ref Svec Snext) (funcall Supdate element value))
	       (incf Snext)))
	   (pop-in-stack ()
	     (when (> Snext 0)
	       (decf Snext)
	       (evec-ref Svec Snext)))
	   (ith-element-in-stack (i)
	     (unless (> i (1- Snext))
	       (evec-ref Svec (- Snext i 1)))))
      #'(lambda (kind &optional value)
	  (case kind
	    (:push         (push-in-stack value))
	    (:pop          (pop-in-stack))
	    (:current-size (1- Snext))
	    (:ith-element  (ith-element-in-stack value))
	    (:mk-empty     (<- Snext 0)))))))

;;; Interface functions

(defun stack-push (stack val)
    (funcall stack ':push val))
(defun stack-pop (stack)
    (funcall stack ':pop))
(defun ith-element (stack i)
    (funcall stack ':ith-element i))
(defun current-size (stack)
    (funcall stack ':current-size))
(defun make-empty-stack (stack)
    (funcall stack ':mk-empty))
