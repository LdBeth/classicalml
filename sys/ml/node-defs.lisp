;;; -*- Package: Nuprl; Syntax: Common-lisp; Base: 10. -*-

(in-package "NUPRL")

;;; Contains the definitions of the nodes that appear in the converted abstract
;;; syntax tree.  Note that as convert cannibalizes old list structure, the
;;; constructor functions implicitly defined herein aren't used.  Provided to
;;; help maintain the sanity of anyone trying to read the translation code.
;;; Not included here are definitions for node kinds that are removed in the
;;; conversion process, e.g. mk-binop or mk-straint.

(defstruct (node (:type list))
  kind)

(defmacro defnode (node-type kind &body fields)
  `(defstruct (,node-type
	       (:type list)
	       (:include node (kind ',kind)))
     ,@fields))

(defnode const		     ; Any constant term.
  nil			     ; mk-boolconst, mk-intconst, mk-formconst,
			     ; mk-termconst and mk-tokconst
  value			     ; The tree for the value
)

(defnode empty  	     ; The empty pair
  mk-empty
)

(defnode fail		     ; An untagged failure
  mk-fail
)

(defnode var		     ; A variable reference.
  mk-var
  desc			     ; The descriptor for this reference.
)

(defnode and mk-and
  left
  right)

(defnode or mk-or
  left
  right)
	 
(defnode pair		     ; A pair.
  mk-dupl
  left			     ; The tree for the left component.
  right			     ; The tree for the right component.
)

(defnode binop		     ; A binary operator.  Occurs only in varstructs.
  nil
  op
  left
  right
)

(defnode ml-list	     ; A list
  mk-list
  list			     ; A list of trees denoting the values of the list.
)

(defnode assign	     ; An assignment
  mk-assign
  varstruct          ; Varstruct for the assignment.
  value              ; Value to be assigned to the varstruct.
)

(defnode seq		     ; A sequence of commands
  mk-seq
  for-effect		     ; A list of trees denoting commands that are purely
			     ; for effect.
  value			     ; The tree denoting the value to be returned.
)

(defnode failwith	     ; A failure
  mk-failwith
  exp			     ; The tree denoting the expression to be thrown.
)

(defnode test		     ; A conditional expression.
  mk-test
  conditional		     ; A list of arms
  else			     ; An else expression
)

(defnode arm	             ; An arm of a conditional expression.
  nil			     ; ONCE or ITER
  test			     ; A tree denoting a boolean value
  exp			     ; The tree denoting the expression to be executed if
			     ; test evaluates to true.
)

(defnode else	             ; The default for a conditional expression.
  nil			     ; ONCE, ITER or EMPTY
  exp			     ; The expression to be evaluated.
)

(defnode trap		     ; A trap
  mk-trap
  exp			     ; Denotes the expression during whose evaluation 
			     ; failures are to be trapped.
  conditional		     ; A list of arms.  The test of each arm
			     ; denotes a list of tokens.  
  else			     ; An else expression.
  else-binding-id	     ; If non nil, an identifier to  be bound to
			     ; the tag thrown by the failure during the
			     ; evaluation of the else expression.
)

(defnode appn		     ; An application
  mk-appn
  fun			     ; The function to apply.
  args			     ; The arguments of the application.
)

(defnode abstr		     ; An abstraction
  mk-abstr
  body			     ; Denotes the body of the abstraction.
  params		     ; A list of varstructs for the parameters of the
			     ; abstraction.
)

(defnode in		     ; A local declaration
  mk-in
  decl			     ; Denotes the declaration.
  body			     ; Denotes the expression to be evaluated in the scope
			     ; of the declaration.
)

(defnode decl		     ; A declaration
  nil			     ; mk-let, mk-letrec or mk-letref
  varstructs		     ; A list of varstructs corresponding to
  values                     ;   a list of values
)
