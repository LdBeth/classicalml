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


;;;
;;; THEOREM-OBJECT
;;;
;;; A collection of functions to allow "proof tops".  The representation of a proof of a
;;; theorem object is either an actual proof tree or a rule body tree.  These functions
;;; allow "transparent" access to theorem objects.

(defvar *status-change-when-checking-is-an-error* nil)

(defun maybe-status-change-error ()
  (when *status-change-when-checking-is-an-error*
    (with-terminal-io-on-frame
      (cerror "Continue." "Here's a chance to quit."))))


;-- check-proof-of-object (obj name)
;--
;-- This has effect only for proofs represented as rule body trees.  It expands out
;-- the tree, and checks that the status obtained is the same as the status
;-- the object had when it was dumped.  Assumes obj has kind THM.
;-- 
(defun check-proof-of-object (obj name)
  (let ((thm (sel (object obj) value))
	(status (sel (object obj) status)))
    (unless (eql (sel (theorem-object thm) proof-rep-type) 'PROOF-TREE)
      (let* ((proof 
	       ;; Avoid nasty self-reference problems.
	       ;; (Non-loop cycles are still possible.)
	       (unwind-protect
		   (progn (<- (sel (object obj) status) 'BAD)
			  (build-proof-tree
			    (sel (theorem-object thm) goal-body)
			    (sel (theorem-object thm) proof-representation)))
		 (<- (sel (object obj) status) status)))
	     (new-status (if proof 
			     (red-status-to-obj-status
			       (status-of-proof-tree proof))
			     (if (eql status 'RAW) 'RAW 'BAD))))
	(<- (sel (theorem-object thm) proof-rep-type) 'PROOF-TREE)
	(<- (sel (theorem-object thm) proof-representation) proof)
	(cond ((not (eql new-status status))
	       (display-message
		 (append
		   '#.(istring "Warning: Status of ")
		   (istring name)
		   '#.(istring " has changed from ")
		   (istring status)
		   '#.(istring " to ")
		   (istring new-status)))
	       (<- (sel (object obj) status) new-status)
	       (when redisplay-on-status-change (update-lib-display (list name)))
	       (maybe-status-change-error))
	      (t
	       ;; t->T in lib display.
	       (when redisplay-on-status-change (update-lib-display (list name))))))))
  '(REFERENCED))

(defun get-proof-of-theorem-object (thm name)
  (check-proof-of-object (library-object name)
			 name)
  (sel (theorem-object thm) proof-representation))

(defun expanded-thm-p (obj)
  (and (eql (sel (object obj) kind) 'THM)
       (eql (sel (theorem-object (sel (object obj) value))
		proof-rep-type)
	   'PROOF-TREE)))

(defun set-proof-of-theorem-object (thm type rep)
    (<- (sel (theorem-object thm) proof-rep-type) type)
    (<- (sel (theorem-object thm) proof-representation) rep)
)

(defun get-conclusion-of-theorem-object (thm)
    (Pif (eql (sel (theorem-object thm) proof-rep-type) 'PROOF-TREE) -->
	(conclusion-of-proof-tree (sel (theorem-object thm) proof-representation))
     || (not (null (sel (theorem-object thm) conclusion))) -->
        (sel (theorem-object thm) conclusion)
     || t -->
        (Plet (conc (goal-body-to-proof-tree (sel (theorem-object thm) goal-body)))
	    (<- (sel (theorem-object thm) conclusion) (conclusion-of-proof-tree conc))
	    (conclusion-of-proof-tree conc)
	)
     fi)
)
