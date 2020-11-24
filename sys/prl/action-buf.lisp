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


;--      ACTION-BUFFER.L
;-- 
;-- Because of the lookahead needed by both the scanner and the parser, we
;-- need a buffer between the Ttree generator and the best Ttree computor. 
;-- For historical reasons we call the entities being sent from the
;-- generator to the computor "actions".  An action is a number
;-- (representing a character), the atom ENTER, or a list (actually a
;-- definition reference).
;-- 
;-- The data structures needed are set up by:
;-- 
;--      (action-buffer-create)
;-- 
;-- Initially, the action buffer is dead, that is, it doesn't take notice of
;-- any requests made of it.  To make it come alive one calls:
;-- 
;--      (activate-action-buffer)
;--           This causes the action buffer to respond to requests, and
;--           initializes the buffer (and thus the actions for the current token)
;--           to be empty. 
;-- 
;-- To kill it one calls:
;-- 
;--      (deactivate-action-buffer)
;--           Causes any subsequent requests to the buffer (up to the next time
;--           activate-action-buffer is called) to be ignored.
;-- 
;-- This explicit activation, deactivation is needed because of the ML
;-- interface.  When it starts up, prl just hands it characters, about which
;-- prl doesn't care.  Then when an ml quote character is seen, the ml system
;-- asks for a term to be parsed.  At this point the action buffer must be
;-- activated for the best Ttree for the term to be computed in the parsing
;-- of the term.  Because there could be many "raw" characters passed to ML
;-- before any prl scanning is done, we don't want the actions for these
;-- characters to pile up in the buffer.
;-- 
;-- The following routines have the given effect only when the action buffer
;-- is alive.
;-- 
;-- The Ttree generator sends new actions to the buffer using:
;-- 
;--      (add-to-action-buffer action)
;--           The action is added to the buffer, but not associated with the
;--           current token. 
;-- 
;-- The scanner causes actions to be associated with the current
;-- token using the two calls:
;-- 
;--      (add-all-to-token-actions)
;--           All actions which have been added to the buffer but not
;--           associated with the current token are associated with the current 
;--           token now. 
;-- 
;--      (add-white-space-to-token-actions)
;--           It is assumed that the only actions unassociated with the current 
;--           token are some number of "white space" actions followed by the
;--           actions for the first character of the next token.  This
;--           causes all the white space actions, up to the first unmatched
;--           ENTER, to be associated with the current token.
;-- 
;-- 
;-- The parser controls when the current token's actions are sent
;-- to the best Ttree computor using:
;-- 
;--      (flush-token-actions)
;--           All the actions associated with the current token are sent to
;--           the best Ttree computor.
;-- 
;-- The scanner is sometimes used in situations where not all the tokens are
;-- used by the parser, and thus flush-token-actions is not being called for
;-- every token.  To avoid overflowing the action buffer we arrange for the
;-- scanner to call the following routine at the beginning of execution of
;-- scan.
;-- 
;--       (forget-previous-token-actions)
;--           Forget the actions associated with the previous token and
;--           initialize the actions for the current token to be empty.
;-- 

;-- IMPLEMENTATION
;-- 
;-- We store the values in a vector (as defined in vector.l)
;--

(defvar action-buffer-active)  ;-- True iff the action buffer should respond
                               ;-- to requests.

(defvar action-buffer)         ;-- The vector holding the actions.
(constant action-buffer-init-size 100)

(defvar next)                  ;-- The index of the next available slot.
(defvar token-begin)           ;-- The index of the first action associated
                               ;-- with the current token.
(defvar token-end)             ;-- The first slot after the actions for the
                               ;-- current token
(defvar action-buffer-size)    ;-- The buffers current-size.

(defun action-buffer-create ()
    (<- action-buffer (new-vector action-buffer-init-size))
    (<- action-buffer-size action-buffer-init-size)
    (<- action-buffer-active nil)
)

(defun activate-action-buffer ()
    ;-- Make it active.
        (<- action-buffer-active t)

    ;-- Initialize it to be empty.
        (<- next 0)
        (<- token-begin 0)
        (<- token-end 0)
)

(defun deactivate-action-buffer ()
    ;-- Make it inactive
        (<- action-buffer-active nil)
)

;-- For Franz: hide the local implementation functions.
;(declare (localf AB-add-to-action-buffer AB-add-all-to-token-actions
;                 AB-add-white-space-to-token-actions AB-flush-token-actions
;                 AB-forget-previous-token next-in-buffer
;                 find-matching-white-space grow-action-buffer
;         )
;)

;-- The message handler for the action buffer.  We do it way to make the
;-- checking of action-buffer-active easy.
(defun send-to-action-buffer (message &optional value)
    (Pif action-buffer-active -->
        (case message
            (:value           (AB-add-to-action-buffer value))
            (:add-to-all      (AB-add-all-to-token-actions))
            (:add-white-space (AB-add-white-space-to-token-actions))
            (:flush-token     (AB-flush-token-actions))
            (:forget-prev     (AB-forget-previous-token))
        )
     fi)
)

;-- Define the interface functions.
(defun add-to-action-buffer (value)
    (send-to-action-buffer ':value value)
)
(defun add-all-to-token-actions ()
    (send-to-action-buffer ':add-to-all)
)
(defun add-white-space-to-token-actions ()
    (send-to-action-buffer ':add-white-space)
)
(defun flush-token-actions ()
    (send-to-action-buffer ':flush-token)
)
(defun forget-previous-token-actions ()
    (send-to-action-buffer ':forget-prev)
)

;-- The implementation functions.  The function named AB-x is just the
;-- function which implements the function advertised by the name x.
;-- 
(defun AB-add-to-action-buffer (val)
    (<- (vector-ref action-buffer next) val)
    (<- next (next-in-buffer next))
    (Pif (= next token-begin) -->
        (grow-action-buffer)
     fi)
)

(defun AB-add-all-to-token-actions ()
    (<- token-end next)
)

(defun AB-add-white-space-to-token-actions ()
    (multiple-value-bind
        (found end) (find-matching-white-space)
        (Ploop
            (while found)
            (do
                (<- token-end end)
                (multiple-value-setq (found end) (find-matching-white-space))
            )
        )
    )
)

(defun AB-flush-token-actions ()
    (Ploop
        (while (not (= token-begin token-end)))
        (do
            (Plet (val (vector-ref action-buffer token-begin))
                (Pif (numberp val) -->
                    (send-to-best-Ttree ':value val)
                 || (consp val) -->
                    (send-to-best-Ttree ':exit val)
                 || t -->
                    (send-to-best-Ttree ':enter)
                 fi)
            )
            (<- token-begin (next-in-buffer token-begin))
        )
    )
)

(defun AB-forget-previous-token ()
    (<- token-begin token-end)
)

(defun next-in-buffer (slot)
    (rem (1+ slot) action-buffer-size)
)

(defun find-matching-white-space ()
    (Ploop
        (local slot            token-end
               nesting-level   0
               all-white-space t
        )
        (while (and (not (= slot next)) all-white-space))
        (do
            (Plet (val (vector-ref action-buffer slot))
                (Pif (numberp val) -->
                    (Pif (not (member val white-space)) -->
                        (<- all-white-space nil)
                     fi)
                 || (consp val) -->
                    (Pif (> nesting-level 0) -->
                        (<- nesting-level (1- nesting-level))
                     fi)
                 || (eql val 'ENTER) -->
                    (<- nesting-level (1+ nesting-level))
                 fi)
            )
            (Pif all-white-space -->
                (<- slot (next-in-buffer slot))
             fi)
        )
        (until (= nesting-level 0))
        (result
            (Pif (and (not (= slot token-end)) (= nesting-level 0)) -->
                (values t slot)
             || t --> nil
             fi)
        )
    )
)

(defun grow-action-buffer ()

    ;-- Make the buffer bigger.
    (<- action-buffer
        (grow-vector action-buffer (+ action-buffer-init-size action-buffer-size))
    )

    ;-- ShPift all the values in token-begin..buffer-size-1 over so they are
    ;-- at the "right hand side" of the buffer.
    (Ploop
        (local from (1- action-buffer-size)
               to   (1- (vector-length action-buffer))
        )
        (while (>= from token-begin))
        (do
            (<- (vector-ref action-buffer to) (vector-ref action-buffer from))
            (<- from (1- from))
            (<- to (1- to))
        )
    )

    ;-- Correct the state variables.
    (Plet (shift (- (vector-length action-buffer) action-buffer-size))
        (Pif (>= token-end token-begin) -->
            ;-- Token-end indicated a slot in the values that got shifted so
            ;-- must be updated.
            (<- token-end (+ token-end shift))
         fi)
        (<- token-begin (+ token-begin shift))
    )
    (<- action-buffer-size (vector-length action-buffer))
)

    

         
