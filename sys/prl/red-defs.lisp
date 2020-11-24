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


;-------------------------------------;
;                                     ;
;       RED DATA DEFINITIONS          ;
;                                     ;
;-------------------------------------;


;-- Proof data descriptor: these structures are kept in
;-- the region array for all active Proof regions

(Pdeftype red-descriptor
   (thm type         ;-- THM object being edited
      theorem-object ;--
                     ;--
    proof-cursor     ;-- Cursor into proof part of the theorem being edited.
                     ;--   This cursor is a list of subgoal numbers (each of
                     ;--   which is >= 1).  The nil cursor selects the top
                     ;--   level of the proof, additional numbers select the
                     ;--   specified level of the level selected so far.
                     ;--   A level is a subgoal and its children.
    displayed-cursor-body
                     ;-- Prlstr showing the last four levels of the current
                     ;-- proof-cursor.  'top' is displayed for level 0 and
                     ;-- ... is used to indicate the cursor isn't complete.
    current-level    ;-- The level of the proof selected by proof-cursor.
    level-cursor     ;-- The level-cursor (defined below) for current-level.
    long-count       ;-- Number of presses of LONG pending for this region.
    level-map        ;-- List of level-map-entry, these entries are in
                     ;--   increasing order as one proceeds down the display
                     ;--   of the entire current-level.  Both the lines
                     ;--   numbers and the stopping points (with the 'natural'
                     ;--   order imposed) increase.
    first-displayed-entry
                     ;-- The level-map-entry of the entity visible at
                     ;--   the top of the view.
    edited-part      ;-- The sort of thing being edited in the subsidiary
                     ;--   TTREE region (RULE of current-level or MAINGOAL)
                     ;--   or nil if nothing is being edited.
    previous-ch-was-exit
                     ;-- t if the most recently processed input char was
                     ;--   an EXIT (contro-D), nil otherwise
   )
)


;--
;-- A 'normal' view of a proof looks like
;--
;--
;--         .------------------------------------------------.
;--         |                                                |
;--         |------------------------------------------------|
;--         |# top 1 2                                       |
;--         |1. x:int                                        |
;--         |2. y:int                                        |
;--         |>> int                                          |
;--         |                                                |
;--         |BY int intro x+y                                |
;--         |                                                |
;--         |1* 1. x:int                                     |
;--         |   >> x:int                                     |
;--         |                                                |
;--         |2# 1. y:int                                     |
;--         |   >> y:int                                     |
;--         |                                                |
;--         .------------------------------------------------.
;--


(deftuple level-map-entry   ;-- Description of one 'entry' in the view.
                            ;--   Entries are assumptions,
                            ;--   conclusions, and rules.  Each is given
                            ;--   its own set of lines in the view.
    level-cursor            ;-- The level-cursor for this entry of the
                            ;--   current-level.
    start                   ;-- First line number of this entry in the fully
                            ;--   laid out level.  The first line of the
                            ;--   first entry is line number 1.
                            ;--   (line number 0 is now reserved for
                            ;--   displayed cursor)
    end                     ;-- Last line number of the entry.
    body                    ;-- Ttree to display with this entry.  For goals
                            ;--   the assumptions and conclusion are just
                            ;--   the 'text' of the formula (i.e. with no
                            ;--   assumption num or '>>').  The rule has no
                            ;--   'BY'.  This Ttree is laid out in an area
                            ;--   indented from the left margin of the view
                            ;--   by the length of the label, defined below.
    label                   ;-- The prlstring that labels the displayed body.
                            ;--   For example, for a rule it is 'BY '.
                            ;--   The general layout of an entry looks like:
                            ;--
                            ;--       |   :                 |
                            ;--       |   :                 |
                            ;--       |                     |
                            ;--       |label................|
                            ;--       |     .              .|
                            ;--       |     .    ttree     .|
                            ;--       |     .              .|
                            ;--       |     ................|
                            ;--       |                     |
                            ;--       |   :                 |
                            ;--       |   :                 |
)


(deftuple level-cursor      ;-- The entity that specifies one entry in
                            ;--   a given level of a proof.
    major                   ;-- The major stopping point is
                            ;--     (GOAL)           for the  goal
                            ;--     (RULE)           for the  rule
                            ;--     (SUBGOAL 1)
                            ;--       ..(SUBGOAL n)  for the  subgoals
    minor                   ;-- The minor stopping point is nil if the major
                            ;--   does not specify a (sub)goal.  If it does
                            ;--   then the minor is
                            ;--     (ASSUM 1)
                            ;--       ..(ASSUM m)    for the  assumptions
                            ;--     (CONCL)          for the  conclusion
)


(global rdescr$ red-descriptor)



