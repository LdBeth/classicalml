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


;-- Result returned by 'display-Ttree'.

(deftuple displayed-Ttree
            cursor-r     ;--  r,c relative to window of location in displayed  
            cursor-c     ;--      Ttree corresponding to 'cursor'.
                         ;--       (nil,nil if the 'cursor' has not been
                         ;--        reached by the time the bottom,right
                         ;--        of the region is encountered.
                         ;--        Else
                         ;--        A redisplay of Ttree with a new 
                         ;--        lines-to-skip = old lines-to-skip +
                         ;--        (cursor-r - top) will cause the cursor
                         ;--        to be on the first line of the region.
                         ;--       )
            ending-r     ;--  r,c relative to window of the last character
            ending-c     ;--      position + 1 displayed of Ttree.
                         ;--      (top$,left$ if value of lines-to-skip
                         ;--       causes the entire Ttree to be processed
                         ;--       before any characters have been output).
            nl-suffix    ;--  The first NL char encountered after 'cursor'
                         ;--       has been encountered, causes 'nl-suffix'
                         ;--       to be set to the suffix of the (sub)Ttree
                         ;--       being processed when that first NL
                         ;--       character was encountered.
                         ;--       (This is nil if 'cursor' not encountered
                         ;--        or no NL after 'cursor' encountered,
                         ;--        or 'cursor' encountered before 'top' 
                         ;--           of region (caused by lines-to-skip)
                         ;--       )
            nl-row       ;--  This is undefined if nl-suffix is nil,
                         ;--       else the row number of the NL character.
            first-blank-row ;-- This is set to
                            ;--   1. nil if region was filled by Ttree display
                            ;--   2. the input parameter 'first-blank-row' if
                            ;--         an early exit was taken
                            ;--   3. (either ending-r if ending-c = left
                            ;--       or (ending-r)+1 if ending-c > left
)

;-- Result returned by 'map-cursor-to-rc'.

(deftuple mapped-cursor
            cursor-r   ;-- r,c relative to window of location in displayed
            cursor-c   ;--     Ttree corresponding to 'cursor'.
                       ;--       (nil,nil if the 'cursor' has not been
                       ;--        reached by the time the bottom,right
                       ;--        of the region is encountered.
                       ;--        Else
                       ;--        A redisplay of Ttree with a new 
                       ;--        lines-to-skip = old lines-to-skip +
                       ;--        (cursor-r - top) will cause the cursor
                       ;--        to be on the first line of the region.
                       ;--       )
            nl-suffix  ;-- These two are the same as for 'displayed-Ttree'.
            nl-row     ;-- 
)

