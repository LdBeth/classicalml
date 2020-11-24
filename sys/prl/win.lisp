;;; -*- Package: Nuprl; Syntax: Zetalisp; Base: 10. -*-

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                                                            ;
;       NuPrl Mathematics Environment -- Release 1                           ;
;           developed by J. Bates, R. Constable, and the PRL group.          ;
;           Computer Science Department, Cornell University, Ithaca, NY      ;
;           (see herald.lisp for complete list of contributors)              ;
;                                                                            ;
;       Permission is granted to use and modify NuPrl                        ;
;       provided this notice is retained in derived works.                   ;
;                                                                            ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


#+franz
(declare (macros t))
#+franz
(eval-when (compile)
    (load 'data-defs)
)


(pdeftype wstate-array array (MAXNUMWINDOWS)   ;-- The i'th entry contains
                                              ;--  current status for window
                                              ;--  number 'i'.  If window
                                              ;--  does not currently exist,
                                              ;--  the 'top' component will be
                                              ;--  nil.
                        (top         ;-- Position of top of window 
                                     ;--   including border lines.
                         left        ;-- Position of left of window
                                     ;--   including border line.
                         height
                         width
                         elided
                         header      ;-- Prlstring of header line
                        )
)

(global W-INFO wstate-array)

(defun window-width (win) (sel W-INFO (win) width))
(defun window-height (win) (sel W-INFO (win) height))

(deftuple ewslot   ;-- Elided window slot tuple
          owner      ;-- Window number of elided window in this slot
                     ;--  (0 indicates slot is available)
          top        ;-- Origin on screen of this slot
          left
)

(deftuple wcursor  ;-- Tuple returned by call to 'getcursor'
          y        ;-- Current output cursor location in window
          x        ;--   passed an argument to 'getcursor'.
)


(global display-message-window)  ;-- Window where output from 
                                 ;-- 'display-message' function should
                                 ;-- go.

(global menuwindow$)
(global selected-prl-window$)
(global windowtodo$)
(global was-selected$)
(global menuop$)

(global elided-slot-list$)

(constant NO-OP$ -1)
(constant ELIDEDSLOTWIDTH 12)


;
;   I N I T W
;

(defun initw()

   ;-- Initialize window interface and all lower level routines.

      ;-- Create the W-INFO array
         (<- W-INFO (new wstate-array))
      ;-- Initialize window routines
         (initwindows)
      ;-- Make the mouse menu
         (makemenu$)
      ;-- Create the elided-windows list
         (<- elided-slot-list$
             (Ploop (local yval 0
                          xval (- SCRWIDTH ELIDEDSLOTWIDTH)
                          l    nil
                   )
                   (while (lessp (+ yval 2) SCRHEIGHT))
                   (do 
                       (<- l (cons (ewslot 0 yval xval) l))
                       (<- yval (+ yval 2))
                   )
                   (result (reverse l))
             )
         )
)


(defun makemenu$()

   ;-- Create the mouse menu and stash it away off screen.

     (<- menuwindow$ (createw 3 7 1 5)) 
     (movew menuwindow$ -100 -100)
     (selectwindow menuwindow$)
     (setmouse 1)
     (<- menuop$ NO-OP$)
     (setheader ^MENU^)
     (putstr ^| Move^|) 
     (putstr ^| ... ^|)
     (putstr ^| Pull^|) 
     (putstr ^| Size^|) 
;    (putstr ^| Kill^|)  ; has a bug, so bag for now.
     (mapcar 'putc ^| Push^|)
     (movecursor 1 0)
)


;
;   C H A N G E S I Z E W
;

(defun changesizew (wnum y1 y2 x1 x2)
   ;-- Change the size of window 'wnum' by destroying it and then
   ;-- creating it with the new coordinates.  This routine makes
   ;-- the assumption that the first call to 'createwindow' after
   ;-- a 'destroywindow' will create a window with the same number
   ;-- as the window destroyed.  If 'wnum' was the currently 
   ;-- selected prl window, re-select it before returning.
   ;-- 

      (Plet (head-str (sel W-INFO(wnum) header))
          (destroyw wnum)
          (Pif (not (equal wnum (createw y1 y2 x1 x2)))  -->
              (error '|CHANGESIZEW: Created wnum not equal destroyed wnum.|)
           fi)
          (<- (sel W-INFO(wnum) header) head-str)
          (selectwindow wnum)
          (setheader head-str)

          (Pif (equal wnum selected-prl-window$)  -->
              (selectwindow selected-prl-window$)
           fi)
      )
)


;
;   C R E A T E W 
;

(defun createw (y1 y2 x1 x2)

   ;-- Create a window whose diagonally opposite corners
   ;-- are y1,x1 and y2,x2.

     (Plet (window nil)
          (<- window (createwindow y1 y2 x1 x2))
          ;-- Initialize window origin and status in W-INFO array.
             (<- (sel W-INFO(window) top) (- (min y1 y2) 3))
             (<- (sel W-INFO(window) left) (- (min x1 x2) 1))
             (<- (sel W-INFO(window) height) (1+ (abs (- y1 y2))))
             (<- (sel W-INFO(window) width) (1+ (abs (- x1 x2))))
             (<- (sel W-INFO(window) elided) nil)
             (<- (sel W-INFO(window) header) nil)

          ;-- Return window num of window just created.
             window
     )
)


;
;   G E T W  Routines
;
;       Return the top, bot, left, right values needed to create
;       this window using createw.
;

(defun getw-top (window)
   (+ (sel W-INFO (window) top) 3)
)

(defun getw-bot (window)
   (+ (sel W-INFO (window) top) (sel W-INFO (window) height) 2)

)

(defun getw-left (window)
   (+ (sel W-INFO (window) left) 1)
)

(defun getw-right (window)
   (+ (sel W-INFO (window) left) (sel W-INFO (window) width))
)


;
;   C L E A R - S C R E E N
;

(defun clear-screen()

   ;-- Clear contents of screen.

      (clearscreen$)
)


;
;   D E S T R O Y A L L W
;

(defun destroyallw()

   ;-- For all existing windows (except the menuwindow), call 'destroyw'.

      (Ploop (local i 1)
            (while (lessp i MAXNUMWINDOWS))
            (do
                (Pif (not (equal i menuwindow$))  -->
                    (destroyw i)
                 fi)
                (<- i (1+ i))
            )
      )

   ;-- Set selected-prl-window to nil, since there are no windows. 
      (<- selected-prl-window$ nil)
)


;
;   D E S T R O Y W
;

(defun destroyw(wnum)

   ;-- Destroy the window whose id is 'wnum', Pif it currently exists.
   ;-- Mark it as destroyed by setting the 'top' field of W-INFO to nil.

      (Pif (sel W-INFO(wnum) top)  -->
          (destroywindow wnum)
          (remove-from-slotlist$ wnum)
          (<- (sel W-INFO(wnum) top) nil)
       fi)
)


;
;   D I S P L A Y - M E S S A G E
;

(defun display-message(str)

   ;-- Displays a message (prlstring) on a new line in display-message-window
   ;-- window, and leaves with the cursor on the line immediately following
   ;-- the message, and with the selected-prl-window window selected.
   
      (selectwindow display-message-window)
      (Pif (plusp (x-of-wcursor (getcursor display-message-window)))  -->
          (putnl)
       fi)

      (putstr str)
      (putnl)

      (selectwindow selected-prl-window$)
)


;
;   E X P L I C I T - M O U S E - M O D E
;

(defun explicit-mouse-mode (mode)

   ;-- 'Mode' non-nil means explicit-mouse-mode being entered.
   ;-- Null means it is being exited.

   (Plet (save-selected selected-prl-window$)
       (Pif mode -->
           ;-- Enter mode.
              (enter-mouse-mode)
        || t  -->
           ;-- Exit mode.
              (leave-mouse-mode)
        fi)
       (<- selected-prl-window$ save-selected)
       (selectwindow selected-prl-window$)
   )
)

;
;   G E T C H A R
;

(defun getchr()

   ;-- Get the next char via 'getc'.  Handle all MOUSE-MENU events.
   ;-- Translate all MOUSE-SEL or MOUSE-JUMP events into a tuple of
   ;-- the form   
   ;--            MOUSE-SEL | MOUSE-JUMP
   ;--                  window num
   ;--                    rel x
   ;--                    rel y
   ;-- If the window num is 0, then the event is discarded.
   ;--
   ;-- If SNAPSHOT character is seen, dump the screen contents to
   ;-- the file "snap-<user>".

      (Plet (ch nil)
          (Ploop
               (do
                  (<- ch (getc))
                  (Pif (dtpr ch)  -->
                      (Pif (or (eq (car ch) 'MOUSE-SEL)
                              (eq (car ch) 'MOUSE-JUMP)
                          )  -->
                          ;-- Translate into a 4 element tuple as 
                          ;-- described above.
                          ;-- Just throw away absx and absy.
                             (<- (cdr ch) (cdddr ch))
                             (Pif (zerop (cadr ch))  -->
                                 ;-- Discard event by setting ch to nil.
                                 (<- ch nil)
                              fi)
                       || (eq (car ch) 'MOUSE-MENU)  -->
                          ;-- Handle mouse event and indicate that
                          ;-- another char must be read.
                             (domouse$ ch)
                             (<- ch nil)
                       || (eq (car ch) 'SNAPSHOT)  -->
                          ;-- dump the screen to "snap-<user>" and indicate
                          ;-- that another char must be read.
                             (snapshot)
                             (<- ch nil)
                       fi)
                   fi)
               )
               (until ch)
          )
          ;-- Return ch.
             ch
      )
)



(defun domouse$(event)

     (Plet (absx  (cadr event)
           absy  (caddr event)
           wnum  (cadddr event)
           relx  (car (cddddr event))
           rely  (cadr (cddddr event))
          )
        (Pif (and (equal menuop$ NO-OP$)
                 (not (equal wnum menuwindow$))
            )  -->
            ;-- Move the mouse menu to absy, absx.
               (Pif (not (equal wnum menuwindow$))  -->
                   (<- windowtodo$ wnum)
                fi)
               (movew menuwindow$
                      (min absy (- SCRHEIGHT 10))
                      (min absx (- SCRWIDTH 7))
               )
         || (equal wnum menuwindow$)  -->
            ;-- Menu selection -- first erase previous selection char
               (selectwindow menuwindow$)
               (putc BS) (putc SPACE)
               (movecursor rely 0) (putc ^*)
               (<- menuop$ rely)
               (selectwindow selected-prl-window$)
               (Pif (equal menuop$ 2)  -->
                   ;-- Pull window.
                      (Pif (not (zerop windowtodo$)) -->
                          (pullwindow windowtodo$)
                       || t -->
                          (display-message ^|Cannot Pull.^|)
                       fi)
                      (reset-menu$)
                || (equal menuop$ 0)  -->
                   ;-- Move window.
                      (Pif (or (zerop windowtodo$)
                              (sel W-INFO(windowtodo$) elided)
                          )  -->
                          (display-message ^|Cannot Move.^|)
                          (reset-menu$)
                       || t  -->
                          (<- menuop$ 10)
                       fi)
                || (equal menuop$ 3)  -->
                   ;-- Size - changesize of window.
                      (Pif (or (zerop windowtodo$)
                              (sel W-INFO(windowtodo$) elided)
                          )  -->
                          (display-message ^|Cannot Size.^|)
                          (reset-menu$)
                       || t  -->
                          (<- was-selected$ selected-prl-window$)
                          (<- menuop$ 30)
                       fi)

		    ; Has a bug, so bag it for now.
;                || (equal menuop$ 4)  -->
;                   ;-- Kill - destroy window.
;                      (Pif (not (zerop windowtodo$))  -->
;                          (menu-kill-event windowtodo$ selected-prl-window$)
;                       || t  -->
;                          (display-message ^|Cannot Kill.^|)
;                       fi)
;                      (reset-menu$)

                || (equal menuop$ 4)  -->
                   ;-- Push window.
                      (Pif (not (zerop windowtodo$)) -->
                          (pushwindow windowtodo$)
                       || t -->
                          (display-message ^|Cannot Push.^|)
                       fi)
                      (reset-menu$)
                || (equal menuop$ 1)  -->
                   ;-- '...' - ellipse window.
                      (Pif (zerop windowtodo$)  -->
                          (display-message ^|Cannot Elide.^|)
                       || (sel W-INFO(windowtodo$) elided)  -->
                          ;-- Unelide and move back to its original 
                          ;--  location.
                             (remove-from-slotlist$ windowtodo$)
                             (<- (sel W-INFO(windowtodo$) elided) nil)
                             (movewindow windowtodo$
                                         (sel W-INFO(windowtodo$) top)
                                         (sel W-INFO(windowtodo$) left)
                             )
                             (setelide windowtodo$ nil)
                       || t -->
                          ;-- Find the first free slot in the elided-windows
                          ;--  list, elide window and move header to slot. 
                            (Plet (freeslot nil)
                              (Ploop (local l elided-slot-list$)
                                    (while (and l (null freeslot)))
                                    (do 
                                        (Pif (zerop (owner-of-ewslot (car l))
                                            ) -->
                                            ;-- Have found an available slot.
                                            (<- freeslot (car l))
                                            (<- (owner-of-ewslot freeslot)
                                                windowtodo$
                                            )
                                         fi)
                                        (<- l (cdr l))
                                    )
                              )
                              (Pif (null freeslot)  -->
                                  (display-message ^|Cannot Elide.^|)
                               || t  -->
                                  (<- (sel W-INFO(windowtodo$) elided) t)
                                  (setelide windowtodo$ t)
                                  (movewindow windowtodo$
                                              (top-of-ewslot freeslot)
                                              (left-of-ewslot freeslot)
                                  )
                               fi)
                             )
                       fi)
                      (reset-menu$)
                || t -->
                      (reset-menu$)
                fi)
         || (equal menuop$ 10)  -->
               (movew windowtodo$ absy absx)
               (reset-menu$)
         || (equal menuop$ 30)  -->
            ;-- Changesize - new window corner is absy,absx.
            ;-- Compute newtop, newleft, newbot and newright and call
            ;-- 'menu-size-event' to handle the changesize.
            ;-- At the end, reselect window that was selected when
            ;-- size operation was chosen fro th menu.
               (<- absx (min absx (- SCRWIDTH 2)))
               (<- absy (min absy (- SCRHEIGHT 2)))
               (menu-size-event windowtodo$
                                selected-prl-window$
                                (min absy
                                     (+ (sel W-INFO(windowtodo$) top) 3)
                                )
                                (min absx
                                     (1+ (sel W-INFO(windowtodo$) left))
                                )
                                (max absy
                                     (+ (sel W-INFO(windowtodo$) top) 3)
                                )
                                (max absx
                                     (1+ (sel W-INFO(windowtodo$) left))
                                )
               )
               (<- selected-prl-window$ was-selected$)
               (reset-menu$)
         fi)
     )
)

(defun reset-menu$ ()
      (<- menuop$ NO-OP$)
      (selectwindow menuwindow$)
      (putc BS) (putc SPACE)
      (Pif selected-prl-window$  -->
          (selectwindow selected-prl-window$)
       fi)
      (<- windowtodo$ 0)
      (movew menuwindow$ -100 -100)
)

(defun remove-from-slotlist$ (wnum)
      (for (x in elided-slot-list$)
           (when (equal wnum (owner-of-ewslot x)))
           (do 
               (<- (owner-of-ewslot x) 0)
           )
      )
)


            
;
;   M O V E C U R S O R
;

(DEFUN movecursor (y x)

   ;-- Moves window cursor for currently selected window to 
   ;-- relative location x,y.

      (putc RS) (putc (+ SPACE x)) (putc (+ SPACE y))
)

(defun erase-to-end-of-line ()
  (putc EEOL))

(defun clear-window ()
  (putc CLEAR))

;
;   M O V E W
;

(defun movew (wnum y x)

   ;-- Move window 'wnum' so that the top left is positioned
   ;-- at location y,x on the screen.

      (movewindow wnum y x)
      ;-- Update window origin in W-INFO array.
         (<- (sel W-INFO(wnum) top) y)
         (<- (sel W-INFO(wnum) left) x)
)


;
;   P U T C
;
;  (defun putc(char)

      ;-- This function is contained within the window package (window.l)
      ;--   Puts 'char' into the selected window at the current output
      ;--   location.  Returns the x-coordinate of the new output location,
      ;--   i.e., after char has been processed.
;  )


;
;   P U T N L
;

(defun putnl()

   ;-- Puts a CR followed by LF into the currently selected window.

       (putc EEOL)
       (putc CR)
       (putc LF)
)

(defun erase-n-chars (n)
  (dotimes (i n) (putc ^| |)))

(defun erase-to-end-of-line ()
  (putc EEOL))

(defun clear-window ()
  (putc CLEAR))

;
;   P U T S T R
;

(defun putstr(str)

   ;-- Puts the prlstring 'str' into the current output location
   ;-- of the selected window.

      (Plet (line-wrapped nil)
          (Ploop
               (while str)
               (do
                  (Pif (zerop (putc (car str)))  -->
                      (<- line-wrapped t)
                   fi)
                  (<- str (cdr str))
               )
          )
          (Pif line-wrapped  -->  (putc EEOL) fi)
      )
)


;
;   R E A D L I N E
;

(defun Preadline(prompt splicer)

   ;-- Print the prompt in the selected window, read chars from 'getchr'
   ;-- until a (NL) or (EXIT) character and return the list read.
   ;-- Whenever the result of 'getchr' is not a fixnum and not (EXIT),
   ;-- apply 'splicer' to it, and splice the resulting list into the
   ;-- list of characters read so far.  Thus 'splicer' should always 
   ;-- yield a list of fixnums, unless it yields the atom redisplay-line,
   ;-- in which case the prompt and chars typed so far are redisplayed.

      (Pif (plusp (x-of-wcursor (getcursor selected-prl-window$)))  -->
          (putnl)
       fi)
      (putc EEOL)
      (echo-str$ prompt)

      (Ploop (local chars      nil
                   ch         nil
                   splice-str nil
            )
            (do
               (<- ch (getchr))
               (Pif (dtpr ch)  -->
                   (Pif (eq (car ch) 'DEL)  -->
                       (<- chars (readline-del$ prompt chars))
		    || (eq (car ch) 'KILL-LINE) -->
		       (Ploop
			   (while (not (null chars)))
			   (do
			     (<- chars (readline-del$ prompt chars))
			   )
		       )
                    || (eq (car ch) 'EXIT)  -->
                       (<- chars (list ch))
                    || t  -->
		       (<- splice-str (apply splicer (list ch)))
		       (Pif (eq splice-str 'redisplay-line) -->
			   (putc CR)
			   (putc EEOL)
			   (echo-str$ (append prompt (reverse chars)))
			|| t -->
			   (echo-str$ splice-str)
			   (<- chars (nconc (reverse splice-str) chars))
			fi)
                    fi)
                || t  -->
                   ;-- Must be a printable character.
                   (echo-char$ ch)
                   (<- chars (cons ch chars))
                fi)
            )
            (until (or (equal ch '(NL))
                       (equal ch '(EXIT))
                   )
            )
            (result (progn (putc CR)
                           (putc LF)
                           (nreverse (cons '(NL) chars))
                    )
            )
      )
)

(defun readline-del$(prompt chars-so-far)

   ;-- Deletes the last character entered (only when the list of
   ;-- characters read so far is not null).  
   ;--   If cursor is currently at the beginning of a line, re-echo prompt and
   ;--   all characters read so far (except for the last).
   ;--   Else erase last character in current line by putc'ing
   ;--   a BS SPACE BS.

      (Pif chars-so-far  -->
          ;-- Remove last character entered.
             (<- chars-so-far (cdr chars-so-far))
          ;-- Now do appropriate action in window.
             (Pif (plusp (x-of-wcursor (getcursor selected-prl-window$)))  -->
                 (putc BS) (putc SPACE) (putc BS)
              || t  -->
                 ;-- In position 0 -- echo prompt followed by current 
                 ;-- list of characters.
                    (echo-str$ (append prompt (reverse chars-so-far)))
              fi)
       fi)

      ;-- Result is (possibly modified) chars-so-far.
         chars-so-far
)

(defun echo-str$(str)

   ;-- Echo 'str' into selected window

      (mapcar 'echo-char$ str)
)

(defun echo-char$(ch)

   ;-- Echo 'ch' into selected window.  If the x-coord after the 'putc'
   ;-- is zero, then clear the entire next line in preparation for
   ;-- input characters.

      (Pif (zerop (putc ch))  -->
          (putc EEOL)
       fi)
)

;
;  G E T - C U R R E N T - S E L E C T E D - W I N D O W
;
(defun get-current-selected-window ()
  selected-prl-window$)

;
;   R E - I N I T W
;

(defun re-initw()

   ;-- Called to re-initialize the screen and window routines
   ;-- to restart prl after, say, an error of sorts.

      (destroyallw)
      (reset-menu$)
      (setmouse 1)
)


;
;   S E L E C T W
;

(defun selectw(wnum)

   ;-- Makes the window whose id-number is 'wnum', the currently
   ;-- selected window.

      (selectwindow wnum)
      (<- selected-prl-window$ wnum)
)


;
;   S E T H E A D E R W
;
 

(defun setheaderw(start-pos str)

   ;-- If start-pos is nil, sets the header line for the window
   ;-- currently selected to the prlstring 'str'.  If start-pos is
   ;-- an integer, places str into the header of the current 
   ;-- window starting at position start-pos (1 is the first pos).

      (Plet (newstr nil
            oldstr nil
            i      0
           )

           (Pif (null start-pos) -->
               (<- newstr str)

            || t -->
               (<- oldstr (sel W-INFO (selected-prl-window$) header))
               
               ;-- copy the old string up to the start position
                   (Ploop
                       (local
                           ub    (min (length oldstr) start-pos)
                       )
                       (while (<& i ub))
                       (do
                           (<- newstr (cons (car oldstr) *-*))
                           (<- i (add1 i))
                           (<- oldstr (cdr *-*))
                       )
                   )

               ;-- insert blanks up to start position
                   (Ploop
                       (while (<& i start-pos))
                       (do
                           (<- newstr (cons ^| | *-*))
                           (<- i (add1 i))
                       )
                   )

               ;-- copy in the argument string
                   (Ploop
                       (while (not (null str)))
                       (do
                           (<- newstr (cons (car str) *-*))
                           (<- str (cdr *-*))
                       )    
                   )

               (<- newstr (nreverse newstr))

            fi)

           (<- (sel W-INFO (selected-prl-window$) header) newstr)
           (setheader newstr)
      )
) 