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


;       I N T E R F A C E    T O    S C R E E N    P R I M I T I V E S
;
;
;     (scrinit bordercharsvector)
;
;         Open the terminal and mouse devices and initialize internal
;                 state for I/O primitives.
;
;     (scrgetrows)
;
;         Returns the number of rows on the screen.
;
;     (scrgetcols)
;
;         Returns the number of columns on the screen.
;
;     (scrwrchar character)
;
;         Writes the character onto the screen.
;
;     (scrwrctl special-character)
;
;         Writes a terminal-specific character onto the screen.
;         The special characters are CLEAR$ (clear screen)
;         and FS$ (non-destructive space to the right).
;
;     (scrmvcursor x y)
;
;         Repositions the cursor to location x,y on the screen.
;         Location 0,0 is the upper left corner.
;
;         (scrrdchar)
;
;                 Get the next character from the input stream.
;
;         (scrmvmouse x y)
;
;                 Move mouse cursor to location x,y on the screen.
;
;         (set-prl-tty flag)
;
;                 Enable or disable PRL state on terminal according to
;                 whether flag is 1 or 0, respectively.
;
;         (get-keypad-def i j)
;
;                 Obtain character j of keypad sequence i.
;


;  CONSTANTS

(constant MAXSCRHEIGHT$ 150)     ;  Max num of lines on the physical screen
(constant MAXSCRWIDTH$ 200)      ;  Max num of chars per line on screen

(constant MAXLINELEN$ 200)       ;  Max chars on any line of a window
                                 ;   (not including border chars)

(constant MINHEIGHT$ 1)          ;  Windows must have at least this many lines
(constant MINWIDTH$ 1)           ;   and at least this many chars per line


(constant FONT0$ 0)              ;  Standard font number

(constant TABAMT$ 4)             ;  How far apart tab stops are


; CHARACTER CONSTANTS FOR OUTPUT THROUGH 'PUTC'

(constant BS 8)
(constant TAB 9)
(constant LF 10)
(constant EEOS 11)
(constant CLEAR 12)
(constant CR 13)
(constant HOME 25)
(constant ESC 27)
(constant FS 28)
(constant EEOL 29)
(constant RS 30)
(constant US 31)
(constant SPACE 32)

(constant BLANKMINUS1$ 31)

(defconstant *lispmprl-key-bindings*
	     #.`'((,(char-code #\circle) . ,(char-code #\`))
	       (,(char-code #\square) . ,(char-code #\`))
	       (,(char-code #\triangle) . ,(char-code #\`))))

(defun is-lispmprl-bound-key (ch)
    (assq ch *lispmprl-key-bindings*))

(defun ch-of-lispmprl-bound-key (ch)
    (cdr (assq ch *lispmprl-key-bindings*)))

(defun is-LM-symbol-ch (n)
    (and (numberp n) (lessp n 32) (not (minusp n))))

(defun code-LM-symbol-ch (n)
    (+ n 142))

(defun is-coded-LM-symbol-ch (n)
    (and (numberp n) (is-LM-symbol-ch (- n 142))))

(defun decode-LM-symbol-ch (n)
    (- n 142))

;  TYPES

(deftype warray vector (MAXNUMWINDOWS))  ;  entry nil -> window undefined

(deftype wtype 
             ( wnumid    ;  id number of window (0..) returned by CREATEWINDOW
               top       ;  y-coord of top border
               bot       ;  y-coord+1 of bottom border
               left      ;  x-coord of left border
               right     ;  x-coord+1 of right border
               depth     ;  z-coord of window (0 = foreground)
               fontnum   ;  number of font in which subsequent characters
                         ;     from 'putc' are to be displayed. 
               standout  ;  if 128, then subsequent characters get displayed in
                         ;     reverse video, if 0 then normal video.
               cursor-x  ;  cursor x-coord ( 0 .. (right-left-2) )
               cursor-y  ;  cursor y-coord ( 0 .. (bot-top-4) ) 
               cur-x     ;  index into 'char' array of wline
               cur-y     ;  list of wlines, the car of which is the current
               header    ;  List of all lines (wlines) for window   
               start     ;  List of all text lines minus the 3 header lines
               end       ;  List of last text line and the footer
                         ;  NOTE: start and end are suffixes of the header list
               elided    ;  if non-nil, then only the header of the window
                         ;     should be displayed.
             )
)

(deftype wline
             ( char byte-vector ((+ MAXLINELEN$ 2))     ;  chars in the line
                                                   ;   (including border chars).
               attrib byte-vector ((+ MAXLINELEN$ 2))   ;  attributes for each char 
                                                   ;    in the 'char' array.
               linenum                             ;  which line of the window
                                                   ;    this wline is. 
                                                   ;    (0 = the top header 
                                                   ;     line)
             )
)

(deftype  mapline byte-vector (MAXSCRWIDTH$))

(deftype  scrmap  vector (MAXSCRHEIGHT$) type mapline)

(deftype charfnarray vector (256))     ;  Array of function names to be used
                                       ;  in processing characters (0..255)
                                       ;  from font0.

(deftype bordchars byte-vector(6)) ;  Border characters returned from scrinit
                              ;  get put here.

(deftuple border   coord     ;  The x, y or z coord of this border element.
                   window    ;  Window owning this border. 
                   flag      ;  'top', 'left', 'right' or 'bot'
)



;   GLOBAL VARIABLES

(global w$ warray)     ;  The array of all currently created windows.

(global last-window-destroyed$)  ;  Window num of last window destroyed
                                 ;    by 'destroywindow'.

(global screenmap$ scrmap) ;  For position i,j o the screen, 
                           ;    screenmap$( i * SCRWIDTH$ + ) contains 
                           ;    the number of the window which is visible.

(global window0$ wtype) ;  Window 0 -- does not exist from the user's point
                        ;     of view, but makes the refresh function
                        ;     simpler.

(global ylist$)        ;  There are two border element tuples ('top' and 'bot')
                       ;     on this list for each currently created window.

(global wline-freelist$) ;  List of available wlines.

(global currw$ wtype)  ;  Currently selected window...
(global currwnum$)     ;      id number of currently selected window (1...)
(global currtop$)      ;      y-coord of top of window (1st header line)
(global currleft$)     ;      x-coord of left of window (incl border)
(global currwidth$)    ;      num chars in each line of window (incl borders)
(global currheight$)   ;      num lines in window (incl header and footer)
(global currx$)        ;      cursor position on currentline$ (1..currwidth$)
(global curry$)        ;      A suffix of the 'start' line list whose CAR
                       ;          is the current line (containing the cursor).
(global currline$ wline) ;        (Invariant: always = (car curr-y$))
(global currmapline$ mapline) ;   (NIL if the absolute mapping of currline 
                       ;           would be off the screen in the y-direction,
                       ;           else, this is the row of the scrmap on
                       ;           which the cursor currently rests (used to
                       ;           determine if the current char location is 
                       ;           visible.
(global currfont$)     ;      Font number for current window (for PUTC)
(global currstandout$) ;      0 if normal video, else 128 for inverse video.

(global putcfn$)       ;  Name of function to process the next character
                       ;      to be sent to PUTC
(global putcfont0fns$ charfnarray)
                       ;  Array of PUTC sub-function names which process
                       ;      font 0 characters. 
(global cursorcol$)    ;  Holds col character for a cursor addressing op

(global refr-x$)       ;  Coordinates of current refresh position, i.e., where
(global refr-y$)       ;      next refreshed character should be displayed. 

(global tempw$ wtype)  ;  Temporary window variable (efficiency).

(global mouseexists$)  ;  If t, then mouse device is available.
(global mousestate$)   ;  If MOUSEENABLED$, then mouse is enabled and 
                       ;      mouse events can be received through GETC.
                       ;     MOUSEDISABLED$, then mouse is alive, but
                       ;      no mouse events are returned from GETC.
                       ;     MOUSEEXPLICIT$, then mouse is enabled and
                       ;      controlled by the 3x3 keypad
                       ;     MOUSEOFF$, then the mouse is totally dead.
(constant MOUSEENABLED$ 1)
(constant MOUSEDISABLED$ 2)
(constant MOUSEEXPLICIT$ 3)
(constant MOUSEOFF$ 0)

(global mousecursor-x$)        ;-- Current location of mousecursor while
(global mousecursor-y$)        ;-- in MOUSEEXPLICIT mode.

(constant SHORT-VERT-AMT$ 1)   ;-- How far to move explicit mouse cursor
                               ;--   when (UP) or (DOWN) is entered
(constant SHORT-HORZ-AMT$ 1)   ;-- How far to move explicit mouse cursor
                               ;--   when (LEFT) or (RIGHT) is entered
(constant LONG-VERT-AMT$ 4)    ;-- How far to move explicit mouse cursor
                               ;--   when (LONG)(UP) or (LONG)(DOWN) entered
(constant LONG-HORZ-AMT$ 8)    ;-- How far to move explicit mouse cursor
                               ;--   when (LONG)(LEFT) or (LONG)(RIGHT) entered



;-- List of linear tries defining the command character sequences for
;-- each of the terminal-independent commands.
;-- Don't change the definition of (REFRESH) character sequence without also
;-- changing the ^Z handler in screen.c.

#+lispm
(constant FIXED-INCHAR-TRIE$
    '( ((323 nil (COPY)))           ;-- ^C  --> (COPY)
       ((329 nil (INS)))            ;-- ^I  --> (INS)
       ((331 nil (KILL)))           ;-- ^K  --> (KILL)
       ((324 nil (EXIT)))           ;-- ^D  --> (EXIT)
       ((141 nil (NL)))             ;-- CR  --> (NL)
       ((135 nil (DEL)))            ;-- RUBOUT  --> (DEL)
       ((332 nil (REFRESH)))        ;-- ^L  --> (REFRESH)
       ((341 nil (KILL-LINE)))      ;-- ^U  --> (KILL-LINE)
       ((336 nil (SNAPSHOT)))       ;-- ^P  --> (SNAPSHOT)
       ((322 nil (BRACKET)))        ;-- ^B  --> (BRACKET)
       ((340 nil (TRANSFORM)))      ;-- ^T  --> (TRANSFORM)
       ((343 nil (SHOW-PARENS)))    ;-- ^W  --> (SHOW-PARENS)
     )
)
#+franz
(constant FIXED-INCHAR-TRIE$
    '( ((3   nil (COPY)))           ;-- ^C  --> (COPY)
       ((9   nil (INS)))            ;-- ^I  --> (INS)
       ((11  nil (KILL)))           ;-- ^K  --> (KILL)
       ((4   nil (EXIT)))           ;-- ^D  --> (EXIT)
       ((13  nil (NL)))             ;-- ^M  --> (NL)
       ((127 nil (DEL)))            ;-- ^?  --> (DEL)
       ((12  nil (REFRESH)))        ;-- ^L  --> (REFRESH)
       ((21  nil (KILL-LINE)))      ;-- ^U  --> (KILL-LINE)
       ((16  nil (SNAPSHOT)))       ;-- ^P  --> (SNAPSHOT)
       ((2   nil (BRACKET)))        ;-- ^B  --> (BRACKET)
       ((20  nil (TRANSFORM)))      ;-- ^T  --> (TRANSFORM)
       ((23  nil (SHOW-PARENS)))    ;-- ^W  --> (SHOW-PARENS) 
     )
)

(deftype kp-array array (10))

(global key-pad$ kp-array)      ;-- keypad definitions as linear tries

(constant KP-CMDS$              ;-- positional command codes for keypad
    '(  (CMD)   (SEL)   (DOWN)  (MOUSE) (LEFT)
        (LONG)  (RIGHT) (DIAG)  (UP)    (REGION)
     )
)

(global inchar-map$)            ;-- The input char mapping table appropriate
                                ;--   for the current PRL terminal.
(global curr-inmap$)            ;-- Current subtree of 'inchar-map'.
(global curr-inpchars$)         ;-- The sequence of chars that have taken 
                                ;--   us to the value of 'curr-inmap'.
(global inbuf$)                 ;-- Input buffer used by 'getc'.


(constant MOUSEESC$ 20)         ;-- Signals the beginning of a mouse event.
(constant MOUSEFLAGS-SEL$ 2)    ;--   Mouse flag value for SEL button
(constant MOUSEFLAGS-REGION$ 8) ;--   Mouse flag value for REGION button
(constant MOUSEFLAGS-MENU$ 4)   ;--   Mouse flag value for MENU button

(global SCRHEIGHT)    ;  Number of lines on physical screen.
(global SCRWIDTH)     ;  Number of chars on each line (-1 since we never
                      ;  want to write in the bottom right position of the
                      ;  screen, since this causes automatic scrolling on
                      ;  a number of terminals).

(global MAXHEIGHT$)    ;  Maximum number of lines any window can have. 
(global MAXWIDTH$)     ;  Maximum number of chars per line.

(global borderchars$ bordchars)

(global VERTBAR$ )     ;  Used as left and right border character
(global HORZBAR$ )     ;  Used as top and bottom border character
(global TOPLEFT$ )
(global TOPRIGHT$ )
(global BOTLEFT$ )
(global BOTRIGHT$ )

;
;  I N I T W I N D O W S
;

(defun initwindows ()
  
    ;  Initialize for screen I/O and mouse.
    (<- borderchars$ (new bordchars))
    (Plet (retcode (scrinit borderchars$))
        (<- mouseexists$ t)
        (Pif (not (zerop retcode))  -->
            (Pif (>& retcode 15) -->
                (error '|INITWINDOWS: No keypad on terminal input device|)
             || (>& retcode 7)  -->
                (error '|INITWINDOWS: Unable to access interval timer.|)
             || (>& retcode 3)  -->
                (error '|INITWINDOWS: Unable to open terminal output device|)
             || (>& retcode 1)  -->
                (error '|INITWINDOWS: Unable to open terminal input device|)
             || t  -->
                ; Mouse open failed.
                (<- mouseexists$ nil)
             fi)
         fi)
    )
  
    ;-- Initialize for 'getc'.
  
    (<- mousestate$ MOUSEOFF$)
  
    ;-- Build list of linear tries, one for each keypad key.
    (Plet (tr-list nil)
        (Ploop   (local  i  0
                        tr nil
                        ch nil
                )
                (while (<& i 10))
                (do
                    ;-- Build a list of fixnums, consisting of the characters
                    ;-- sent by keypad key i, in reverse order.
                    (<- ch (get-keypad-def i 0))
                    (<- tr nil)
                    (Ploop   (local j 0)
                        (while (not (equal ch 0)))
                        (do
                            (<- tr (cons ch tr))
                            (<- j (1+ j))
                            (<- ch (get-keypad-def i j))
                        )
                    )
                    ;-- Construct a linear trie out of tr and add it to the list.
                    (<- tr-list (cons   (build-linear-trie
                                            (reverse tr)
                                            (nthelem (1+ i) KP-CMDS$)
                                        )
                                        tr-list
                                )
                    )
                    (<- i (1+ i))
                )
        )
       
        ;-- Construct a single trie out of the set of linear tries.
        (<- inchar-map$ (merge-linear-tries (append tr-list FIXED-INCHAR-TRIE$)))
    )
  
    (<- curr-inmap$ inchar-map$)
    (<- inbuf$ nil)
    (<- curr-inpchars$ nil)
  
    ;-- Copy border characters to global varaibles.
    (<- VERTBAR$  (sel borderchars$ (0)))
    (<- HORZBAR$  (sel borderchars$ (1)))
    (<- TOPLEFT$  (sel borderchars$ (2)))
    (<- TOPRIGHT$ (sel borderchars$ (3)))
    (<- BOTLEFT$  (sel borderchars$ (4)))
    (<- BOTRIGHT$ (sel borderchars$ (5)))
  
    ;  Initialize global variables 
  
    (<- w$ (new warray))
  
    (<- last-window-destroyed$ nil)
  
    (<- ylist$ nil)
  
    (<- currw$ nil)
  
    (<- wline-freelist$ nil)
  
    (<- screenmap$ (new scrmap))
  
    ;-- Initialize array of character handling function names for PUTC.  Most
    ;-- characters in font 0 are just plain old printing characters, viz. those
    ;-- greater than space (32) and are handled by PUTCNORMCH.
    (<- putcfn$ 'putcfont0$)
    (<- putcfont0fns$ (new charfnarray))
    (Ploop (local i 0)
        (while (<& i 256))
        (do
            (Pif (<& i 32) -->
                (<- (sel putcfont0fns$ (i)) 'putcspace$)
             || t -->
                (<- (sel putcfont0fns$ (i)) 'putcnormch$)
             fi)
            (<- i (1+ i))
        )
    )

    ;-- Enter functions for special characters.
    (<- (sel putcfont0fns$ (BS))    'putcbs$)
    (<- (sel putcfont0fns$ (TAB))   'putctab$)
    (<- (sel putcfont0fns$ (LF))    'putclf$)
    (<- (sel putcfont0fns$ (EEOS))  'putceeos$)
    (<- (sel putcfont0fns$ (CLEAR)) 'putcclear$)
    (<- (sel putcfont0fns$ (CR))    'putccr$)
    (<- (sel putcfont0fns$ (HOME))  'putchome$)
    (<- (sel putcfont0fns$ (ESC))   'putcesc$)
    (<- (sel putcfont0fns$ (FS))    'putcfs$)
    (<- (sel putcfont0fns$ (EEOL))  'putceeol$)
    (<- (sel putcfont0fns$ (RS))    'putcrs$)
    (<- (sel putcfont0fns$ (US))    'putcus$)

    ;-- Get screen parameters from lower level routines.
  
    (<- SCRHEIGHT (scrgetrows))
    (<- SCRWIDTH  (1- (scrgetcols)))

    (<- MAXHEIGHT$ SCRHEIGHT)
    (<- MAXWIDTH$ SCRWIDTH)

    ;-- Enter PRL state.
    (set-prl-tty 1)
  
    ;-- Create a window whose borders match those of the physical screen.
    ;-- This makes the boundary conditions in 'refresh' a lot easier to
    ;-- handle.  The line list is a circular list of 1 blanked-out wline.
    (createwindow 3 (- SCRHEIGHT 2) 1 (- SCRWIDTH 2))
    (Plet (soleline (list (get-a-wline$)))
        (initline$ 0 (car soleline) ^| | ^| | ^| | (1+ MAXLINELEN$) FONT0$)
        (<- (sel window0$ header) soleline)
        (<- (sel window0$ start) soleline) 
        (<- (sel window0$ end) soleline)
        (<- (cdr soleline) soleline)
    )
  
    ;-- Return 'nil' as result.
    nil
)



;
;   C R E A T E W I N D O W
;

(defun createwindow (y1 y2 x1 x2)

     ;  Creates a new window in the foreground at the specified location.
     ;  y1,x1 and y2,x2 are coordinates of the text lines of the
     ;  new window and do not include border or header lines.  These
     ;  coordinates must all be onscreen (0..SCRWIDTH$-1 in the x direction,
     ;  and 0..SCRHEIGHT$-1 in the y direction).
     ;  Returns the number of the new window created.
      (Plet (top   (min y1 y2)
            bot   (max y1 y2)
            left  (min x1 x2)
            right (max x1 x2)
           )

        (Plet (height (1+ (- bot top))
              width  (1+ (- right left))
              newwindow nil
             )

           ;-- Check parms onscreen and within min and max limits.
             (Pif (or (not (numberp top))
                     (not (numberp bot))
                     (not (numberp left))
                     (not (numberp right))
                     (minusp top)
                     (minusp bot)
                     (minusp left)
                     (minusp right)
                     (>& bot (1- SCRHEIGHT))
                     (>& right (1- SCRWIDTH))
                     (<& width MINWIDTH$)
                     (>& width MAXWIDTH$)
                     (<& height MINHEIGHT$)
                     (>& height MAXHEIGHT$)
                 )  -->
                 (error '|CREATEWINDOW: Improper parms:| 
                        (list top bot left right))
              fi)

           ;-- Try to use the window that was most recently destroyed.
              (Pif last-window-destroyed$  -->
                  (<- newwindow last-window-destroyed$)
                  (<- last-window-destroyed$ nil)
               fi)

           ;-- Find first nil entry in W$ array -- its index will be
           ;-- the number of the window to be created.  If none found,
           ;-- then too many windows around.
              (Ploop (local i 0)
                    (while (and (<& i MAXNUMWINDOWS)
                                (null newwindow)
                           )
                    )
                    (do (Pif (null (sel w$ (i)))  -->
                            (<- newwindow i)
                         fi)
                        (<- i (1+ i))
                    )
              )
              (Pif (not newwindow)  -->
                  (error '|CREATEWINDOW: Too many windows created.|)
               fi)

           ;-- Push all currently existing windows into the background
           ;-- by 1 notch. 
              (pushallback$)

           ;-- Create a new window and enter it into the W array.  Initialize
           ;-- window fields and line lists for window.
              (<- tempw$ (new wtype))
              (<- (sel w$ (newwindow)) tempw$)
              (<- (sel tempw$ wnumid) newwindow)
              (<- (sel tempw$ top) (- top 3))
              (<- (sel tempw$ bot) (+ bot 2))
              (<- (sel tempw$ left) (1- left))
              (<- (sel tempw$ right) (+ right 2))
              (<- (sel tempw$ depth) 0)
              (<- (sel tempw$ fontnum) FONT0$)
              (<- (sel tempw$ standout) 0)
              (<- (sel tempw$ cursor-x) 0)
              (<- (sel tempw$ cursor-y) 0)
              (<- (sel tempw$ elided) nil)
           ;-- Insert top and bottom borders onto y-list.
              (add-to-ylist$ tempw$)

           (Pif (not (zerop newwindow))  -->
               (initwlines$ tempw$ height (1+ width))
               ;-- Refresh part of screen covered by new window.
                  (refresh-part$ (sel tempw$ top) (1- (sel tempw$ bot))
                                 (sel tempw$ left) (1- (sel tempw$ right))
                  )
            || t  -->
               (<- window0$ tempw$)
               (clearscreen$)
            fi)
            
           ;-- Return 'newwindow' as result.
              newwindow

        )  ; let
      )  ; let
)  ; createwindow

(defun initwlines$ (window height width)

    ;  Build and initialize the list of lines (type wline) for the
    ;  window 'window'.  'width' is the linelength plus 1.

     (Plet (headl nil 
           endl  nil
           footl nil
          ) 

        ;-- Build and init footer line
           (<- footl (get-a-wline$))
           (initline$ (+ height 3) footl 
                      HORZBAR$ BOTLEFT$ BOTRIGHT$ width FONT0$)

        ;-- Build and init the line list from start to end 
           (<- endl (get-a-wline$))
           (initline$ (+ height 2) endl ^| | VERTBAR$ VERTBAR$ width FONT0$)
           (<- (sel (wtype window) end) (cons endl (list footl)))
           (<- (sel (wtype window) start)
               (Ploop (local numlines (1- height)
                            linelist (sel (wtype window) end)
                     )
                     (while (plusp numlines))
                     (do (<- linelist (cons (get-a-wline$) linelist))
                         (initline$ (+ numlines 2) (car linelist)
                                    ^| | VERTBAR$ VERTBAR$ width FONT0$)
                         (<- numlines (1- numlines))
                     )
                     (result linelist)
               )
           )

        ;-- Create and initialize the 3 header lines
           ; The 3rd header line.
            (<- headl (get-a-wline$))
            (initline$ 2 headl HORZBAR$ VERTBAR$ VERTBAR$ width FONT0$)
           ; The 2nd header line.
            (<- headl (cons (get-a-wline$)
                            (cons headl (sel (wtype window) start))
                      )
            )
            (initline$ 1 (car headl) ^| | VERTBAR$ VERTBAR$ width FONT0$)
           ; The 1st header line.
            (<- headl (cons (get-a-wline$) headl))
            (initline$ 0 (car headl) 
                       HORZBAR$ TOPLEFT$ TOPRIGHT$ width FONT0$)
            (<- (sel (wtype window) header) headl)
     )  ; let
)  ; initwline$

(defun initline$ (lineno line midch leftch rightch widp1 fontnum)

    (fillbyte-vector (sel (wline line) char) 0 (1+ widp1) midch)
    (fillbyte-vector (sel (wline line) attrib) 0 (1+ widp1) fontnum)
    (<- (sel (wline line) char (0)) leftch)
    (<- (sel (wline line) char (widp1)) rightch)
    (<- (sel (wline line) linenum) lineno)
)

(defun get-a-wline$ ()

    ;  Return a wline object.  Removes one from the freelist if possible,
    ;   otherwise creates a new one.

      (Pif wline-freelist$  -->
          (Plet (result (car wline-freelist$))
             (<- wline-freelist$ (cdr wline-freelist$))
             result
          )
       || t  -->  (new wline)
       fi)
)

(defun reclaim-wlines$ (lis)

    ;  Adds a list of wlines 'lis' to the freelist.
      (<- wline-freelist$ (append lis wline-freelist$))
)

(defun insert$ (elem lis)

    ;  Inserts a border tuple 'elem' onto the 'lis' priority queue on
    ;  the basis of the coord-of-border value.  Returns the list with the
    ;  newly inserted item. 

      (Pif (null lis)  -->
          (list elem)
       || (<& (coord-of-border elem) (coord-of-border (car lis)) )  -->
          (cons elem lis)
       || t  -->
          (cons (car lis) (insert$ elem (cdr lis)))
       fi)
)

(defun delete$ (window lis)

    ;  Deletes the first border tuple on 'lis' whose window-of-border
    ;  field matches 'window'.  Returns the list without the selected tuple.

      (Pif (null lis)  --> nil  
       || (eq window (window-of-border (car lis)))  -->
          (cdr lis)
       || t  -->
          (cons (car lis) (delete$ window (cdr lis)) )
       fi)
)

(defun add-to-ylist$ (window)
    
    ;  Add 'top' and 'bot' border-tuples for 'window' onto ylist.
    ;  If 'elided' for the window is not nil, then take 'bot' to be
    ;    'top'+2.

      (<- ylist$ (insert$ (border (sel (wtype window) top) 
                                  window
                                  'top
                          )
                          ylist$
                 )
      )
      (<- ylist$ (insert$ (border (Pif (sel (wtype window) elided)  -->
                                      (+ (sel (wtype window) top) 3)
                                   || t  -->
                                      (sel (wtype window) bot)
                                   fi)
                                  window
                                  'bot
                          )
                          ylist$
                 )
      )
)

(defun delete-from-ylist$ (window)

    ;  Deletes border tuples for 'window', both 'top' and 'bot' from ylist$.

      (<- ylist$ (delete$ window ylist$))
      (<- ylist$ (delete$ window ylist$))
)

(defun pushallback$ ()

    ;  Push all windows 'back' 1 notch into the screen by adding 1 to
    ;  their depth field.

      (for (x in ylist$)
           (when (eq (flag-of-border x) 'top))
           (do (<- (sel (wtype (window-of-border x)) depth) (1+ *-*)) )
      )
)


(defun validwindow$ (wnum)

    (Pif (and (numberp wnum)
             (plusp wnum)
             (<& wnum MAXNUMWINDOWS)
             (sel w$ (wnum))
        )  -->  t
     || t  -->  nil
     fi)
)


;
;   S E T E L I D E
;

(defun setelide (n elideval)

    ;  If elideval matches the current elide state of the window, then
    ;  no need to do anything.
    ;  Else set the elide state for window 'n' to elideval,
    ;  and refresh the area of the screen occupied by the window minus
    ;  the header lines.

      (Pif (not (validwindow$ n))  -->
          (error '|SETELIDE: Improper window number:| n)
       fi)

      ;-- Only do real work if the elide state for the window
      ;--  differs from elideval.
         (<- tempw$ (sel w$ (n)))

         (Pif (or (and (null elideval) (sel tempw$ elided))
                 (and elideval (null (sel tempw$ elided)))
             )  -->
             (<- (sel tempw$ elided) elideval)

             ;-- Delete and then add window to ylist.  This will set the
             ;--   new vertical border locations for refresh.  
                (delete-from-ylist$ tempw$)
                (add-to-ylist$ tempw$)
                (refresh-part$ (+ (sel tempw$ top) 3) (1- (sel tempw$ bot))
                               (sel tempw$ left) (1- (sel tempw$ right))
                )
          fi)
)



;
;   M O V E W I N D O W
;

(defun movewindow (n top left)

    ;  Moves the specified window so that the origin of the top left corner
    ;  is changed to 'top' and 'left'.  In addition, the window is
    ;  moved to the foreground and the screen is redrawn.

      ;-- Check parms.
         (Pif (not (validwindow$ n))  -->
             (error '|MOVEWINDOW: Improper window number:| n)
          fi)
         (Pif (or (not (numberp top))
                 (not (numberp left))
             )  -->
             (error '|MOVEWINDOW: Improper parms:| (list top left))
          fi)

      ;-- Save global vars for currently selected window (if any).
         (save-selected$)

      ;-- Adjust window boundaries.
         (<- tempw$ (sel w$ (n)))

         (Plet (oldtop (sel tempw$ top)
               oldleft (sel tempw$ left)
               oldbot (sel tempw$ bot)
               oldright (sel tempw$ right)
              )

            ;-- Adjust bot and right coords of window to reflect new position.
               (<- (sel tempw$ bot)
                   (+ *-* (- top (sel tempw$ top)))
               )
               (<- (sel tempw$ right)
                   (+ *-* (- left (sel tempw$ left)))
               )

            ;-- Replace top and left.
               (<- (sel tempw$ top) top)
               (<- (sel tempw$ left) left)

            ;-- Delete old window borders from ylist.
               (delete-from-ylist$ tempw$)

            ;-- Refresh area which used to be occupied by old window.
               (refresh-part$ oldtop
                              (Pif (sel tempw$ elided)  -->
                                  (+ oldtop 3)
                               || t  -->
                                  (1- oldbot)
                               fi)
                              oldleft
                              (1- oldright)
               )
         )

      ;-- Add window back onto ylist with new borders.
         (add-to-ylist$ tempw$)

      ;-- Pull window 'n' to foreground.
         (pullwindow n)

      ;-- Restore global vars from currently selected window (if any).
         (restore-selected$)
)

;
;   P U L L W I N D O W
;

(defun pullwindow (n)

    ;  Moves window n to the foreground and refreshes it.

     (Pif (not (validwindow$ n))  -->
         (error '|PULLWINDOW: Invalid window number.|)
      fi)
     (pushallback$)
     (<- tempw$ (sel w$ (n)))
     (<- (sel tempw$ depth) 0)
     (refresh-part$ (sel tempw$ top) 
                    (Pif (sel tempw$ elided)  -->
                        (+ (sel tempw$ top) 3)
                     || t  -->
                        (1- (sel tempw$ bot))
                     fi)
                    (sel tempw$ left)  
                    (1- (sel tempw$ right))
     )
)


;
;   P U S H W I N D O W
;

(defun pushwindow (n)

    ;  Moves window n to the background and refreshes it.

     (Pif (not (validwindow$ n))  -->
         (error '|PUSHWINDOW: Invalid window number.|)
      fi)
     (<- tempw$ (sel w$ (n)))
     (<- (sel tempw$ depth) (sel window0$ depth))
     (<- (sel window0$ depth) (1+ *-*))
     (refresh-part$ (sel tempw$ top) 
                    (Pif (sel tempw$ elided)  -->
                        (+ (sel tempw$ top) 3)
                     || t  -->
                        (1- (sel tempw$ bot))
                     fi)
                    (sel tempw$ left) 
                    (1- (sel tempw$ right))
     )
)



;
;   D E S T R O Y W I N D O W
;

(defun destroywindow (n)

    ;  Window 'n' is removed from the screen (and the window array, w$) 
    ;  and the screen is redrawn.

     (Pif (not (validwindow$ n))  -->
         (error '|DESTROYWINDOW: Improper window number.|)
      fi)

     (<- tempw$ (sel w$ (n)))

     ;-- Delete window from y-list, both top and bottom tuples.
        (delete-from-ylist$ tempw$)

     ;-- Reclaim all lines of the window.
        (reclaim-wlines$ (sel tempw$ header))

     ;-- Refresh area of screen where window used to be.
        (refresh-part$ (sel tempw$ top) 
                       (Pif (sel tempw$ elided)  -->
                           (+ (sel tempw$ top) 3)
                        || t  -->
                           (1- (sel tempw$ bot))
                        fi)
                       (sel tempw$ left) 
                       (1- (sel tempw$ right))
        )

     ;-- Delete from the w$ array.
        (<- (sel w$ (n)) nil)

     ;-- Save number of window just destroyed.
        (<- last-window-destroyed$ n)

     ;-- Check if destroying the currently selected window.
        (Pif (equal tempw$ currw$)  -->
            (<- currw$ nil)
         fi)

)


;
;   S E L E C T W I N D O W
;

(defun selectwindow (n)

    ;-- Verify specified window number is valid and then
    ;-- copy global variables for current window (if not nil) back into
    ;-- window structure for old window.  Then set variables for new window.

       (Pif (not (validwindow$ n))  -->
           (error '|SELECTWINDOW: Improper window number:| n)
        fi)

       ;-- Copy vars for currently selected window (if any).
          (save-selected$)

       (<- currw$ (sel w$ (n)))

       ;-- Copy vars for newly selected window.
          (restore-selected$)
)

(defun save-selected$ ()

    ;-- If a curently selected window exists, then copy the global versions
    ;-- of some important vars back into window structure for that window.
       (Pif currw$  -->
           ;-- Restore current window global variables to the data
           ;-- structure for the old window.
              (<- (sel currw$ cursor-x) (1- currx$))
              (<- (sel currw$ cursor-y) (- (sel currline$ linenum) 3))
              (<- (sel currw$ fontnum) currfont$)
              (<- (sel currw$ standout) currstandout$)
        fi)
)

(defun restore-selected$ ()

   ;-- If a currently selected window exists, then copy some important
   ;-- vars from the window structure to global versions of those vars.
      (Pif currw$  -->
          ;-- Restore global vars from current window structure.
             (<- currwnum$ (sel currw$ wnumid))
             (<- currtop$ (sel currw$ top))
             (<- currleft$ (sel currw$ left))
             (<- currwidth$ (- (sel currw$ right) (sel currw$ left) 2))
             (<- currheight$ (- (sel currw$ bot) (sel currw$ top) 4))
             (putcmovecursor$ (sel currw$ cursor-x) (sel currw$ cursor-y))
             (<- currfont$ (sel currw$ fontnum))
             (<- currstandout$ (sel currw$ standout))
      fi)
)



;
;   G E T C
;

(defun getc ()

   ;-- Get the next character from the input stream.

      (Pif (null currw$)  -->
          (error '|GETC: No window currently selected.|)
       fi)

      ;-- Get either... 
      ;--        a printing character (or space)
      ;--     or...
      ;--        a mouse event or special character, eg. (UP)
         (Ploop
              (local ch nil)
              (do
                 (Pif (null inbuf$)  -->
                     (get-a-char$)
                  fi)
      
                 (<- ch (car inbuf$))
                 (<- inbuf$ (cdr inbuf$))
              )
              (until (or (dtpr ch)
                         (and (>& ch BLANKMINUS1$) (< ch 256))
			 (is-LM-symbol-ch ch)
			 (is-lispmprl-bound-key ch)
                     )
              )
              (result (Pif (is-LM-symbol-ch ch) --> (code-LM-symbol-ch ch)
		       || (is-lispmprl-bound-key ch) --> (ch-of-lispmprl-bound-key ch)
		       || t --> ch fi))
         )

)


(defun get-a-char$()

   ;-- This routine is called when 'inbuf' is empty (null).
   ;-- Get at least one character of input into 'inbuf'.

      (Pif (equal mousestate$ MOUSEEXPLICIT$)  -->
          (<- inbuf$ (process-explicit-mouse$))
       || t  -->
          (<- inbuf$ (getc-logical$))
       fi)
      ;-- While the current character is (MOUSE), i.e., a request to
      ;-- enter explicit mouse mode, replace (MOUSE) in 
      ;-- 'inbuf' by the result of processing an explicit mouse (either
      ;-- a mouse event or if the mode was exited before an event was
      ;-- entered, the character right after leaving explicit mode).
         (Ploop (while (equal (car inbuf$) '(MOUSE)))
               (do
                 (<- inbuf$ (append (process-explicit-mouse$) (cdr inbuf$))) 
               )
         )
)

(defun getc-logical$()

   ;-- Gets a logical character (after translating multi-character
   ;-- sequences) or mouse event and returns it in a list.

      (Ploop
           (local ch           nil
                  char-logical nil
           )
           (while (null char-logical))
           (do
              (<- ch (scrrdchar))
              (Pif (listp ch)  -->  ;-- a BLIP from the 3600 mouse
                  (<- char-logical (process-mouseevent$ ch))
               || t  -->
                  ;-- Search in current level of 'inchar-map',
                  ;-- (= top level of 'curr-inmap') for ch.
                     (<- curr-inmap$ (assoc ch curr-inmap$))
                     (<- curr-inpchars$ (append1 curr-inpchars$ ch))
                     (Pif curr-inmap$  -->
                         (Pif (null (cadr curr-inmap$))  -->
                             ;-- Success - end of sequence - add
                             ;-- sequence of items from inchar-map
                             ;-- to the input buffer.  Reset current map
                             ;-- to top of search tree.
                                (<- char-logical (cddr curr-inmap$))
                                (<- curr-inmap$ inchar-map$)
                                (<- curr-inpchars$ nil)
                             ;-- If a (REFRESH) character is ever input,
                             ;-- perform a screen refresh and read another
                             ;-- character.
                                (Pif (equal char-logical '((REFRESH)))  -->
                                    (refresh)
                                    (<- char-logical nil)
                                 fi)
                          || t  -->
                             ;-- Somewhere in middle of sequence.
                             ;-- Save next level of map.
                                (<- curr-inmap$ (cdr curr-inmap$))
                          fi)
                      || t  -->
                         ;-- Not found.  Transfer all characters that
                         ;-- had been accumulated in looking for the
                         ;-- sequence.  Reset to top of search tree.
                            (<- char-logical curr-inpchars$)
                            (<- curr-inmap$ inchar-map$)
                            (<- curr-inpchars$ nil)
                      fi)
               fi)
           )
           (result char-logical)
      )
)


(defun process-mouseevent$(ch)

   ;-- If MOUSEENABLED$, returns a list whose only element is a
   ;-- six element list of the following items:
   ;--      1.   MOUSE-JUMP | MOUSE-SEL | MOUSE-MENU
   ;--      2.   abs x 
   ;--      3.   abs y
   ;--      4.   window number for window visible at location absx,absy
   ;--                 = 0 if no window visible at absx,absy
   ;--      5.   rel x -- The x coord of the event relative to text
   ;--                 position 0,0 of the window on which the event
   ;--                 appeared. (If not on any window, this is the 
   ;--                 same as the absolute x coord.)
   ;--      6.   rel y -- The y coord of the event relative to ... 
   ;--                 (same as for 5.)

      (Plet (event (Pmod (cadr ch) 256)
            absx  (cadddr ch)
            absy  (car (cddddr ch))
            wnum  nil
            ch    nil
           )
          (Pif (equal mousestate$ MOUSEENABLED$)  -->
              ;-- Read in flags and set first item of event.
                 (Pif (equal event 0) -->
                     (<- event '(MOUSE-SEL))
                  || (equal event 2) -->
                     (<- event '(MOUSE-JUMP))
                  || t  -->
                     (<- event '(MOUSE-MENU))
                  fi)

		 (<- absx (max left-pixel (min right-pixel absx)))
                 (<- absx (min (/ (+ 1 (- absx left-pixel)) char-width)
                               (- SCRWIDTH 1)
                          )
                 )
                 (<- event (append1 event absx))

		 (<- absy (max top-pixel (min bottom-pixel absy)))
                 (<- absy (min (/ (+ 2 (- absy top-pixel)) char-height)
                               (- SCRHEIGHT 1)
                          )
                 )
                 (<- event (append1 event absy))

                 ;-- Translate absx,absy into a window number
                 ;-- and relative x,y to be added on to the end of 
                 ;-- the event.
                    (<- wnum (sel screenmap$ (absy)(absx)))
                    (Pif (plusp wnum)  -->
                        (<- tempw$ (sel w$ (wnum)))
                        (<- absx (- absx (sel tempw$ left) 1))
                        (<- absy (- absy (sel tempw$ top) 3))
                     fi)

                    (<- event (append1 event wnum))
                    (<- event (append1 event absx))
                    (<- event (append1 event absy))
           fi)
          ;-- Return list of mouse event.
             (list event)
      )
)

(defun process-explicit-mouse$()

   ;-- Changes mouse state to explicit mouse mode (if not already in
   ;-- that mode).  Ignores all characters input while in this mode
   ;-- except for the 9 char pad
   ;--              (DIAG) (UP)   (REGION)
   ;--              (LEFT) (LONG) (RIGHT)
   ;--              (SEL)  (DOWN) (MOUSE)
   ;-- Exits
   ;--   when (SEL), (MOUSE), or (REGION) have been pressed to
   ;--   signal a mouse event, in which case the mouse event
   ;--   similar to the result of 'process-mouseevent' is returned
   ;--   in a list, eg. ((MOUSE-SEL...))
   ;-- or when (DIAG) is pressed to exit without signalling an event.
   ;--   In this second case, the character(s) immediately following the 
   ;--   (DIAG) will be returned in a list.

      (Pif (not (equal mousestate$ MOUSEEXPLICIT$))  -->
          ;-- Enter MOUSEEXPLICIT mode -- record current output cursor
          ;-- in   mousecursor-x, mousecursor-y
             (setmouse MOUSEEXPLICIT$)
             (explicit-mouse-mode t)
             (<- mousecursor-x$ (+ currleft$ currx$))
             (<- mousecursor-y$ (+ currtop$ (sel currline$ linenum)))
       fi)

      (Ploop (local event nil
                   ch    nil
            )
            (while (null event))
            (do
               (<- ch (getc-logical$))
               ;-- Note that if ch is a list of normal chars (i.e., not from
               ;-- the 3x3 keypad) it's OK to replace ch by its car since
               ;-- we are throwing them away anyway.
               (<- ch (car ch))
               (Ploop (local long-state nil)
                     (while (or (atom ch)
                                (not (memq (car ch) '(MOUSE SEL REGION DIAG)))
                            )
                     )
                     (do
                        (Pif (dtpr ch)  -->
                            (Pif (eq (car ch) 'LONG)  -->
                                (Pif long-state  -->
                                    (<- long-state 'VERYLONG)
                                 || t  -->
                                    (<- long-state 'LONG)
                                 fi)
                             || t  -->
                                (mouse-motion$ (car ch) long-state)
                                (<- long-state nil)
                             fi)
                         fi)
                        (<- ch (car (getc-logical$)))
                     )
               )

               ;-- Here, ch = (MOUSE) | (SEL) | (REGION) | (DIAG)
               (Pif (equal ch '(DIAG))  -->
                   ;-- Reset mouse cursor to output location.
                      (scrmvmouse (+ currleft$ currx$)
                                  (+ currtop$ (sel currline$ linenum))
                      )
                   ;-- Exit MOUSEEXPLICIT mode with the next character(s)
                   ;-- read.
                      (setmouse MOUSEENABLED$)
                      (explicit-mouse-mode nil)
                      (<- event (getc-logical$))
                || t  -->
                   ;-- Create a mouse event.
                      (Pif (equal ch '(MOUSE))  -->
                          (<- event '(MOUSE-MENU))
                       || (equal ch '(SEL))  -->
                          (<- event '(MOUSE-SEL))
                       || (equal ch '(REGION))  -->
                          (<- event '(MOUSE-JUMP))
                       fi)

                      (Plet (absx mousecursor-x$
                            absy mousecursor-y$
                            wnum nil
                           )
                          (<- event (append1 event absx))
                          (<- event (append1 event absy))
    
                          ;-- Translate absx,absy into a window number
                          ;-- and relative x,y to be added on to the end of 
                          ;-- the event.
                             (<- wnum (sel screenmap$ (absy)(absx)))
                             (Pif (plusp wnum)  -->
                                 (<- tempw$ (sel w$ (wnum)))
                                 (<- absx (- absx (sel tempw$ left) 1))
                                 (<- absy (- absy (sel tempw$ top) 3))
                              fi)
    
                             (<- event (append1 event wnum))
                             (<- event (append1 event absx))
                             (<- event (append1 event absy))
                      )
                   ;-- Return a list of the event.
                      (<- event (list event))
                fi)
            )
            (result event)
      )
)

(defun mouse-motion$ (direction long-state)

   ;-- Given direction = UP | DOWN | LEFT | RIGHT,
   ;-- move the mouse cursor in the direction specified by 
   ;-- the amount specified by long state.  If long-state
   ;-- is VERYLONG, then move cursor to top, bottom, leftend, or rightend
   ;-- of screen depending on direction.  If long-state is LONG,
   ;-- the cursor is moved by LONG-HORZ-AMT or LONG-VERT-AMT.
   ;-- Else the cursor is moved by SHORT-HORZ-AMT or SHORT-VERT-AMT.

      (Pif (eq direction 'UP)  -->
          (<- mousecursor-y$
              (max 0
                   (- mousecursor-y$
                      (Pif (eq long-state 'LONG)  --> LONG-VERT-AMT$
                       || (eq long-state 'VERYLONG)  --> SCRHEIGHT
                       || t  --> SHORT-VERT-AMT$
                       fi)
                   )
              )
          )

       || (eq direction 'DOWN)  -->
          (<- mousecursor-y$
              (min (1- SCRHEIGHT)
                   (+ mousecursor-y$
                      (Pif (eq long-state 'LONG)  --> LONG-VERT-AMT$
                       || (eq long-state 'VERYLONG)  --> SCRHEIGHT
                       || t  --> SHORT-VERT-AMT$
                       fi)
                   )
              )
          )

       || (eq direction 'LEFT)  -->
          (<- mousecursor-x$
              (max 0
                   (- mousecursor-x$
                      (Pif (eq long-state 'LONG)  --> LONG-HORZ-AMT$
                       || (eq long-state 'VERYLONG)  --> SCRWIDTH
                       || t  --> SHORT-HORZ-AMT$
                       fi)
                   )
              )
          )

       || (eq direction 'RIGHT)  -->
          (<- mousecursor-x$
              (min (1- SCRWIDTH)
                   (+ mousecursor-x$
                      (Pif (eq long-state 'LONG)  --> LONG-HORZ-AMT$
                       || (eq long-state 'VERYLONG)  --> SCRWIDTH
                       || t  --> SHORT-HORZ-AMT$
                       fi)
                   )
              )
          )
       fi)

      (scrmvmouse mousecursor-x$ mousecursor-y$)

)


;
;   G E T C U R S O R
;

(deftuple gottencursor
          y
          x
)

(defun getcursor (wnum)

   ;-- Return the current cursor value for window 'wnum' in the
   ;-- 'gottencursor' tuple.

      (Pif (equal wnum currwnum$)  -->
          ;-- Get cursor for selected window.
             (gottencursor (- (sel currline$ linenum) 3)
                           (1- currx$)
             )
       || t  -->
          ;-- Get cursor for non-active window.
             (Pif (validwindow$ wnum)  -->
                 (<- tempw$ (sel w$(wnum)))
                 (gottencursor (sel tempw$ cursor-y)
                               (sel tempw$ cursor-x)
                 )
              || t  -->
                 (error '|GETCURSOR: Improper window number:| wnum)
              fi)
       fi)
)


;
;   S E T M O U S E
;

(defun setmouse (state)

   ;-- If a change of mouse state is requested and mouse device exists,
   ;--        disable it for everything if state = MOUSEOFF$,
   ;--        set explicit control of mouse cursor if state = MOUSEEXPLICIT$,
   ;--        disable GETC returning events if state = MOUSEDISABLED$,
   ;--        enable it for everything if state = MOUSEENABLED$.

      (Pif (not (equal state mousestate$))  -->
          ;-- Caller wants a change of mouse state.
          (Pif mouseexists$  -->
              (Pif (equal state MOUSEOFF$)  -->
                  (scrmouse 0)
               || (equal state MOUSEEXPLICIT$)  -->
                  (scrmouse 2)
               || t  -->
                  ;-- Must be MOUSEENABLED$ or MOUSEDISABLED$.
                  (Pif (or (equal mousestate$ MOUSEOFF$) 
                          (equal mousestate$ MOUSEEXPLICIT$)
                      )  -->
                      (scrmouse 1)
                   fi)
               fi)
           || t  -->
              ;-- Here's the case where there is no mouse device --
              ;-- Only explicit control of mouse cursor allowed.
              (Pif (equal state MOUSEEXPLICIT$)  -->
                  (scrmouse 2)
               || t  -->
                  (scrmouse 0)
               fi)
           fi)
          (<- mousestate$ state)
       fi)
)



;
;   S E T R E V
;  

(defun setrev (revval)

    ;-- Set normal/reverse video for current window.

       (Pif (null currw$)  -->
           (error '|SETREV: No window currently selected.|)
        fi)
       (<- currstandout$ (Pif revval  -->  128
                          || t  -->  0
                          fi)
       )
)

;
;   S E T H E A D E R
;

(defun setheader (hdrstr)

    ;-- Assigns 'hdrstr' to the header line of the current window.

       (Pif (null currw$)  -->
           (error '|SETHEADER: No window currently selected.|)
        fi)

       ;-- Blank out the current header line.
          (fillbyte-vector (sel (wline (cadr (sel currw$ header))) char)
                      1 currwidth$ ^| |
          )

       ;-- Copy 'min(length(hdrstr),currwidth$)' chars from 'hdrstr'
       ;-- to the 2nd header line (in FONT0 and currstandout$).
          (Ploop (local
                     cnt      (min (length hdrstr) currwidth$)
                     remstr   hdrstr
                     headline (cadr (sel currw$ header))
                     i        1
                )
                (while (not (>& i cnt)))
                (do
                    (<- (sel (wline headline) char (i)) (car remstr))
                    (<- (sel (wline headline) attrib (i))
                        (+ FONT0$ currstandout$)
                    )
                    (<- i (1+ i))
                    (<- remstr (cdr remstr))
                )
          )

       ;-- Refresh the updated header line.
          (refresh-part$ (1+ currtop$) (1+ currtop$)
                         (1+ currleft$) (+ currleft$ currwidth$)
          )
)




;
;   P U T C
;

(defun putc (ch)

    ;-- Puts 'ch' into the current window structure (and possibly onto 
    ;-- the actual screen) at the current cursor location.
    ;-- Returns the curr-x value (0..width-2) after the character
    ;-- has been output.

       (Pif (null currw$)  -->
           (error '|PUTC: No window currently selected.|)
        fi)

       ;-- Note that this test is for efficiency -- the 'apply'
       ;-- will always work as well.
       (Pif (and (eq putcfn$ 'putcfont0$)
                (or (>& ch BLANKMINUS1$)
		    (is-coded-LM-symbol-ch ch))
           )  -->
           (putcnormch$ (Pif (is-coded-LM-symbol-ch ch) --> (decode-LM-symbol-ch ch)
			 || t --> ch
			 fi
			)
	   )
        || t  -->
           (apply putcfn$ (list ch))
        fi)

       ;-- Return the current x coord.
          (1- currx$)
)

(defun putcfont0$ (ch)

    ;-- Handle a char when currfont$ = FONT0.

       (apply (sel putcfont0fns$ (ch)) (list ch))
)

(defun putcfontn$ (ch)

    ;-- Handle char when currfont$ not = FONT0.

       (Pif (equal ch ESC)  -->
           (<- putcfn$ 'putcesc$)
        || t  --> 
           (putcnormch$ ch)
        fi)
)

(defun putcnormch$ (ch)

    ;-- Place ch into 'char' vector of currentline$ at position currx$.
       (<- (sel currline$ char (currx$)) ch)

    ;-- Set attribute corresponding to character.
       (<- (sel currline$ attrib (currx$)) (+ currfont$ currstandout$))

    ;-- Write ch to screen (if possible).
       (wrscrchar$ ch)

    ;-- Move logical cursor right 1 position -- physical cursor was taken
    ;-- care of by 'wrscrchar'.
       (<- currx$ (1+ currx$))
       (Pif (>& currx$ currwidth$)  -->
           (putccr$ CR)
           (putclf$ LF)
        fi)
)

(defun putcspace$ (ch)
  (declare (ignore ch))

    ;-- Handle a space char.
       (putcnormch$ SPACE)
)

(defun putcbs$ (ch)
  (declare (ignore ch))

    ;-- Handle a BS char.  Adjust currx$ left by 1 and then adjust physical
    ;-- cursor.

       (Pif (>& currx$ 1)  -->
           (<- currx$ (1- currx$))
        fi)
       (wrscrcursor$ (+ currleft$ currx$)
                     (+ currtop$ (sel currline$ linenum))
       )
)

(defun putctab$ (ch)
  (declare (ignore ch))

    ;-- Update currx$ to next tab location and then set screen cursor.

       (<- currx$ (1+ (* TABAMT$ 
                         (/ (+ currx$
                               (1- TABAMT$)
                            )
                            TABAMT$
                         )
                      )
                  )
       )
       (Pif (>& currx$ currwidth$)  -->
           (<- currx$ currwidth$)
        fi)
       (wrscrcursor$ (+ currleft$ currx$)
                     (+ currtop$ (sel currline$ linenum))
       )
)

(defun putccursdown$ (ch)
  ch

    ;-- Handle cursor down character.  Move cursor down if not already at 
    ;-- bottom line.

       (Pif (not (equal curry$ (sel currw$ end)))  -->
           (putcmovecursor$ (1- currx$) (- (sel currline$ linenum) 2))
        fi)
)

(defun putclf$ (ch)
  (declare (ignore ch))

    ;-- Handle linefeed character.
    ;-- Pif on last line of window, move up to line 0,
    ;-- else just move down 1 line.

       (Pif (equal curry$ (sel currw$ end))  -->
           ;-- Move to correct location on top line of window.
              (putcmovecursor$ (1- currx$) 0)
        || t  -->
           ;-- Move cursor down 1 line.
              (putcmovecursor$ (1- currx$) (- (sel currline$ linenum) 2))
        fi)
)

(defun putceeos$ (ch)
  (declare (ignore ch))

    ;-- Perform an EEOL for the current line.  Blank out all lines from
    ;-- the current + 1 to the last line of the window. 
    ;-- Then call refresh to write out the newly blanked area.

       (Plet (holdx currx$
             holdy (sel currline$ linenum)
            )
          ;-- Erase current line and move to the next.
             (putceeol$ EEOL)
             (putcmovecursor$ 0 (- holdy 2))

          ;-- Blank out lines from current+1 to the bottom line of window.
             (Ploop (while (not (eq curry$ (cdr (sel currw$ end)))))
                   (do
                       (fillbyte-vector (sel currline$ char) 1 currwidth$ SPACE) 
                       (fillbyte-vector (sel currline$ attrib) 1 currwidth$
                                         (+ FONT0$ currstandout$)
                       )
                       (putcmovecursor$ 0 (- (sel currline$ linenum) 2))
                   )
             )

          ;-- Now refresh newly blanked out area and reposition cursor.
             (refresh-part$ (+ currtop$ holdy 1) 
                            (+ currtop$ currheight$ 2)
                            (1+ currleft$)   
                            (+ currleft$ currwidth$)
             )
             (putcmovecursor$ (1- holdx) (- holdy 3))
       )
)

(defun putcclear$ (ch)
  (declare (ignore ch))
    ;-- Handle a clear char.  Blank out all lines of the current window.
    ;-- Do a partial refresh for the area of the screen occupied by the
    ;-- current window.  Then reposition the cursor at 0,0.

       (<- curry$ (sel currw$ start))
       (Ploop (local footl (cdr (sel currw$ end)))
             (do
                (<- currline$ (car curry$))
                (fillbyte-vector (sel currline$ char) 1 currwidth$ SPACE)
                (fillbyte-vector (sel currline$ attrib) 1 currwidth$
                              (+ FONT0$ currstandout$)
                )
                (<- curry$ (cdr curry$))
             )
             (until (eq curry$ footl))
       )
       (refresh-part$ (+ currtop$ 3) 
                      (- (sel currw$ bot) 2)
                      (1+ currleft$)  
                      (- (sel currw$ right) 2)
       )
       (putcmovecursor$ 0 0)
)

(defun putccr$ (ch)
  (declare (ignore ch))

    ;-- Handle a carriage return.  

       (<- currx$ 1)
       (wrscrcursor$ (1+ currleft$) (+ currtop$ (sel currline$ linenum)))
)

(defun putchome$ (ch)
  (declare (ignore ch))

    ;-- Handle a home character.

       (putcmovecursor$ 0 0)
)

(defun putcesc$ (ch)
  (declare (ignore ch))

    ;-- Handle esc sequences.
    ;-- For now, just output a blank.
       (putcnormch$ SPACE)
)

(defun putcfs$ (ch)
  (declare (ignore ch))

    ;-- Handle FS.  Move current cursor position right by 1.

       (<- currx$ (1+ currx$))
       (Pif (>& currx$ currwidth$)  -->
           (putccr$ CR)
           (putclf$ LF)
        || t  -->
           (wrscrcursor$ (+ currleft$ currx$)
                         (+ currtop$ (sel currline$ linenum))
           )
        fi)
)

(defun putceeol$ (ch)
  (declare (ignore ch))

    ;-- Handle EEOL.  Erase to end of line by writing blanks.  Then 
    ;-- reposition the logical (and physical) cursor.

       (Pif (not (>& currx$ currwidth$))  -->
           (Plet (absy (+ currtop$ (sel currline$ linenum))
                 blankcnt (- currwidth$ currx$ -1)
                )
              (fillbyte-vector (sel currline$ char) currx$ blankcnt SPACE)
              (fillbyte-vector (sel currline$ attrib) currx$ blankcnt
                                (+ FONT0$ currstandout$)
              )
              ;-- Write the blanks to the screen.
                 (refresh-part$ absy
                                absy 
                                (+ currleft$ currx$) 
                                (+ currleft$ currwidth$)
                 )

           )
        fi)
)

(defun putcrs$ (ch)
  (declare (ignore ch))

    ;-- Handle RS char -- x,y cursor addressing.
    ;-- Sequence should be   RS column row.
    ;-- Set up PUTC handler for next char to be a function which 
    ;-- saves the column address character.
       (<- putcfn$ 'putcsavex$)
) 

(defun putcsavex$ (ch)

    ;-- Save column address char and set up PUTC handler function to
    ;-- be one which does the actual cursor addressing.
       (<- cursorcol$ ch)
       (<- putcfn$ 'putcsavey$)
)

(defun putcsavey$ (ch)

    ;-- Reset PUTC handler to that for characters of FONT0
    ;-- and move the cursor -- BUT clamped to the window boundaries.

       (<- putcfn$ 'putcfont0$)
       (Plet (col (- cursorcol$ SPACE)
             row (- ch SPACE)
            )
          (putcmovecursor$ (Pif (minusp col)  -->  0
                            || (<& col currwidth$)  -->  col
                            || t  -->  (1- currwidth$)
                            fi)
                           (Pif (minusp row)  -->  0
                            || (<& row currheight$)  -->  row
                            || t  -->  (1- currheight$)
                            fi)
          )
       )
)

(defun putcus$ (ch)
  (declare (ignore ch))

    ;-- Handle US character.  Move 1 line up in the vertical direction
    ;-- as long as not at top of window.

       (Pif (not (eq curry$ (sel currw$ start)))  -->
           ;-- Move to current x location and current y - 1.
              (putcmovecursor$ (1- currx$) (- (sel currline$ linenum) 4) )
        fi)
)

(defun putcmovecursor$ (col row)

    ;-- Set currx$, curry$, currline$, currmapline$ 
    ;-- to logically reflect position col,row of the current window,
    ;-- and then move the physical cursor.
    ;-- Should be used mainly when vertical cursor motion is needed.

       (<- currx$ (1+ col))
       (<- curry$ (nthcdr row (sel currw$ start)))
       (<- currline$ (car curry$))
       (<- currmapline$ nil)
       (Plet (absy (+ currtop$ (sel currline$ linenum)))
           (Pif (and (not (minusp absy))
                    (<& absy SCRHEIGHT)
               )  -->
               (<- currmapline$ (sel screenmap$ (absy)))
            fi)
            (wrscrcursor$ (+ currleft$ currx$) absy)
       )
)


(defun wrscrctl$ (ch)

    (scrwrctl ch)
)

(defun wrscrcursor$ (x y)

    ;-- Position the physical screen cursor to location x,y.
    ;-- Clamp x,y to be the nearest boundary of the screen if either 
    ;-- of x or y is off screen.

       (scrmvcursor (Pif (minusp x)  -->  0
                     || (<& x SCRWIDTH)  -->  x
                     || t  -->  (1- SCRWIDTH)
                     fi)

                    (Pif (minusp y)  -->  0
                     || (<& y SCRHEIGHT)  -->  y
                     || t  -->  (1- SCRHEIGHT)
                     fi)
       )
)

(defun wrscrchar$ (ch)

    ;-- Write out the character 'ch' from position 'currx$' of the current line
    ;-- 'currentline$' if it's on screen and visible.
    ;-- Elseif updated cursor address will still be on screen then move
    ;-- cursor right 1 position (by writing an FS$ character).
    ;-- Else leave cursor alone.

       (Pif currmapline$  -->
           ;-- y-coord is on screen.
           (Plet (absx (+ currx$ currleft$))
              (Pif (and (not (minusp absx))
                       (<& absx SCRWIDTH)
                       (equal currwnum$ (sel currmapline$ (absx)))
                  )  -->
                  ;-- x-coord is on screen and position is visible.
                  (scrwrchar ch)
               || t  -->
                  ;-- Check Pif updated cursor addr will be on screen.
                     (<- absx (1+ absx))
                     (Pif (and (not (minusp absx))
                              (<& absx SCRWIDTH)
                         )  -->
                         (wrscrctl$ FS)
                      fi)
               fi)
           )
        fi)
)


;
;   R E F R E S H
;

(defun refresh ()

    ;  Redraws the entire screen.  (Don't write characters from background
    ;   window).

     (clearscreen$)
     (refresh$ 0 SCRHEIGHT 0 SCRWIDTH nil)
     (reset-cursor$)
)

(defun refresh-part$ (top bot left right)

    ;  Redraws the specified section of the screen.  

      (Pif (minusp top)   -->  (<- top 0)  fi) 
      (Pif (minusp left)  -->  (<- left 0) fi)
      (Pif (not (<& bot SCRHEIGHT))   -->  (<- bot (1- SCRHEIGHT))  fi)
      (Pif (not (<& right SCRWIDTH))  -->  (<- right (1- SCRWIDTH)) fi)

      (Pif (and (not (<& bot top))
               (not (<& right left))
          )  -->

          ;-- Remove window 0 (marker window) from the y-list.
             (delete-from-ylist$ window0$)

          ;-- Replace it on ylist with refresh coords.
             (<- (sel window0$ top) top)
             (<- (sel window0$ bot) (1+ bot))
             (<- (sel window0$ left) left)
             (<- (sel window0$ right) (1+ right))
             (add-to-ylist$ window0$)

          (refresh$ top (1+ bot) left (1+ right) t)

          ;-- Replace it on ylist with its original coords.
             (delete-from-ylist$ window0$)
             (<- (sel window0$ top) 0)
             (<- (sel window0$ bot) SCRHEIGHT)
             (<- (sel window0$ left) 0)
             (<- (sel window0$ right) SCRWIDTH)
             (add-to-ylist$ window0$)
       fi)

      ;-- Reset cursor to correct spot on selected window.
         (reset-cursor$)

      ;-- Result will be nil.
         nil
)

(defun reset-cursor$ ()

    ;-- If a window is currently selected, reset cursor location
    ;-- to currx$,curry$.

       (Pif currw$  -->
           (wrscrcursor$ (+ currleft$ currx$)
                         (+ currtop$ (sel currline$ linenum))
           )
        fi)
)



(defun refresh$ (refr-top refr-bot refr-left refr-right drawbg)

    ;  Redraws the current screen.
    ;  If 'drawbg' is true, then blank characters from window0 are output
    ;  in any area within the refresh rectangle not covered by a real window.

     (Plet (curr-ylist ylist$
           xlist      nil
          )
        (<- refr-y$ (coord-of-border (car curr-ylist)))
 
        (Ploop (while (<& refr-y$ refr-bot)
              )
              (do (Ploop (while (not (>& (coord-of-border (car curr-ylist))
                                              refr-y$
                               )    )
                        )
                        (do (Plet (window (window-of-border (car curr-ylist))
                                 )
                               (Pif (eq (flag-of-border (car curr-ylist))
                                       'top)  -->
                                   ;-- Insert left and right borders onto x-list
                                      (<- xlist (insert$
                                                   (border
                                                      (sel (wtype window) left)
                                                      window
                                                      'left
                                                   )
                                                   xlist
                                                )
                                      )
                                      (<- xlist (insert$
                                                   (border
                                                      (sel (wtype window) right)
                                                      window
                                                      'right
                                                   )
                                                   xlist
                                                )
                                      )
                                      (<- (sel (wtype window) cur-y)
                                          (sel (wtype window) header)
                                      )
                                || t  -->
                                   ;-- Delete left and right borders from xlist
                                      (<- xlist (delete$ window xlist))
                                      (<- xlist (delete$ window xlist))
                                fi)
                                (<- curr-ylist (cdr curr-ylist))
                            ) ;  let
                        ) ;  do
                  ) ;  loop
                  (Ploop (while (<& refr-y$ 
                                      (coord-of-border (car curr-ylist))
                               )
                        )
                        (do (Pif (<& refr-y$ refr-top)  -->
                                (down-all-1-line$ xlist)
                             || t  -->
                                (do-1-line$ xlist refr-left refr-right drawbg)
                             fi)
                            (<- refr-y$ (1+ refr-y$))
                        ) ;  do
                  ) ;  loop
              ) ;  do
        ) ;  loop
     ) ;  let
) ;  refresh


(defun down-all-1-line$ (lis)

    ;  For each window in a border tuple on lis, advance the current line 
    ;  pointer (cur-y) to the next line of text in the list of lines for 
    ;  that window.

      (for (x in lis)
           (when (eq (flag-of-border x) 'right))
           (do (<- (sel (wtype (window-of-border x)) cur-y)
                   (cdr *-*)
               )
           )
      )
)


(defun do-1-line$ (xlist refr-left refr-right drawbg)

    (Plet (curr-xlist xlist
          zlist      nil
         )
       (<- refr-x$ (coord-of-border (car curr-xlist)))

       (Ploop (while (<& refr-x$ refr-right)
             )
             (do (Ploop (while (not (>& (coord-of-border (car curr-xlist))
                                             refr-x$
                              )    )
                       )
                       (do (Plet (window (window-of-border (car curr-xlist))
                                )
                             (Pif (eq (flag-of-border (car curr-xlist))
                                     'left
                                 )  -->
                                 ;-- Put window on zlist.
                                    (<- zlist (insert$ 
                                                 (border
                                                    (sel (wtype window) depth)
                                                    window
                                                    'depth
                                                 )
                                                 zlist
                                              )
                                    )
                                    (<- (sel (wtype window) cur-x) 0)
                              || t  -->
                                 ;-- Delete from zlist.
                                    (<- zlist (delete$ window zlist))
                                    (<- (sel (wtype window) cur-y)
                                        (cdr *-*)
                                    )
                              fi)
                             (<- curr-xlist (cdr curr-xlist))
                           ) ;  let
                       ) ;  do
                 ) ;  loop
                 (Plet (diff (- (coord-of-border (car curr-xlist))
                               refr-x$
                            )
                      )
                    (Pif (and (not (<& refr-x$ refr-left)) 
                             (or drawbg
                                 (not (eq window0$ 
                                          (window-of-border (car zlist))
                                      )
                                 )
                             )
                        )  -->
                        ;-- Write out 'diff' characters
                        ;-- from text of first window on zlist at 'cur-y,cur-x' 
                        ;-- to screen at 'refr-y$,refr-x$'
                           (writechars$ (window-of-border (car zlist)) diff)
                     fi)
                    (<- refr-x$ (+ refr-x$ diff))
                    
                    ;-- Add diff to the 'cur-x' value of each window on the
                    ;-- zlist.
                       (for (x in zlist)
                            (do (<- (sel (wtype (window-of-border x)) cur-x)
                                    (+ *-* diff))
                            )
                       )
                 ) ;  let
             ) ;  do
       ) ;  loop
       (down-all-1-line$ curr-xlist)
    ) ;  let
) ; do-1-line$

(defun clearscreen$ ()

    ;-- Clear the contents of the physical screen. (Write a 'clear' char)
       (wrscrctl$ CLEAR)

    ;-- Initialize the screenmap to 0, ie., only window 0 is visible in
    ;-- all locations.
       (Ploop (local i 0)
             (while (<& i SCRHEIGHT))
             (do
                (fillbyte-vector (sel screenmap$ (i)) 0 SCRWIDTH 0)
                (<- i (1+ i))
             )
       )
)

(defun writechars$ (window numchars)

    ;--  Write to screen at refr-x$,refry$ 
    ;--  'numchars' characters from
    ;--  'window' at position cur-x of line (car cur-y).

      ;-- Set cursor to refr-x$,refr-y$.
         (wrscrcursor$ refr-x$ refr-y$)

      ;-- Now write the characters.
         (putbyte-vector (sel (wline (car (sel (wtype window) cur-y))) char)
                    (sel (wtype window) cur-x)
                    numchars
         )

      ;-- Fill the screenmap$ at refr-x$,refr-y$ with 'numchars' of the 
      ;-- current window id number.
         (fillbyte-vector (sel screenmap$ (refr-y$))
                     refr-x$
                     numchars
                     (sel (wtype window) wnumid)
         )
)

;-- trie := (branch ... branch)                         ;linear trie: (branch)
;-- branch := (# branch ... branch) | (# nil (code))    ;linear branch: (# branch)

;-- Merge a list of linear tries into a single trie.
(defun merge-linear-tries (tr-list)
    (Pif (null tr-list) --> nil
     || t --> (insert-linear-trie (car tr-list) (merge-linear-tries (cdr tr-list)))
     fi)
)

;-- Insert a linear trie into a trie.
(defun insert-linear-trie (lt tr)
    (Pif (null tr) --> lt
     || (equal (caar lt) (caar tr)) -->
        (cons (insert-branch (car lt) (car tr)) (cdr tr))
     || t --> (cons (car tr) (insert-linear-trie lt (cdr tr)))
     fi)
)

;-- Insert one branch into another, returning a branch.
;-- Note: br1 must be a branch of a linear trie.
(defun insert-branch (br1 br2)
    (Pif (null (cadr br2)) --> (error '|insert-branch: prefix of insertion exists|)
     || (null (cadr br1)) --> (error '|insert-branch: insertion is prefix of entry|)
     || t --> (cons (car br1) (insert-linear-trie (cdr br1) (cdr br2)))
     fi)
)

;-- Build a linear trie from a list of fixnums and a command code.
(defun build-linear-trie (cl code)
    (list (build-linear-branch cl code))
)
;-- Build a linear branch from a list of fixnums and a command code.
(defun build-linear-branch (cl code)
    (Pif (equal (length cl) 1) --> (list (car cl) 'nil code)
     || t --> (list (car cl) (build-linear-branch (cdr cl) code))
     fi)
)

