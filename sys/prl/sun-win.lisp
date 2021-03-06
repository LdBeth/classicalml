;;; -*- Package: Nuprl; Base: 10; Syntax: Common-lisp -*-


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


;;; Provides the necessary support for Prl to use SunTools windows.  The
;;; interface is at the level of win.lisp.  This file obsoletes win.lisp,
;;; window.lisp and the primitive screen functions of zprlfuncs.lisp.


;;; All panes (all windows created by prl) have viewports
;;; whose position-x, position-y, width, and height are an integral
;;; number of characters (in the current fixed-width font).


(proclaim '(special lib-window cmd-window$ display-message-window))

(defvar *nuprl-frame-created-p* nil
  "The main nuprl frame (the root viewport) has already been created.")
(defvar *allocated-panes* nil
  "The panes (children of the frame) that prl is currently using.")
(defvar *free-panes* nil
  "The panes (children of the frame) that prl is currently not using")	
(defvar *frame-input-stream* nil
  "An input stream for window operation mouse-clicks.")
(defvar *help-window* nil
  "A window containing information on the use of the mouse and keyboard")

(defvar *selected-window* nil
  "The currently selected (for input and output) nuprl pane.")
(defvar *selected-width* 0
  "The width (in chars) of the selected pane.")
(defvar *selected-height* 0
  "The height (in chars) of the selected pane.")

(defvar *char-width* 0
  "The width of a character in the nuprl character style in pixels.")
(defvar *line-height* 0
  "The height of a line (a character and the vsp) in pixels.")
(defvar *baseline-height* 0
  "The baseline height of the current font.")

(defvar *snapshot-buffer-width* 140)
(defvar *snapshot-buffer-height* 60)
(defvar *snapshot-buffer*  ;each row represents a row of the window being snapshotted
	(make-array `(,*snapshot-buffer-height* ,*snapshot-buffer-width*)
		    :element-type 'ichar
		    :initial-element *ispace*
		    :adjustable t))
(defvar *snapshot-file* nil
  "The file to which snapshots are appended.")
(defvar *snapshot-mode-p* nil
  "Certain output to a nuprl pane will also be sent to *snapshot-buffer*.")

(defvar *current-prompt* nil
  "The current prompt string for Nuprl's command window")

;;; When in keypad mode, the nine keys U-I-O-J-K-L-M-,-. are interpreted
;;; as a keypad.  A keyboard character not in the keypad terminates
;;; keypad-mode and is interpreted normally.  Mouse clicks do not
;;; terminate keypad-mode and are interpreted normally.  The character M
;;; terminates keypad-mode and is discarded.  Keypad-mode is entered
;;; with ^Q (#\DC1).
(defvar *keyboard-in-keypad-mode-p* nil
  "Input from the keyboard is being interpreted as keypad input.")

;; Help message list - up to 35 lines of 60 characters each telling user
;; how to interact with the system
(defconstant *help-message-list*
	     '("Key assignments:"
	       "  arrow keys (R8,R10,R12,R14) are arrows;"
	       "  ^A is LONG; ^D exits edit window; ^Z is COMMAND"
	       "  ^Q is ENTER-KEYPAD-MODE; ^C is COPY; ^S is SEL;"
	       "  TAB and ^I are INS; ^K is KILL; ^U kills the input line;"
	       "  ^B toggles bracket mode; ^T for transformation tactic."
	       ""
	       "Special characters:"
	       "  Type ESC followed by alphabetic character. E.g.:"
	       "  <ESC>a gives ; <ESC>b gives . The full list:"
	       "  c: d: e: f: g: h: i:	 j:nothing k:"
	       "  l: m:
 n: o: p: q: r: s: t: u: v:"
	       "  w: x: y: z: {: }: \\: ^: _: `: " 
	       ""
	       "Mouse buttons:"
	       "  Left - SEL (select);"
	       "  Middle - JUMP;"
	       "  Right - menu of operations on the window under the "
               "          mouse (menu items described below)."
	       ""
	       "Menu items:"
	       "  Move - left-click the mouse to select the new"
	       "         upper-left corner for the window."
	       "  Shape - left-click for the new upper-left corner and "
	       "          then for the new bottom-right corner."
	       "  Bury - bury the window."
	       "  Select - bring up a menu of windows to select from."
	       "  Snapshot - snapshot the window to a file (default is"
               "             ~/snapshot.text).  To name another file, use"
               "             the ML function set_snapshot_file."
	       "  Refresh - redraw the window."
	       "  Refresh All - redraw all windows."
	       "  Help - put up this window.  Click left button to continue."
	       ""
	       "CLICK ON LEFT BUTTON TO DELETE WINDOW AND CONTINUE"
	       ))


;;; Characters treated specially by the system.  Typing any of these
;;; characters results in the associated thing being put in the input
;;; stream.  (Note: Sun control characters are ascii 0-31).
(defconstant *prl-special-characters*
	     '((#\ETX . (COPY))        (#\HT . (INS))
	       (#\VT . (KILL))         (#\EOT . (EXIT))
	       (#\Return . (NL))       (#\Rubout . (DEL))
	       (#\NAK . (KILL-LINE))   (#\SUB . (CMD))
	       (#\STX . (BRACKET))     (#\DC4 . (TRANSFORM))
	       (#\SOH . (LONG))        (#\DC3 . (SEL))))

(defconstant *prl-escape-characters*
	     '((#\A . (UP))	(#\B . (DOWN))
	       (#\C . (RIGHT))	(#\D . (LEFT))))

(defconstant *prl-keypad-characters*
	     '((#\u . (DIAG))  (#\i . (UP))   (#\o . (REGION))
	       (#\j . (LEFT))  (#\k . (LONG)) (#\l . (RIGHT))
	       (#\m . (SEL))   (#\, . (DOWN)) #|(#\. . (MOUSE))|#))

(defconstant *enter-keypad-mode-character* #\DC1)	;^Q
(defconstant *exit-keypad-mode-character* #\.)

(defvar *window-op-menu* nil
  "The menu for choosing window operations.
This is a momentary window hacking menu.")

(defvar *window-op-item-list*
	`(("Move" . move-window)
	  ("Shape" . reshape-window)
	  ("Bury" . bury-window)
	  ("Select" . select-window-from-menu)
	  ("Snapshot" . snapshot-window)
	  ("Refresh". refresh-window)
	  ("Refresh All" . refresh-all)
	  ("Help" . help-window)
	  ))

(defvar *select-window-menu* nil
  "The menu for selecting another pane.
This is a dynamic momentary menu.")

(defvar *selectable-windows-item-list* nil
  "The item list of all the selectable Nuprl panes")


(proclaim '(inline x-pixelate y-pixelate x-unpixelate y-unpixelate))
(defun x-pixelate (x-distance-in-chars)
  (* x-distance-in-chars *char-width*))
(defun y-pixelate (y-distance-in-chars)
  (* y-distance-in-chars *line-height*))
(defun x-unpixelate (x-distance-in-pixels)
  (truncate x-distance-in-pixels *char-width*))
(defun y-unpixelate (y-distance-in-pixels)
  (truncate y-distance-in-pixels *line-height*))

(defparameter *default-frame-width* 120)
(defparameter *default-frame-height* 60)

(defun window-equal (w1 w2) (equal w1 w2))

;;; Find a suitable font, set font-determined parameters, and
;;; create the Nuprl frame.
(defun create-frame ()
  (let ((init-file (merge-pathnames *init-file-name*
				    (user-homedir-pathname))))
    (when (probe-file init-file) (load init-file)))
  (when (and (not (windows:find-font "CPTFONT"))
	     (open "sys/cptfont.font" :direction :probe))
    (windows:load-font "sys/cptfont.font"))
  (setf windows:*default-font*
	(or (windows:find-font "CPTFONT") windows:*default-font*))
  (setf *line-height* (windows:font-height windows:*default-font*)
	*char-width* (or (windows:font-fixed-width windows:*default-font*)
			 (error "windows:*default-font* must be a fixed-width font."))
	*baseline-height* (windows:font-baseline windows:*default-font*))
  (windows:initialize-windows
    :label "Nuprl"
    :height (y-pixelate *default-frame-height*) 
    :width (x-pixelate *default-frame-width*))
  (setf SCRHEIGHT (- (window-height (windows:root-viewport))
		     2)	; subtract 2 so we don't cover the who line
	SCRWIDTH (window-width (windows:root-viewport)))
  (setf *frame-input-stream* (windows:make-mouse-input-stream
			       :queue-mouse-events-p t))
  (setf (windows:keyboard-input) *frame-input-stream*
	(windows:mouse-input) *frame-input-stream*)
  (values))

(defun clear-frame ()
  (mapc #'destroyw (copy-list *allocated-panes*)))

(defun reset ()
  (when *nuprl-frame-created-p* 
    (windows:leave-window-system))
  (setf *allocated-panes* nil
	*free-panes* nil
	*nuprl-frame-created-p* nil)
  (reset-prl))

(defun initw ()
  (if *nuprl-frame-created-p*
      (clear-frame)
      (progn (create-frame)
	     (setf *nuprl-frame-created-p* t)
	     (setf *window-op-menu*
		   (windows:make-pop-up-menu *window-op-item-list*))
	     (setf *help-window*
		   (windows:make-window
		     :x (x-pixelate 30) :y (y-pixelate 15)
		     :width (x-pixelate 61) :height (y-pixelate 40)
		     :title " Help" :activate nil :operation boole-1))
	     (let* ((*selected-window* *help-window*)
		    (*selected-height* (window-height *help-window*))
		    (*selected-width* (window-width *help-window*)))
	       (windows:with-fast-drawing-environment
		 (dolist (i *help-message-list*)
		   (write-string-to-current-window i)
		   (putnl))))))
  (setf *selectable-windows-item-list* nil)
  (values))

(defun allocate-pane ()
  (let ((pane (or (pop *free-panes*)
		  (windows:make-window :operation boole-1
				       :x 10 :y 10 
				       :inside-width 10 :inside-height 10
				       :activate nil
				       :title ""))))
    (push pane *allocated-panes*)
    pane))

(defun deallocate-pane (pane)
  (push pane *free-panes*)
  (remove pane *allocated-panes*))

(defun createw (top bottom left right &key (library nil) (allow-shift nil))
  (declare (ignore allow-shift))
  (let ((pane (allocate-pane)))
    (let* ((inside (windows:window-inside-region pane))
	   (outside (windows:viewport-screen-region pane))
	   (inc-w (- (windows:region-width outside)
		     (windows:region-width inside)))
	   (inc-h (- (windows:region-height outside)
		     (windows:region-height inside))))
      (windows:reshape-viewport
	pane
	:x (- (x-pixelate left) (truncate inc-w 2))
	:y (- (y-pixelate top) (- (windows:region-origin-y inside)
				  (windows:region-origin-y outside)))
	:width (+ inc-w (x-pixelate (1+ (- right left))))
	:height (+ inc-h (y-pixelate (1+ (- bottom top)))))
      (setf (windows:stream-x-position pane) 0
	    (windows:stream-y-position pane) *baseline-height*)
      (unless library (push pane *selectable-windows-item-list*))
      (windows:expose-viewport pane)
      (windows:activate-viewport pane)
      pane)))

(defun destroyw (window)
  ;; Kill a window.  It is removed from the list of candidates for selection and made
  ;; inactive so that it can be reused.
  ;; Clear the window so that the next use won't be surprised by the contents.
  (windows:clear-bitmap window)
  (setf (windows:window-title window) "")
  (windows:deactivate-viewport window)
  (deallocate-pane window)
  (setf *selectable-windows-item-list*
	(remove window *selectable-windows-item-list*)))

(defun changesizew (w y1 y2 x1 x2)
  (declare (ignore w y1 y2 x1 x2))
  ;; A stub.
  nil)

;; rle
(defun pane-at-point (x y)
  (let ((pane (windows:viewport-at-point x y)))
    (when (and pane
	       (member pane *allocated-panes*))
      pane)))
      
(defun window-width (w)
  (x-unpixelate (windows:region-width (windows:window-inside-region w))))

(defun window-height (w)
  (y-unpixelate (windows:region-height (windows:window-inside-region w))))

(defun getw-top (w)
  (y-unpixelate (windows:region-origin-y (windows:window-inside-region w))))

(defun getw-bot (w)
  (1- (+ (getw-top w) (window-height w))))

(defun getw-left (w)
  (x-unpixelate (windows:region-origin-x (windows:window-inside-region w))))

(defun getw-right (w)
  (1- (+ (getw-left w) (window-width w))))

(defun move-cursor (x y)
  (setf (windows:stream-x-position *selected-window*)
	(x-pixelate x))
  (setf (windows:stream-y-position *selected-window*)
	;; Characters are drawn on the screen so that the
	;; starting y-position line up with the character's
	;; baseline.
	(+ *baseline-height* (y-pixelate y))))

;;; Used by prl.
(defun movecursor (x y) (move-cursor y x))

(defun selectw (window)
  (windows:expose-viewport window)
  (setf *selected-window* window)
  (setf *selected-width* (window-width *selected-window*))
  (setf *selected-height* (window-height *selected-window*)))

(defun breakdown-mouse (mouse-char func)
  (cond
    ((char= #\mouse-left-down mouse-char) (funcall func 'left 'down))
    ((char= #\mouse-left mouse-char) (funcall func 'left 'button))
    ((char= #\mouse-left-up mouse-char) (funcall func 'left 'up))
    ((char= #\mouse-right-down mouse-char) (funcall func 'right 'down))
    ((char= #\mouse-right mouse-char) (funcall func 'right 'button))
    ((char= #\mouse-right-up mouse-char) (funcall func 'right 'up))
    ((char= #\mouse-middle-down mouse-char) (funcall func 'middle 'down))
    ((char= #\mouse-middle mouse-char) (funcall func 'middle 'button))
    ((char= #\mouse-middle-up mouse-char) (funcall func 'middle 'up))))


(defun prl-mouse-p (m)
  (when (consp m)
    (eql (first m) 'mouse)))

(defun prl-mouse-button (m)
  (second m))

(defun prl-mouse-x (m)
  (third m))

(defun prl-mouse-y (m)
  (fourth m))

;;; 
;;;  when a mouse button is clicked, three events are queued
;;;  in seemingly arbitrary order. 
;;;  to prevent any problems with dangling mouse events
;;;  these functions insure that all events related to a mouse
;;;  click are received before proceeding to act on that click.
;;;

(defun prl-read-any-no-hang ()
  (let ((input (windows:read-any-no-hang)))
    (when input
      (prl-read input))))

(defun prl-read-any ()
  (do ((ch  (prl-read (windows:read-any))
	    (prl-read (windows:read-any))))
      (ch ch)))

(defun prl-read (input)
  (if (windows:mouse-event-p input)
      (unless (eq #\mouse-moved (windows:mouse-event-char input))
	(let ((count 0)
	      (mode nil)
	      (mouse-x 0)
	      (mouse-y 0))
	  (breakdown-mouse (windows:mouse-event-char input)
			   #'(lambda (which what)
			       (declare (ignore what))
			       (setf mode which)
			       (incf count)
			       (setf mouse-x windows:*mouse-x*)
			       (setf mouse-y windows:*mouse-y*)))
	  (do ()
	      ((= 3 count) (list 'mouse mode mouse-x mouse-y))
	    (let ((event (windows:read-any)))
	      (when (windows:mouse-event-p event)
		(breakdown-mouse 
		 (windows:mouse-event-char event)
		 #'(lambda (which what)
		     (declare (ignore what))
			 (incf count))))))))
      input))

(defun read-char-from-current-window ()
  (invert-text-cursor)
  (let ((x (windows:stream-x-position *selected-window*))
	(ch (prl-read-any)))
    (when (eql x (windows:stream-x-position *selected-window*))
      (invert-text-cursor))
    ch))

(defun getchr ()
  (windows:with-mouse-methods-preempted *selected-window*
    (do ((ch (read-char-from-current-window)
	     (read-char-from-current-window)))
	(nil)
      (when (setf ch (if (prl-mouse-p ch)
			 (process-mouse ch)
			 (process-normal-or-keypad ch)))
	(return ch)))))

(defun process-normal-or-keypad (ch)
  (if *keyboard-in-keypad-mode-p*
      (let ((ch2 (cdr (assoc ch *prl-keypad-characters* :test #'char=))))
	(or ch2
	    (setf *keyboard-in-keypad-mode-p* nil)
	    (and (char/= ch *exit-keypad-mode-character*)
		 (process-normal ch))))
      (process-normal ch)))

 (defun process-normal (ch)
  ;; Process a normal character.  If it a special character return its definition.
  ;; Otherwise if it has any bits set, refuse it.
  (cond ((char= ch *enter-keypad-mode-character*)
	 (setf *keyboard-in-keypad-mode-p* t)
	 nil)
	((char-equal ch #\ESC)
	 (let ((ch2 (prl-read-any)))
	   (cond
	     ((prl-mouse-p ch2) (process-mouse ch2))
	     ((char-equal #\[ ch2) (process-esc))
	     (t (char->ichar (code-char (logand (char-code ch2) 31)))))))
	((cdr (assoc ch *prl-special-characters* :test #'char-equal)))
	((not (zerop (char-bits ch))) nil)
	(t (char->ichar ch))))


(defun process-esc ()
  ;; Read either a number followed by 'z' or a single letter & decode it
  (let ((ans
	  (do ((ch (prl-read-any)
		   (prl-read-any))
	       (value 0))
	      ((not (digit-char-p ch))
	       (unless (prl-mouse-p ch)
		 (if (char-equal ch #\z) value (char-upcase ch))))
	    (setq value (+ (* 10 value) (digit-char-p ch))))))
    ;; the check for prl mouse was added to catch and ignore stray mouse events.
    ;; the rest of it is somewhat nonsensical, if a number is input then it 
    ;; can never be used? I don't know why its here so I'll leave it. rle 4/26/89
    (cdr (assoc ans *prl-escape-characters* :test #'eql))))

(defun process-mouse (event)
  ;; Process a mouse character.  If it is a Right down do menu processing.
  ;; If any other mouse down is seen, expose the window under the mouse.
  ;; On mouse up return blip of the form (type window x y)  where type is one of
  ;; MOUSE-SEL or MOUSE-JUMP, and x,y are relative to the inside of the window.
  (let ((win (pane-at-point (prl-mouse-x event) 
			    (prl-mouse-y event))))
    ;; pane-at-point returns nil if root was hit.
    (case (prl-mouse-button event)
      ('left
       (when win
	 (windows:expose-viewport win)
	 (mouse-sel-jump win event 'MOUSE-SEL)))
      ('middle
       (when win
	 (windows:expose-viewport win)
	 (mouse-sel-jump win event 'MOUSE-JUMP)))
      ('right
       (mouse-menu-process win)))))

(defun wait-for-left-click ()
  (do ((event (prl-read-any) (prl-read-any)))
      ((and (prl-mouse-p event)
	    (eql 'left (prl-mouse-button event))))))
  
  (defun mouse-sel-jump (win event type)
    ;; Return a PRL blip with the window coordinates
    (let ((x (prl-mouse-x event))
	  (y (prl-mouse-y event)))
      (unless (or (eql win *selected-window*)
		  (eql win lib-window))
	(selectw win))
      (list type win
	    (- (x-unpixelate x) (getw-left win))
	    (- (y-unpixelate y) (getw-top win)))))
  
  
;;; Select and execute an operation from the menu
(defun mouse-menu-process (win)
  (let ((op (unwind-protect
		 (progn
		   (setf (windows:mouse-input-stream-queue-mouse-events-p 
			  (windows:mouse-input))
			 nil)
		   (windows:pop-up-menu-choose *window-op-menu*))
	      (setf (windows:mouse-input-stream-queue-mouse-events-p
		     (windows:mouse-input))
		    t))))
      
    ;; return result of op execution.
    (if op
	(funcall (symbol-function op) win)
	nil)))
  
  
  
(defun select-window-from-menu (win)
  ;; Put up the menu of selectable windows and select the result.  Called from the
  ;; window operations menu.
  (declare (ignore win))
  (let ((window (unwind-protect
		     (progn
		       (setf (windows:mouse-input-stream-queue-mouse-events-p 
			      (windows:mouse-input))
			     nil)
		       (windows:pop-up-menu-choose
			(windows:make-pop-up-menu 
			 (map 'list #'(lambda (x) (cons (windows:window-title x) x))
			      *selectable-windows-item-list*))))
		  (setf (windows:mouse-input-stream-queue-mouse-events-p 
			 (windows:mouse-input))
			t))))
    (if window
	(progn
	  (selectw window)
	  ;; Make a fake blip so that the upper level of the system will
	  ;; know the window has been selected.
	  `(MOUSE-JUMP ,window 0 0))
	nil)))
  
  
(defun rubber-window-til-left-click (echo-func)
  (do ((event (prl-read-any-no-hang)
	      (prl-read-any-no-hang)))
      ((and (prl-mouse-p event) 
	    (eql 'left (prl-mouse-button event))))
    (funcall echo-func
	     (x-unpixelate windows:*mouse-x*)
	     (y-unpixelate windows:*mouse-y*))))
    
(defun move-window (w)
  (when (and w
	     (not (eql w (windows:root-viewport))))
    (windows:with-mouse-documentation
	("left click to place left top corner")
      (rubber-window-til-left-click
       #'(lambda (mouse-x mouse-y)
	   (let ((good-x (cond
			   ((< mouse-x 0) 0)
			   ((> (+ mouse-x (window-width w)) SCRWIDTH)
			    (- SCRWIDTH (window-width w)))
			   (t mouse-x)))
		 (good-y (cond
			   ((< mouse-y 0) 0)
			   ((> (+ mouse-y (window-height w)) SCRHEIGHT) 
			    (- SCRHEIGHT (window-height w)))
			   (t mouse-y))))
	     (windows:move-viewport w 
				    (x-pixelate good-x)
				    (y-pixelate good-y)))))))
    
  nil)
  
(defun reshape-window (w)
  (when (and w
	     (not (eql w (windows:root-viewport))))
    (move-window w)
    (let ((left (getw-left w))
	  (top (getw-top w)))
      (windows:with-mouse-documentation
	  ("left click to place right bottom corner")
	(rubber-window-til-left-click
	 #'(lambda (mouse-x mouse-y)
	     (let ((good-x (cond
			     ((< (- mouse-x left) 10)
			      (+ left 10))
			     ((< SCRWIDTH mouse-x) SCRWIDTH)
			     (t mouse-x)))
		   (good-y (cond
			     ((< (- mouse-y top) 3) 
			      (+ top 3))
			     ((< SCRHEIGHT mouse-y) SCRHEIGHT)
			     (t mouse-y))))
	       (windows:reshape-viewport 
		w
		:x (x-pixelate left) :y (y-pixelate top)
		:width (x-pixelate (1+ (- good-x left)))
		:height (y-pixelate (1+ (- good-y top))))))))
      (windows:clear-bitmap w)
      (menu-size-event w nil (getw-top w) (getw-left w)
		       (getw-bot w) (getw-right w))))
  nil)
  
(defun bury-window (window)
  ;; Bury the window under the mouse.
  (when (and window
	     (not (eql window (windows:root-viewport))))
    (windows:hide-viewport window)
    (let ((new-window (find-if #'(lambda (w) (member w *allocated-panes*))
			       (windows:viewport-children
				(windows:root-viewport)))))
      (selectw new-window)
      ;; Return a fake blip so that the upper level of the system will find out that
      ;; the window has been selected.
      `(MOUSE-JUMP ,new-window 0 0))))
  
(defun refresh-window (w)
  (when (and w
	     (not (eql w (windows:root-viewport))))
    (windows:clear-bitmap w)
    (menu-size-event w nil (getw-top w) (getw-left w) (getw-bot w) (getw-right w))
    nil))
  
(defun refresh-all (w)
  (declare (ignore w))
  (dolist (i *selectable-windows-item-list*)
    (refresh-window i))
  nil)
  
(defun help-window (w)
  (declare (ignore w))
  (windows:activate-viewport *help-window*)
  (windows:expose-viewport *help-window*)
  (wait-for-left-click)
  (windows:deactivate-viewport *help-window*)
  nil)

  
;;; Output functions.
  
(defun invert-text-cursor ()
    (let ((x (windows:stream-x-position *selected-window*))
	  (y (windows:stream-y-position *selected-window*)))
      (setf (windows:stream-operation *selected-window*) boole-eqv)
      (write-char #\space *selected-window*)
      (setf (windows:stream-x-position *selected-window*) x)
      (setf (windows:stream-y-position *selected-window*) y)
      (setf (windows:stream-operation *selected-window*) boole-1)
      )
    nil)
  
(defun cursor-pos (w)
  (values (x-unpixelate (windows:stream-x-position w))
	  (y-unpixelate (windows:stream-y-position w))))
  
(defun get-char-position ()
  (list (x-unpixelate (windows:stream-x-position *selected-window*))
	(y-unpixelate (windows:stream-y-position *selected-window*))))
  
(defun write-char-to-current-window (c)
  (multiple-value-bind (x y) (cursor-pos *selected-window*)
    (if (char= c #\newline)
	(if (>= y (1- *selected-height*))
	    (move-cursor 0 0)
	    (write-char #\newline *selected-window*))
	(progn
	  (cond ((< x (1- *selected-width*))
		 (write-char c *selected-window*)
		 (when *snapshot-mode-p*
		   (setf (aref *snapshot-buffer* y x) (char->ichar c))))
		((= x (1- *selected-width*))
		 (write-char c *selected-window*)
		 (write-char-to-current-window #\newline)
		 (when *snapshot-mode-p*
		   (setf (aref *snapshot-buffer* y x) (char->ichar c))))
		(t
		 (write-char-to-current-window #\newline)
		 (when *snapshot-mode-p*
		   (multiple-value-bind (x y) (cursor-pos *selected-window*)
		     (setf (aref *snapshot-buffer* y x) (char->ichar c))))
		 (write-char c *selected-window*)))))))
  
(defun write-string-to-current-window (str)
  (map nil #'write-char-to-current-window str))
  
(defun putc (ch)
  ;; Clear the current position, write the character in that position and return the
  ;; new x position.
  (write-char-to-current-window (ichar->char ch))
  (get-char-position))
  
(defun putnl ()
  ;; Clear the rest of this line, and the next line and put the cursor at the
  ;; beginning of the next line.
  (erase-to-end-of-line)
  (write-char-to-current-window #\newline)
  (erase-to-end-of-line))
  
(defun putstr (str)
  ;; Print all the characters in the prl-string after clearing appropriate locations.
  ;;  It is assumed that all the elements of the prl-string are printing characters.
  (windows:with-fast-drawing-environment
      (clear-forward (length str))
    (write-string-to-current-window (prl-string-to-string str))))
  
(defun fresh-line-in-current-window ()
  (unless (eql 0 (cursor-pos *selected-window*))
    (write-char-to-current-window #\newline))
  (erase-to-end-of-line))
  
(defun display-message-str (str)
  ;; Output the message in the display-message-window (usually the command window)
  ;; without disturbing the window state.
  (let ((curwin *selected-window*)
	(curht *selected-height*)
	(curwd *selected-width*))
    (setf *selected-window* display-message-window
	  *selected-width* (window-width *selected-window*)
	  *selected-height* (window-height *selected-window*))
    (windows:with-fast-drawing-environment
	(fresh-line-in-current-window)
      (write-string-to-current-window str)
      (erase-to-end-of-line t))
    (setf *selected-window* curwin)
    (setf *selected-width* curht)
    (setf *selected-height* curwd)))
  
(defun display-message (prl-str)
  (display-message-str (prl-string-to-string prl-str)))
  
(defvar *prl-string* (make-array 100 :element-type 'string-char :fill-pointer 0 :adjustable t)
  "A string for converting from prl strings to real strings.")
  
(defun prl-string-to-string (prl-str)
  ;; Returns a string containing the characters corresponding to the elements of
  ;; prl-str.  This string is only valid until the next call of this function.
  (setf (fill-pointer *prl-string*) 0)
  (dolist (ch prl-str)
    (vector-push-extend (ichar->char ch) *prl-string*))
  *prl-string*)
  
  
(defun clear-window-region (window x y width height)
  (windows:clear-bitmap
   window
   (windows:make-region :x (x-pixelate x) :y (y-pixelate y)
			:width (x-pixelate width)
			:height (y-pixelate height))))
  
(defun clear-forward (m &optional (move-cursor-p nil))
  (multiple-value-bind (x y) (cursor-pos *selected-window*)
    (let* ((win *selected-window*)
	   (w (window-width win))
	   (h (window-height win))
	   (n (mod m (* w h)))
	   (new-x (mod (+ x n) w))
	   (k (+ y (truncate (+ x n) w)))
	   (new-y (mod k h)))
      (cond ((>= m (* w h))
	     (windows:clear-bitmap win))
	    ((<= (+ x n) (1- w))
	     (clear-window-region win x y n 1))
	    (t
	     (clear-window-region win x y (- w x) 1)
	     (cond ((> k (1- h))
		    (clear-window-region win 0 (1+ y) w (- h y 1))
		    (clear-window-region win 0 0 w new-y))
		   (t
		    (clear-window-region win 0 (1+ y) w (- new-y y 1))))
	     (clear-window-region win 0 new-y new-x 1)))
      (when move-cursor-p
	(move-cursor new-x new-y)))))
  
(defun clear-backward (n &optional (move-cursor-p nil))
  (multiple-value-bind (x y) (cursor-pos *selected-window*)
    (let* ((win *selected-window*)
	   (w (window-width win))
	   (h (window-height win))
	   (new-x (mod (- x n) w))
	   (k (+ y (truncate (1+ (- x w n)) w)))
	   (new-y (mod k h)))
      (move-cursor new-x new-y)
      (clear-forward n)
      (unless move-cursor-p
	(move-cursor x y)))))
  
(defun erase-to-end-of-line (&optional (move-cursor-p nil))
  (clear-forward (- *selected-width* (cursor-pos *selected-window*)) 
		 move-cursor-p))
  
;;; Moves cursor.
(defun erase-n-chars (n)
  (windows:with-fast-drawing-environment
      (clear-forward n t)))
  
(defun clear-window ()
  (windows:clear-bitmap *selected-window*)
  (move-cursor 0 0))
  
(defun clear-screen ()
  nil)
  
(defun setheaderw (start str &optional (clear-to-end-p nil))
  ;; Change the label of the selected window.
  (when (null start) (setf start 0))
  (setf (windows:window-title *selected-window*) 
	(let* ((name (windows:window-title *selected-window*))
	       (name-length (length name))
	       (string (prl-string-to-string str))
	       (str-length (length string)))
	  (cond ((>= start name-length)
		 (concatenate 'string name string))
		((or (>= (+ start str-length) name-length)
		     clear-to-end-p)
		 (concatenate 'string (subseq name 0 start) string))
		(t
		 (concatenate 'string
			      (subseq name 0 start)
			      string
			      (subseq name (+ start str-length)))))))
  )
  
  
(defun get-current-selected-window ()
  ;; An ugly little function for the hacks in lib.lisp.
  *selected-window*)
  
(defvar *readline-chars* (make-array 200 :fill-pointer 0 :adjustable t))
  
(defun Preadline (prl-prompt splicer)
  ;; Print the prompt in the selected window, read chars from 'getchr'
  ;; until a (NL) or (EXIT) character and return the list read.
  ;; Whenever the result of 'getchr' is not a fixnum and not (EXIT),
  ;; apply 'splicer' to it, and splice the resulting list into the list
  ;; of characters read so far.  Thus 'splicer' should always yield a
  ;; list of fixnums, unless it yields the atom redisplay-line, in
  ;; which case the prompt and chars typed so far are redisplayed.
  (fresh-line-in-current-window)
  (setf (fill-pointer *readline-chars*) 0)
  (let ((window *selected-window*)
	(prompt (lisp:copy-seq (prl-string-to-string prl-prompt))))
    (setf *current-prompt* prompt)
    (windows:with-fast-drawing-environment
	(write-string-to-current-window prompt))
    (do ((ch (getchr) (getchr)))
	((or (equal ch '(NL)) (equal ch '(EXIT)))
	 (write-char-to-current-window #\newline)
	 (clear-forward *selected-width*)
	 (vector-push-extend ch *readline-chars*)
	 (setf *current-prompt* nil)
	 (concatenate 'list *readline-chars*))
      (unless (eql *selected-window* window)
	(selectw window))
      (if (consp ch)
	  (case (first ch)
	    (DEL
	     (when (not (zerop (fill-pointer *readline-chars*)))
	       (clear-backward 1 t)
	       (decf (fill-pointer *readline-chars*))))
	    (KILL-LINE
	     (clear-backward (+ 2 (length *readline-chars*)) t)
	     (write-string-to-current-window prompt)
	     (setf (fill-pointer *readline-chars*) 0))
	    (otherwise
	     (let ((splice-str (funcall splicer ch)))
	       (if (eql splice-str 'redisplay-line)
		   (redisplay-line)
		   (progn
		     (putstr splice-str)
		     (dolist (x splice-str)
		       (vector-push-extend x *readline-chars*)))))))
	  (progn
	    (putc ch)
	    (vector-push-extend ch *readline-chars*))))))

(defun redisplay-line ()
  ;; Move to a fresh line and redisplay the current string.
  (windows:with-fast-drawing-environment
    (fresh-line-in-current-window)
    (write-string-to-current-window *current-prompt*)
    (let ((length (length *readline-chars*)))
      (clear-forward length)
      (dotimes (i length)
	(let ((ch (aref *readline-chars* i)))
	  (when (numberp ch)
	    (write-char-to-current-window (ichar->char ch))))))))

(defun adjust-snapshot-buffer-size (window)
  (let ((width (window-width window))
	(height (window-height window)))
    (when (or (< *snapshot-buffer-width* width)
	      (< *snapshot-buffer-height* height))
      (adjust-array *snapshot-buffer* (list (max *snapshot-buffer-height* height)
					    (max *snapshot-buffer-width* width))
		    :element-type 'ichar
		    :initial-element *ispace*))))

;;; Also clear the portion of the buffer that is output.
(defun output-snapshot-buffer (label width height)
  (with-open-file (s (or *snapshot-file* "~/snapshot.text")
		     :direction :output
		     :if-exists :append
		     :if-does-not-exist :create)
    (format s "~3%~A~2%" label)
    (dotimes (y height) 
      (dotimes (x width)
	(write-char (if *output-for-latexize*
			(ichar->char-for-latexize (aref *snapshot-buffer* y x))
			(ichar->char-or-string (aref *snapshot-buffer* y x)))
		    s)
	(setf (aref *snapshot-buffer* y x) *ispace*))
      (format s "~%"))))
  
(defun snapshot-window (w)
  (when (and w
	     (not (eql w (windows:root-viewport))))
    (let ((*snapshot-mode-p* t))
      (adjust-snapshot-buffer-size w)
      (refresh-window w)
      (output-snapshot-buffer 
       (windows:window-title w)
       (window-width w) (window-height w)))
    nil))

(defun enter-prl-state$ ()
  nil)

(defun leave-prl-state$ ()
  nil)

;;; There's no easy way to do this.  It doesn't matter, since
;;; it's only used as a convenience.
(defmacro with-terminal-io-on-frame (&body body)
  `(progn . ,body))

(defun with-fast-redrawing (w redrawing-function &rest args)
  (declare (ignore w))
  (apply redrawing-function args))

(defun nuprl ()
  (prl))


