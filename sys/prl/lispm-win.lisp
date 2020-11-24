;;; -*- Package: Nuprl; Base: 10; Syntax: Common-lisp -*-
;;;
;;; Provides the necessary support for Prl to use Lisp Machine windows.  The
;;; interface is at the level of win.lisp.  This file obsoletes win.lisp,
;;; window.lisp and the primitive screen functions of zprlfuncs.lisp.

(defvar *nuprl-frame* nil
  "The frame in which all the Nuprl panes live.")
(defvar *nuprl-io-buffer* nil
  "The io buffer to be used by all the Nuprl panes.")


(defvar *nuprl-character-style* '(:fix :roman :normal)
  "The character style to use for the body of all the panes")
(defvar *nuprl-label-char-style* '(:fix :bold :normal)
  "The character style to use for the labels of the the panes")
(defvar *nuprl-label-font* (si:get-font si:*b&w-screen* si:*standard-character-set*
					*nuprl-label-char-style*))
(defvar *nuprl-frame-label-style* '(:eurex :italic :huge))

;;; Return T if the arguments are different than the current styles, nil
;;; otherwise.  The caller must guarantee that the nuprl window system
;;; gets reinitialized (initw).  The styles must be given as a 3-element
;;; list.
(defun change-nuprl-character-styles (new-main-style new-label-style)
  (let ((changed-p (not (and (equal new-main-style *nuprl-character-style*)
			     (equal new-label-style *nuprl-label-char-style*)))))
    (setq *nuprl-character-style* new-main-style
	  *nuprl-label-char-style* new-label-style
	  *nuprl-label-font* (si:get-font si:*b&w-screen* si:*standard-character-set*
					  *nuprl-label-char-style*))
    changed-p))

(defun change-nuprl-character-size (new-size)
  (unless (member new-size '(:very-small :small :normal :large :very-large))
    (error "~A is not an acceptable character size." new-size))
  (let ((new-main-style (copy-list *nuprl-character-style*))
	(new-label-style (copy-list *nuprl-label-char-style*)))
    (setf (third new-main-style) new-size)
    (setf (third new-label-style) new-size)
    (change-nuprl-character-styles new-main-style new-label-style)))
      

(defvar *char-width* 0
  "The width of a character in the nuprl character style in pixels")
(defvar *line-height* 0
  "The height of a line (a character and the vsp) in pixels")

(defvar *snapshot-buffer-width* 140)
(defvar *snapshot-buffer-height* 60)
(defvar *snapshot-buffer*  ;each row represents a row of the window being snapshotted
	(make-array `(,*snapshot-buffer-height* ,*snapshot-buffer-width*)
		    :element-type 'string-char
		    :initial-element #\space
		    :adjustable t))

(defvar *snapshot-mode-p* nil
  "Certain output to a nuprl pane will also be sent to *snapshot-buffer*.")

(defvar *current-prompt* nil
  "The current prompt string for Nuprl's command window")

;; Characters treated specially by the system.  Typing any of these characters
;; results in the associated thing being put in the input stream.
(defparameter *prl-special-characters*
		 '((#\c-C . (COPY))        (#\c-I . (INS))
		   (#\c-K . (KILL))        (#\c-D . (EXIT))
		   (#\Return . (NL))       (#\Rubout . (DEL))
		   (#\c-U . (KILL-LINE))
		   (#\c-B . (BRACKET))     (#\c-T . (TRANSFORM))
		   (#\c-W . (SHOW-PARENS)) (#\Tab . (CMD))
		   (#\m-Z . (SEL))	   (#\m-X . (DOWN))
		   (#\m-C . (MOUSE))	   (#\m-A . (LEFT))
		   (#\m-S . (LONG))	   (#\m-D . (RIGHT))
		   (#\m-Q . (DIAG))	   (#\m-W . (UP))
		   (#\m-E . (REGION))
		   (#\h-m . (SEL))	   (#\h-\, . (DOWN))
		   (#\h-. . (MOUSE))	   (#\h-j . (LEFT))
		   (#\h-k . (LONG))	   (#\h-l . (RIGHT))
		   (#\h-u . (DIAG))	   (#\h-i . (UP))
		   (#\h-o . (REGION))))


(defun window-equal (w1 w2) (equal w1 w2))

(scl:defflavor nuprl-frame
	()
	(tv:basic-frame tv:window-with-typeout-mixin tv:borders-mixin
	 tv:label-mixin tv:minimum-window)
  (:default-init-plist
   :typeout-window '(tv:temporary-typeout-window)))

(scl:defmethod (:force-kbd-input nuprl-frame) (ch &optional no-hang-p whostate)
  ;; The nuprl frame flavor doesn't have an io buffer so we have to provide this
  ;; method for the mouse to report clicks on the frame.
  (tv:io-buffer-put *nuprl-io-buffer* ch no-hang-p whostate))

(scl:defmethod (:who-line-documentation-string nuprl-frame) ()
  "Mouse-R: Window Selection Menu")

(defmacro do-panes (var &body body)
  ;; A macro for iterating over all the panes of the nuprl frame.
  (let ((typeout-window (gensym)))
    `(let ((,typeout-window (scl:send *nuprl-frame* :typeout-window)))
       (dolist (,var (tv:sheet-inferiors *nuprl-frame*))
	 (when (neq ,var ,typeout-window)
	   ,@body)))))

(scl:defflavor nuprl-pane
	(top left right bottom select-item)
	(tv:pane-no-mouse-select-mixin
	 tv:top-box-label-mixin
	 tv:window)
  :readable-instance-variables)

(scl:defmethod (:who-line-documentation-string nuprl-pane) ()
  (declare (special lib-window))
  (if (window-equal lib-window scl:self)
      "Mouse-L: Grab object name; Mouse-M: Display theorem or scroll window; Mouse-R: Window operation menu."
      "Mouse-L: Select; Mouse-M: Jump; Mouse-R: Window operation menu."))

(defvar *selectable-windows-item-list* nil
  "The item list of all the selectable Nuprl panes")

(scl:defmethod (set-up-select-item nuprl-pane) ()
  (setq select-item
	(list nil :value scl:self :documentation nil))
  (push select-item *selectable-windows-item-list*))

(scl:defmethod (:set-label nuprl-pane :after) (&rest ignore)
  ;; Put the name of the window into the item.
  (let ((name (sixth (scl:send scl:self :label))))
    ;; Set the name of the item.
    (setf (first select-item) name)
    ;; Set the documentation string.
    (setf (fifth select-item) (scl:string-append "Select " name))))

(scl:defmethod (set-character-coordinates nuprl-pane) ()
  ;; Update the local character coordinates.
  (multiple-value-bind (left-pixel top-pixel)
      (scl:send scl:self :position)
    (decf top-pixel (scl:send scl:self :top-margin-size))
    (decf left-pixel (scl:send scl:self :left-margin-size))
    (setf top (cl:truncate top-pixel *line-height*))
    (setf left (cl:truncate left-pixel *char-width*))
    (multiple-value-bind (width height)
	(scl:send scl:self :size-in-characters)
      (setf bottom (1- (+ top height)))
      (setf right (1- (+ left width))))))

(tv:defwindow-resource nuprl-pane-resource ()
  ;; A resource of nuprl panes.
  :initial-copies 0
  :constructor make-nuprl-pane
  :reusable-when :deactivated)

(defun make-nuprl-pane (resource-info &optional (blinker-p t))
  ;; Make a nuprl pane with the default attributes.
  (declare (ignore resource-info))
  (tv:make-window 'nuprl-pane
		  :superior *nuprl-frame*
		  :io-buffer *nuprl-io-buffer*
		  :save-bits t
		  :more-p nil
		  :label ""
		  :deexposed-typeout-action :permit
		  :default-character-style *nuprl-character-style*
		  :borders t
		  :integral-p t
		  :blinker-p blinker-p))

(defvar *window-op-menu* nil
  "The menu for choosing window operations.
This is a momentary window hacking menu.")

(defvar *window-op-item-list*
	`(("Move" :window-op move-window
	   :documentation "Move window under mouse")
	  ("Shape" :window-op reshape-window
	   :documentation "Reshape window under mouse")
	  ("Bury" :window-op bury-window
	   :documentation "Bury window under mouse")
	  ("Select" :funcall select-window-from-menu
	   :documentation "Select a window")
	  ("Snapshot" :window-op snapshot-window
	   :documentation "Snapshot window under mouse.  Use set_snapshot_file to set destination.")))


(defvar *select-pane-menu* nil
  "The menu for selecting another pane.
This is a dynamic momentary menu.")


;;; Initialize the base level of the the prl window setup.  If *nuprl-frame* is
;;; not null then first deactivate its value.
(defun initw ()
  (let ((init-file (merge-pathnames *init-file-name*
				    (user-homedir-pathname))))
    (when (probe-file init-file) (load init-file)))
  (when *nuprl-frame* (scl:send *nuprl-frame* :deactivate))
  ;; Perform major initialization.
  (setf *nuprl-io-buffer* (tv:make-io-buffer 100))
  ;; Set the parameters for conversion from pixels to character coordinates.
  (let* ((sys:font (si:get-font si:*b&w-screen* si:*standard-character-set*
				*nuprl-character-style*)))
    (setf *line-height* (+ (zl:font-char-height sys:font) 2))
    (setf *char-width* (zl:font-char-width sys:font)))
  ;; Initialize the resource of panes.  Any elements of the resource
  ;; belong to an extinct nuprl frame.
  (scl:clear-resource 'nuprl-pane-resource)
  ;; Set up the menus.
  (setf *selectable-windows-item-list* nil)
  (setf *window-op-menu*
	(tv:make-window 'tv:momentary-window-hacking-menu
			:label '(:string "Window Operation" :font fonts:cptfonti)
			:item-list *window-op-item-list*))
  (setf *select-pane-menu*
	(tv:make-window 'tv:dynamic-momentary-menu
			:label '(:string "Select a window" :font fonts:cptfonti)
			:item-list-pointer '*selectable-windows-item-list*))
  ;; Add an easy way to get the nuprl window.
  (tv:add-select-key #\U 'nuprl-frame "Nuprl" nil t)
  ;; Make the nuprl window.
  (setf *nuprl-frame*
	(tv:make-window 'nuprl-frame
			:label `(:string "Nuprl"
				 :font ,(si:get-font si:*b&w-screen*
						     si:*standard-character-set*
						     *nuprl-frame-label-style*))
			:default-character-style *nuprl-character-style*
			:borders t
			:integral-p t
			:save-bits t))
  ;; Things done every time.
  (scl:send *nuprl-frame* :activate)
  (scl:send *nuprl-frame* :expose)
  (cl:multiple-value-setq (SCRWIDTH SCRHEIGHT)
    (scl:send *nuprl-frame* :size-in-characters))
  ;; to be safe.
  (decf SCRWIDTH) (decf SCRHEIGHT)
  (scl:send *nuprl-frame* :select t))

(defun createw (top bottom left right &key (library nil) (allow-shift nil))
  ;; Make a new nuprl pane and return it.
  (declare (ignore allow-shift))
  (let ((win (if library
		 (make-nuprl-pane nil nil)
		 (scl:allocate-resource 'nuprl-pane-resource))))
    (set-up-select-item win)
    (when library
      (setf *selectable-windows-item-list*
	    (delete (nuprl-pane-select-item win) *selectable-windows-item-list*)))
    (scl:send win :set-position (* left *char-width*) (* top *line-height*))
    ;; Set a null label so that the window knows how much space to leave.
    (scl:send win :set-label `(:string "" :font ,*nuprl-label-font*))
    (scl:send win :set-size-in-characters (1+ (- right left)) (1+ (- bottom top)))
    (scl:send win :activate)
    (scl:send win :expose)
    (set-character-coordinates win)
    win))

(defun destroyw (window)
  ;; Kill a window.  It is removed from the list of candidates for selection and made
  ;; inactive so that it can be reused.
  (setf *selectable-windows-item-list*
	(delete (nuprl-pane-select-item window) *selectable-windows-item-list*))
  ;; Clear the window so that the next use won't be surprised by the contents.
  (scl:send window :clear-window)
  (scl:send window :set-label "")
  (scl:send window :deexpose)
  (scl:send window :deactivate))

(defun changesizew (w y1 y2 x1 x2)
  (declare (ignore w y1 y2 x1 x2))
  ;; A stub.
  nil)

;; Remove the definition of the following as normal functions.  This is necessary if
;; this file is being loaded over win.lisp which defines these as normal functions.
(eval-when (load)
  (mapc #'scl:fundefine '(window-width window-height getw-top getw-bot getw-left getw-right)))

(scl:defmethod (window-width nuprl-pane) ()
  (scl:send scl:self :size-in-characters))

(scl:defmethod (window-height nuprl-pane) ()
  (multiple-value-bind (ignore height)
      (scl:send scl:self :size-in-characters)
    height))

(scl:defmethod (getw-top nuprl-pane) ()
  top)

(scl:defmethod (getw-bot nuprl-pane) ()
  bottom)

(scl:defmethod (getw-left nuprl-pane) ()
  left)

(scl:defmethod (getw-right nuprl-pane) ()
  right)

(defun movecursor (y x)
  ;; Move the cursor to position x,y.
  (scl:send (scl:send *nuprl-frame* :selected-pane) :set-cursorpos x y :character))

(defun selectw (window)
  ;; Make window the active (selected) window.
  (scl:send window :expose)
  (scl:send *nuprl-frame* :select-pane window))

(defun getchr ()
  ;; Read the next available input.
  (do ((ch (scl:send (scl:send *nuprl-frame* :selected-pane) :any-tyi)
	   (scl:send (scl:send *nuprl-frame* :selected-pane) :any-tyi)))
      (nil)
    (when (setf ch
		(if (consp ch)
		    (process-mouse ch)
		    (process-normal ch)))
      (return ch))))

(defun process-normal (ch)
  ;; Proces a normal character.  If it a special character return its definition.
  ;; Otherwise if it has any bits set, refuse it.
  (cond ((char-equal ch #\Refresh)
	 (refresh)
	 nil)
	((cdr (assoc ch *prl-special-characters* :test #'char-equal)))
	((not (zerop (char-bits ch))) nil)
	(t (char->ichar ch))))

(defun process-mouse (blip)
  ;; Process a mouse character.  If it is a Middle click do menu processing.  If any
  ;; other click is seen by the frame, expose the first pane which conains the point.
  ;; Otherwise return blip of the form (type window x y)  where type is one of
  ;; MOUSE-SEL or MOUSE-JUMP, and x,y are relative to the inside of the window.
  (declare (special lib-window))
  (when (eql (first blip) :mouse-button)
    ;; The blip is of the form
    ;;   (:mouse-button mouse-char window x y)
    ;; where the coordinates are with respect to the outside of the given window.
    ;; The mouse-char object isn't a real character but a mouse character.
    (scl:destructuring-bind (buttons window x y) (cdr blip)
      ;; When the mouse is clicked on a window which is only partially visible (i.e.
      ;; deexposed), the blip comes from the frame.  The following searches for a
      ;; pane which contains the point.  The panes are kept in priority order by the
      ;; system, so the first pane containing the point will be the visible pane.
      (when (eql window *nuprl-frame*)
	(block found-pane
	  (do-panes pane
	    (when (tv:sheet-contains-sheet-point-p pane *nuprl-frame* x y)
	      ;; The mouse is over the pane, but it is deexposed so the frame receives
	      ;; its blips.
	      (setf window pane)
	      (setf x (- x (tv:sheet-x pane)))
	      (setf y (- y (tv:sheet-y pane)))
	      (return-from found-pane (values))))))
      (cond ((scl:char-mouse-equal buttons #\mouse-r)
	     (if (eql window *nuprl-frame*)
		 (select-window-from-menu)
		 (scl:send *window-op-menu* :choose)))
	    ((eql window *nuprl-frame*)
	     ;; Ignore any other blips on the frame.
	     (scl:beep) nil)
	    (t
	      (when (and (not (eql window (scl:send *nuprl-frame* :selected-pane)))
			 (not (eql window lib-window)))
		;; Select the window.
		(selectw window))
	      (let* ((type (scl:selector buttons scl:char-mouse-equal
			    (#\Mouse-L 'MOUSE-SEL)
			    (#\Mouse-M 'MOUSE-JUMP)))
		    ;; Translate the coordinates into inside character coordinates.
		    (x1 (- x (scl:send window :left-margin-size)))
		    (new-x (cl:truncate x1 *char-width*))
		    (y1 (- y (scl:send window :top-margin-size)))
		    (new-y (truncate y1 *line-height*)))
	       `(,type ,window ,new-x ,new-y)))))))

(defun select-window-from-menu ()
  ;; Put up the menu of selectable windows and select the result.  Called from the
  ;; window operations menu.
  (let ((window (scl:send *select-pane-menu* :choose)))
    (if window
	(progn
	  (selectw window)
	  ;; Make a fake blip so that the upper level of the system will
	  ;; know the window has been selected.
	  `(MOUSE-JUMP ,window 0 0))
	nil)))

(defun move-window (window x y)
  ;; Let the user move the window under the mouse using the mouse.
  (declare (ignore x y))
  (tv:window-call-relative (window)
    (tv:mouse-set-window-position window)
    (set-character-coordinates window))
  nil)

(defun reshape-window (window x y)
  ;; Let the user reshape the window under the mouse using the mouse.
  (declare (ignore x y))
  (tv:window-call-relative (window)
    (tv:mouse-set-window-size window)
    (scl:send window :clear-window)
    ;; the window must have space for at least one character.
    (multiple-value-bind (width height)
	(scl:send window :size-in-characters)
      (when (or (= 0 width) (= 0 height))
	(scl:send window :set-size-in-characters (max 1 width) (max height 1))))
    (when (neq (scl:send window :status) :deactivated)
      (set-character-coordinates window)
      ;; Call the prl routine which handles refresh etc.
      (menu-size-event window nil (getw-top window) (getw-left window) 
		       (getw-bot window) (getw-right window))))
  nil)


(defun bury-window (window x y)
  (declare (ignore x y))
  (scl:send window :bury)
  (let ((new-window (scl:send *nuprl-frame* :selected-pane)))
    ;; Return a fake blip so that the upper level of the system will find out that
    ;; the window has been selected.
    `(MOUSE-JUMP ,new-window ,(nuprl-pane-top new-window) ,(nuprl-pane-left new-window))))


(defun adjust-snapshot-buffer-size (window)
  (multiple-value-bind (width height)
      (scl:send window :size-in-characters)
    (when (or (< *snapshot-buffer-width* width)
	      (< *snapshot-buffer-height* height))
      (adjust-array *snapshot-buffer* (list (max *snapshot-buffer-height* height)
					    (max *snapshot-buffer-width* width))
		    :element-type 'string-char
		    :initial-element #\space))))

;;; Also clear the portion of the buffer that is output.
(defun output-snapshot-buffer (label width height)
  (with-open-file (s (or *snapshot-file*
			 (merge-pathnames "snapshot.text" (fs:user-homedir)))
		     :direction :output
		     :if-exists :append
		     :if-does-not-exist :create)
    (format s "~3%~A~2%" label)
    (dotimes (y height) 
      (dotimes (x width)
	(scl:send s :tyo (aref *snapshot-buffer* y x))
	(setf (aref *snapshot-buffer* y x) #\space))
      (format s "~%"))))
  
(defun snapshot-window (window x y)
  (declare (ignore x y))
  (adjust-snapshot-buffer-size window)
  (tv:window-call-relative (window)
    (let ((*snapshot-mode-p* t))
      (menu-size-event window nil (getw-top window) (getw-left window) 
		       (getw-bot window) (getw-right window))))
  (multiple-value-bind (width height)
      (scl:send window :size-in-characters)
    (output-snapshot-buffer (sixth (scl:send window :label)) width height))
  nil)

(scl:defmethod (:tyo nuprl-pane :before) (ch) 
  (when (and *snapshot-mode-p* (not (char= ch #\return)))
    (multiple-value-bind (x y)
	(scl:send scl:self :read-cursorpos :character)
      (setf (aref *snapshot-buffer* y x) ch))))




;;; Output functions.

(defun putc (ch)
  ;; Clear the current position, write the character in that position and return the
  ;; new x position.
  (declare (special cmd-window$))
  (let ((selected-pane (scl:send *nuprl-frame* :selected-pane)))
    (scl:send selected-pane :clear-char)
    (scl:send selected-pane :tyo (ichar->char ch))
    (multiple-value-bind (x y)
	(scl:send selected-pane :read-cursorpos :character)
      (multiple-value-bind (width height)
	  (scl:send selected-pane :size-in-characters)
	(when (eql selected-pane cmd-window$))
	(if (scl: x width)
	    (progn (scl:send selected-pane :set-cursorpos 0 (mod (1+ y) height) :character)
		   0)
	    x)))))

(defun putnl ()
  ;; Clear the rest of this line, and the next line and put the cursor at the
  ;; beginning of the next line.
  (scl:send (scl:send *nuprl-frame* :selected-pane) :clear-rest-of-line)
  (scl:send (scl:send *nuprl-frame* :selected-pane) :fresh-line))

(defun putstr (str)
  ;; Print all the characters in the prl-string after clearing appropriate locations.
  ;; It is assumed that all the elements of the prl-string are printing characters.
  (mapc #'putc str))

(defun display-message (str)
  ;; Output the message in the display-message-window (usually the command window)
  ;; without disturbing the window state.
  (declare (special display-message-window))
  (tv:window-call-relative (display-message-window)
    (scl:send display-message-window :fresh-line) 
    (scl:send display-message-window :string-out (prl-string-to-string str))
    (erase-to-end-of-line)))

(defvar *prl-string* (make-array 100 :element-type 'string-char :fill-pointer 0 :adjustable t)
  "A string for converting from prl strings to real strings.")

(defun prl-string-to-string (prl-str)
  ;; Returns a string containing the characters corresponding to the elements of
  ;; prl-str.  This string is only valid until the next call of this function.
  (setf (fill-pointer *prl-string*) 0)
  (dolist (ch prl-str)
    (vector-push-extend (ichar->char ch) *prl-string*))
  *prl-string*)

(defun clear-forward (n &optional (set-cursor nil)
		      &aux (selected-pane (scl:send *nuprl-frame* :selected-pane)))
  (multiple-value-bind (x y)
      (scl:send selected-pane :read-cursorpos :character)
    (dotimes (i n) (putc (char->ichar #\space)))
    (unless set-cursor
      (scl:send selected-pane :set-cursorpos x y :character))))


(defun clear-backward (n &optional
		       &aux (selected-pane (scl:send *nuprl-frame* :selected-pane)))
  (multiple-value-bind (width height)
      (scl:send selected-pane :size-in-characters)
    (multiple-value-bind (old-x old-y)
	(scl:send selected-pane :read-cursorpos :character)
      (multiple-value-bind (lines remaining-chars)
	  (truncate n width)
	(multiple-value-bind (screens remaining-lines)
	    (truncate lines height)
	  (let* ((x (mod (- old-x remaining-chars) width))
		 (y (mod (- old-y remaining-lines (if (> x old-x) 1 0))
			 height)))
	    (if (> screens 0)
		(scl:send selected-pane :clear-window)
		(scl:send selected-pane
			  :clear-between-cursorposes x y old-x old-y :character))
	      (scl:send selected-pane :set-cursorpos x y :character)))))))

(defun erase-to-end-of-line ()
  (scl:send (scl:send *nuprl-frame* :selected-pane) :clear-rest-of-line))

(defun erase-n-chars (n)
  (clear-forward n t))

(defun clear-window ()
  (scl:send (scl:send *nuprl-frame* :selected-pane) :clear-window))

(defun refresh ()
  ;; Refresh the screen and redraw the contents.
  ;;(send *nuprl-frame* :refresh nil)
  (do-panes pane
    (when (scl:send pane :exposed-p)
      (tv:window-call-relative (pane)
	(scl:send pane :clear-window)
	(scl:send pane :refresh-margins)
	(menu-size-event pane nil
			 (nuprl-pane-top pane)
			 (nuprl-pane-left pane)
			 (nuprl-pane-bottom pane)
			 (nuprl-pane-right pane))))))

(defun clear-screen ()
  nil)

(defun setheaderw (start str &optional (clear-to-end-p nil))
  ;; Change the label of the selected window.
  (when (null start) (setf start 0))
  (scl:send (scl:send *nuprl-frame* :selected-pane) :set-label
	`(:string
	   ,(let* ((name (sixth (scl:send (scl:send *nuprl-frame* :selected-pane) :label)))
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
				     (subseq name (+ start str-length))))))
	   :font ,*nuprl-label-font*)))


(defun get-current-selected-window ()
  ;; An ugly little function for the hacks in lib.lisp.
  (scl:send *nuprl-frame* :selected-pane))

(defvar *readline-chars* (make-array 200 :fill-pointer 0 :adjustable t))

(defun Preadline (prl-prompt splicer)
  ;; Print the prompt in the selected window, read chars from 'getchr'
  ;; until a (NL) or (EXIT) character and return the list read.
  ;; Whenever the result of 'getchr' is not a fixnum and not (EXIT),
  ;; apply 'splicer' to it, and splice the resulting list into the list
  ;; of characters read so far.  Thus 'splicer' should always yield a
  ;; list of fixnums, unless it yields the atom redisplay-line, in
  ;; which case the prompt and chars typed so far are redisplayed.
  ;; No other windows can be selected until the line is finished.
  (scl:send (scl:send *nuprl-frame* :selected-pane) :fresh-line)
  (setf (fill-pointer *readline-chars*) 0)
  (let* ((prompt (lisp:copy-seq (prl-string-to-string prl-prompt)))
	 (window (scl:send *nuprl-frame* :selected-pane))
	 (*current-prompt* prompt))
    (scl:send (scl:send *nuprl-frame* :selected-pane) :string-out prompt)
    (do ((ch (getchr) (getchr)))
	((or (equal ch '(NL)) (equal ch '(EXIT)))
	 (scl:send (scl:send *nuprl-frame* :selected-pane) :fresh-line)
	 (vector-push-extend ch *readline-chars*)
	 (concatenate 'list *readline-chars*))
      (selectw window)
      (if (consp ch)
	  (case (first ch)
	    (DEL
	     (when (not (zerop (fill-pointer *readline-chars*)))
	       (clear-backward 1)
	       (decf (fill-pointer *readline-chars*))))
	    (KILL-LINE
	     (clear-backward (+ 2 (length *readline-chars*)))
	     (scl:send (scl:send *nuprl-frame* :selected-pane)
		       :string-out *current-prompt*)
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
  ;; Move to a new line and redisplay the current string.
  (scl:send (scl:send *nuprl-frame* :selected-pane) :fresh-line)
  (when *current-prompt*			; Preadline is waiting for input.
    (scl:send (scl:send *nuprl-frame* :selected-pane)
	      :string-out *current-prompt*)
    (let ((length (length *readline-chars*)))
      (clear-forward length)
      (dotimes (i length)
	(let ((ch (aref *readline-chars* i)))
	  (when (numberp ch)
	    (scl:send (scl:send *nuprl-frame* :selected-pane)
		      :tyo (ichar->char ch))))))))

(defun enter-prl-state$ ()
  (scl:send *nuprl-frame* :expose)
  (scl:send *nuprl-frame* :select))

(defun leave-prl-state$ ()
  (scl:send *nuprl-frame* :deselect))

;;; This should only be used for making certain kinds of io
;;; (e.g. debugger) more convenient for the user (e.g., on the lispm,
;;; not requiring him to switch to a lisp-listener).  Implementations
;;; in other window packages are free to define this as progn.
(defmacro with-terminal-io-on-frame (&body body)
  `(tv:with-terminal-io-on-typeout-window (*nuprl-frame* t)
     . ,body))

(defun with-fast-redrawing (w redrawing-function &rest args)
  (declare (ignore w))
  (apply redrawing-function args))

(defun reset ()
  (reset-prl))

(defun nuprl ()
  (in-package "NUPRL")
  (prl))

(defun user::nuprl ()
  (nuprl))

(scl:compile-flavor-methods nuprl-frame nuprl-pane)

