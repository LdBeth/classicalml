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
                                                                               


;;; ---------------------------------------------------------------------------------

(declaim (special lib-window cmd-window$ display-message-window))

(defun mouse-blip (window code x y)
  (declare (special *selected-window* *documentation-istring*))
  (case code
    (1					  ;left click
      (unless (or (window-equal window *selected-window*)
		  (window-equal window lib-window))
	(select-window window))
      (list 'MOUSE-SEL window x y))
    (2					  ;middle click
      (unless (or (window-equal window *selected-window*)
		  (window-equal window lib-window))
	(select-window window))
      (list 'MOUSE-JUMP window x y))
    (3					  ;right click
      (display-message *documentation-istring*)
      nil)))

(defun recompute-window-contents-and-redraw (window)
  ;; prl wants to set the window's position, but it really doesn't care,
  ;; as long as the args yield the right width and height.
  (multiple-value-bind (x y) (window-coordinates window)
    (menu-size-event window nil		  ;second arg is obsolete
		     y x
		     (1- (+ y (window-property window :height)))
		     (1- (+ x (window-property window :width))))))

;;; a-list with keys of type (modifier list) # character
(defvar *key-bindings* nil)
(defvar *initial-key-bindings* nil)

;;; Case and char-bits are ignored.
(defun key-binding (modifiers-and-character)
  (assoc modifiers-and-character *key-bindings*
	 :test #'(lambda (x y)
		   (and (set-equal (car x) (car y))
			(char-equal (cdr x) (cdr y))))))

;;; A modifier is a member of '(:control :meta :hyper :super).
(defun define-key-binding (modifier-or-modifiers character ichar)
  (let ((modifiers (if (listp modifier-or-modifiers)
		       modifier-or-modifiers
		       (list modifier-or-modifiers))))
    (when (and (null modifiers) (standard-char-p character)
	       (graphic-char-p character))
      (error "Can't redefine standard printing characters (~A in this case)." character))
    (let ((old-binding (key-binding (cons modifiers character))))
      (if old-binding
	  (setf (cdr old-binding) ichar)
	  (push (cons (cons modifiers character)
		      ichar )
		*key-bindings*))))
  (values))

(defun keycode->ichar (keycode state)
  (declare (special *display*))
  (let ((modifiers (append
		    (unless (zerop (logand #.(xlib:make-state-mask :control)
					   state))
		      '(:control))
		    (unless (zerop (logand #.(xlib:make-state-mask :mod-1)
					   state))
		      '(:meta))
		    (unless (zerop (logand #.(xlib:make-state-mask :mod-2)
					   state))
		      '(:hyper))))
	(ch (xlib:keycode->character
	     *display*
	     keycode
	     (logandc2 state
		     #.(logior (xlib:make-state-mask :control)
			       (xlib:make-state-mask :mod-1)
			       (xlib:make-state-mask :mod-2))))))

    (when (characterp ch)
      (if (or modifiers
	      ;; kcl 1.530: (graphic-char-p #\rubout) -> t.
	      ;; cltl : "The semi-standard characters ..., #\rubout, ... are
	      ;;         not graphic" pg 235.
	      #+kcl (char= ch #\rubout)
	      (not (graphic-char-p ch)))
	  (cdr (key-binding (cons modifiers ch)))
	  (char->ichar ch)))))


(defun ichar->font-index (ch)
  (if (numberp ch)
      (unshift-code ch)
      *ispace*))

(defun font-index->char-or-string (i)
  (ichar->char-or-string (shift-code i)))

(defun font-index->char-for-latexize (i)
  (ichar->char-for-latexize (shift-code i)))



;;; Nuprl Key Bindings for Nuprl's special characters.

(define-key-binding :control #\c '(COPY))
(define-key-binding :control #\i '(INS))
(define-key-binding :control #\k '(KILL))
(define-key-binding :control #\d '(EXIT))
(define-key-binding nil #\Rubout '(DEL))
(define-key-binding nil #\Backspace '(DEL))
(define-key-binding :control #\h '(DEL))
(define-key-binding :control #\u '(KILL-LINE))
(define-key-binding :control #\m '(BRACKET))
(define-key-binding :control #\t '(TRANSFORM))
(define-key-binding :control #\o '(SNAPSHOT))	  
(define-key-binding nil #\Tab '(CMD))
(define-key-binding nil #\Return '(NL))
(define-key-binding nil #\Newline '(NL))

(define-key-binding :control #\s '(SEL))
(define-key-binding :control #\n '(DOWN))
(define-key-binding :control #\b '(LEFT))
(define-key-binding :control #\l '(LONG))
(define-key-binding :control #\f '(RIGHT))
(define-key-binding :control #\q '(DIAG))
(define-key-binding :control #\p '(UP))
(define-key-binding :control #\j '(REGION))

;;; :meta is :meta on a Sun.

;;; Simulated keypad on left side of keyboard.
(define-key-binding :meta #\z '(SEL))
(define-key-binding :meta #\x '(DOWN))
(define-key-binding :meta #\a '(LEFT))
(define-key-binding :meta #\s '(LONG))
(define-key-binding :meta #\d '(RIGHT))
(define-key-binding :meta #\q '(DIAG))
(define-key-binding :meta #\w '(UP))
(define-key-binding :meta #\e '(REGION))

;;; Simulated keypad on right side of keyboard.
(define-key-binding :meta #\m '(SEL))
(define-key-binding :meta #\, '(DOWN))
(define-key-binding :meta #\j '(LEFT))
(define-key-binding :meta #\k '(LONG))
(define-key-binding :meta #\l '(RIGHT))
(define-key-binding :meta #\u '(DIAG))
(define-key-binding :meta #\i '(UP))
(define-key-binding :meta #\o '(REGION))

 
;;; Key bindings for nonstandard graphic characters.

(defvar *documentation-istring*)

(let ((doc nil))
  (mapc #'(lambda (p) (let ((ch (car p)) (code (shift-code (cdr p))))
		       (define-key-binding '(:control :meta) ch code)
		       (push (ichar #\space) doc)
		       (push (ichar ch) doc)
		       (push (ichar #\:) doc)
		       (push code doc)))
	'((#\' . 0)		;center-dot
	  (#\h . 1)		;down-arrow
	  (#\a . 2)		;alpha
	  (#\b . 3)		;beta
	  (#\q . 4)		;and-sign
	  (#\- . 5)		;not-sign
	  (#\e . 6)		;epsilon
	  (#\p . 7)		;pi
	  (#\l . 8)		;lambda
	  (#\g . 9)		;gamma
	  (#\d . 10)		;delta
	  (#\^ . 11)		;up-arrow
	  (#\: . 12)		;plus-minus
	  (#\+ . 13)		;circle-plus
	  (#\i . 14)		;infinity
	  (#\6 . 15)		;partial-delta
	  (#\t . 16)		;left-horseshoe
	  (#\y . 17)		;right-horseshoe
	  (#\5 . 18)		;up-horseshoe
	  (#\r . 19)		;down-horseshoe
	  (#\u . 20)		;universal-quantifier
	  (#\o . 21)		;existential-quantifier
	  (#\* . 22)		;circle-x
	  (#\~ . 23)		;double-arrow
	  (#\j . 24)		;left-arrow
	  (#\k . 25)		;right-arrow
	  (#\= . 26)		;not-equal
	  (#\v . 27)		;lozenge
	  (#\, . 28)		;less-or-equal
	  (#\. . 29)		;greater-or-equal
	  (#\` . 30)		;equivalence
	  (#\w . 31)		;or-sign
	  (#\/ . 127)))		;integral
  (setf *documentation-istring*  
	(append (istring "Control-meta key bindings: ")
		(cdr (reverse doc)))))

(defun maybe-process-char-immediately (X-window ch)
  (cond ((ichar= ch '(SNAPSHOT))
	 (let ((w (find-window X-window)))
	   (when w (snapshot-window w)))
	 nil)
	(t
	 ch)))

(defun initialize-application-variables ()
  (declare (special *display* SCRWIDTH SCRHEIGHT))
  (let ((screen (xlib:display-default-screen *display*)))
    (setf SCRWIDTH (X-width->width (xlib:screen-width screen))
	  SCRHEIGHT (X-height->height (xlib:screen-height screen)))))

(defun reset-application ()
  (reset-prl))

(defun application ()
  (prl))


;;; ------------------------------------------------------------------------

(defvar *character-X-width*)
(defvar *line-X-height*)
(defvar *baseline-X-height*)
(defvar *border-X-width*)
(defvar *margin-X-width*)
(defvar *interline-X-space*)
(defvar *vertical-X-offset*)
(defconstant *window-minimum-width* 15)
(defconstant *window-minimum-height* 5)

(defvar *windows-in-use* nil)

(defvar *X-window-output-suppressed?* nil)

(defvar *display* nil)
(defvar *gcontext*)
(defvar *reverse-gcontext*)
(defvar *foreground*)
(defvar *background*)
(defvar *cursor-font*)


(defun width->X-width (w)
  (* w *character-X-width*))
(defun height->X-height (h)
  (* h *line-X-height*))
(defun X-width->width (w)
  (truncate w *character-X-width*))
(defun X-height->height (h)
  (truncate h *line-X-height*))

(defvar *init-file-loaded?* nil)

;(deftype font-index () 'fixnum)

;;; The following breaks Lucid 3.0 (production compiler only).
;(proclaim '(inline width->X-width height->X-height X-width->width X-height->height))

(defparameter *options* 
	      (list :host nil
		    :font-name "fixed"
		    :cursor-font-name "cursor" :cursor-font-index 68
		    :frame-left 30 :frame-right 98
		    :frame-top 30 :frame-bottom 98
		    :no-warp? t
		    :host-name-in-title-bars? t
		    :title-bars? nil
		    :foreground-color "black"
		    :background-color "white"))

(defun typecheck-options (options)
  (unless (null options)
    (let ((option (first options)) (v (second options)))
      (unless (case option
		((:host :font-name :cursor-font-name
			:foreground-color :background-color)
		 (stringp v))
		(:cursor-font-index (and (numberp v) (<= 0 v)))
		((:frame-left :frame-right :frame-top :frame-bottom)
		 (and (numberp v) (<= 0 v 100)))
		((:no-warp? :title-bars? :host-name-in-title-bars?)
		 (or (null v) (eql v t)))
		(otherwise
		 (error "TypeCheckOption : Option ~a is unknown.~%" option)))
	(error "The value ~A specified for option ~A is of the wrong type."
	       v option)))
    (typecheck-options (cddr options))))


(defun check-frame-options (options)
  (let ((l (getf options :frame-left))
	(r (getf options :frame-right))
	(top (getf options :frame-top))
	(bot (getf options :frame-bottom)))
    (unless (and (<= 0 l (+ l 20) r 100)
		 (<= 0 top (+ top 20) bot 100))
      (error "Frame parameters must be at least 20 apart, etc."))))

(defvar *effected-options* nil)

(defun check-options ()
  (typecheck-options *options*)
  (check-frame-options *options*)
  (flet ((important-options (options)
	   (mapcar #'(lambda (option) (getf options option))
		   '(:host :font-name :cursor-font-name :cursor-font-index
		     :frame-left :frame-right :frame-top :frame-bottom
		     :title-bars? 
		     :foreground-color :background-color))))
    (unless (equal (important-options *options*)
		   (important-options *effected-options*))
      (reset nil))))

(defun split-list (l)
  (if (null l) 
      (values () ())
      (multiple-value-bind (x y)
	  (split-list (cddr l))
	(values (cons (car l) x) (cons (cadr l) y)))))

;;; For use in user init files.
(defun change-options (&rest plist)
  (typecheck-options plist)
  (multiple-value-bind (l1 l2)
      (split-list plist)
    (mapc #'(lambda (x y) (setf (getf *options* x) y))
	  l1 l2)))

;;; For use in user init files.
(defun get-option (option)
  (getf *options* option))

;;; For internal use only.
(defun option (option)
  (getf *effected-options* option))

(defvar *output-buffer*
	(make-array 200 :element-type 'fixnum :initial-element
;	(make-array 200 :element-type 'font-index :initial-element
		    (ichar->font-index *ispace*)
		    :adjustable t))

(defun adjust-output-buffer (new-width)
  (when (> new-width (array-dimension *output-buffer* 0))
    (adjust-array
      *output-buffer*
      (+ (array-dimension *output-buffer* 0) 50)
      :element-type 'fixnum
;      :element-type 'font-index
      :initial-element (ichar->font-index *ispace*))))

(defun contract-geometry-into-frame (x y width height)
  (let* ((screen (xlib:display-default-screen *display*))
	 (screen-X-width (xlib:screen-width screen))
	 (screen-X-height (xlib:screen-height screen))
	 (horizontal-factor (/ (- (option :frame-right) (option :frame-left))
			       100.0))
	 (vertical-factor (/ (- (option :frame-bottom) (option :frame-top))
			     100.0))
	 (frame-x (X-width->width
		    (truncate (* screen-X-width (option :frame-left)) 100)))
	 (frame-y (X-height->height
		    (truncate (* screen-X-height (option :frame-top)) 100))))
    (values (+ frame-x (truncate (* x horizontal-factor)))
	    (+ frame-y (truncate (* y vertical-factor)))
	    (truncate (* width horizontal-factor))
	    (truncate (* height vertical-factor)))))

(defun X-size->size (width height)	  
  (values (X-width->width (- width (* 2 *margin-X-width*)))
	  (X-height->height (- height *vertical-X-offset* *margin-X-width*))))

(defun geometry->X-geometry (x y width height)
  (values (- (width->X-width x) *margin-X-width* *border-X-width*)
	  (- (height->X-height y) *vertical-X-offset* *border-X-width*)
	  (+ (width->X-width width) (* 2 *margin-X-width*))
	  (+ (height->X-height height) *vertical-X-offset* *margin-X-width*)))

;;; coodinates within a window (as opposed to within the screen).
(defun X-coordinates->coordinates (x y)
  (values (X-width->width (- x *margin-X-width*))
	  (X-height->height (- y *vertical-X-offset*))))

(defun coordinates->X-coordinates (x y)
  (values (+ (width->X-width x) *margin-X-width*)
	  (+ (height->X-height y) *vertical-X-offset*)))


;;; May be grossly wrong.  Use only for window placement heuristics.
(defun window-coordinates (window)
  (let ((w (window-property window :actual-top-level-X-window)))
    (xlib:with-state (w)
	(values (X-width->width
		 (+ (xlib:drawable-x w)
		    *margin-X-width* *border-X-width*))
		(X-height->height
		 (+ (xlib:drawable-y w)
		    *vertical-X-offset* *border-X-width*))))))

(defun check-and-open-font (display font-name default-font-name)
  (cond ((null (xlib:list-font-names display font-name))
	 (format t "~%Unknown font: ~A.  Using default: ~A.~%" 
		 font-name default-font-name)
	 (xlib:open-font display default-font-name))
	(t
	 (xlib:open-font display font-name))))

;;; First X-window created is assumed to be the group leader.
(defun create-X-window (X-x X-y X-width X-height)
  (let* ((screen (xlib:display-default-screen *display*))
	 (colors (xlib:query-colors (xlib:screen-default-colormap screen)
				    (list *foreground* *background*)))
	 (win (xlib:create-window
	       :parent (xlib:screen-root screen)
	       :x X-x :y X-y
	       :width X-width :height X-height
	       :background *background*
	       :border *foreground*
	       :border-width *border-X-width*
	       :colormap (xlib:screen-default-colormap screen)
	       :cursor (xlib:create-glyph-cursor
			:source-font *cursor-font*
			:source-char (option :cursor-font-index)
			:mask-font *cursor-font*
			:mask-char (option :cursor-font-index)
			:foreground (first colors)
			:background (second colors))
	       :bit-gravity :forget
	       :backing-store :when-mapped
	       :event-mask '(:exposure :button-press :key-press 
			     :substructure-notify :structure-notify))))
    (xlib:set-wm-class win "Nuprl" "Nuprl")
    (setf (xlib:wm-name win) "")
    (setf (xlib:wm-normal-hints win)
	  (xlib:make-wm-size-hints :user-specified-position-p t
				   ;; :user-specified-size-p t
				   :x X-x :y X-y
				   :width X-width :height X-height
				   :min-width (width->X-width *window-minimum-width*)
				   :min-height (height->X-height
						*window-minimum-height*)))
    (setf (xlib:wm-hints win)
	  (xlib:make-wm-hints :input :on
                        ;; :initial-state :normal
                        ))

    win))

;;; Window properties: :width, :height, :cursor-x, :cursor-y, :backing-store
;;; and :actual-top-level-X-window.  The last property is needed because
;;; window managers don't like giving us the information we need.  In
;;; particular, prl's window placement decisions require knowing where
;;; currently mapped windows are placed.  To hack around the problem, after a
;;; window is mapped we find the new parent.  :actual-top-level-X-window is
;;; the new parent if there is one, otherwise it is just the window itself.
                                                                             
(defun window-property (window indicator)
  (getf (cdr window) indicator))

(defun window-X-window (window)
  (car window))

(defun make-window (X-window)
  (list X-window))

(defvar *selected-window*)
(defvar *selected-window-X-window*)
(defvar *selected-window-backing-store*)
(defvar *selected-window-cursor-x*)
(defvar *selected-window-cursor-y*)
(defvar *selected-window-width*)
(defvar *selected-window-height*)

(defun set-window-property (window indicator value)
  (when (and *selected-window*
	     (window-equal window *selected-window*))
    (case indicator
      (:width (setf *selected-window-width* value))
      (:height (setf *selected-window-height* value))
      (:cursor-x (setf *selected-window-cursor-x* value))
      (:cursor-y (setf *selected-window-cursor-y* value))
      (:backing-store (setf *selected-window-backing-store* value))))
  (setf (getf (cdr window) indicator)
	value))

(defsetf window-property set-window-property)

(defun window-equal (w1 w2)
  (xlib:window-equal (window-X-window w1)
		     (window-X-window w2)))

(defun find-window (X-window)
  (find X-window *windows-in-use*
	:test #'(lambda (X-window window)
		  (xlib:window-equal
		    X-window (window-X-window window)))))   

(defun initialize-window-system ()
  (let (display)
    (unwind-protect
	(progn
	  (setf display (xlib:open-display (option :host)))
	  (let* ((font (check-and-open-font display
					    (option :font-name)
					    "fixed"))
		 (screen (xlib:display-default-screen display))
		 (colormap (xlib:screen-default-colormap screen))
		 (root (xlib:screen-root screen))
		 (foreground (xlib:alloc-color
			      colormap
			      (xlib:lookup-color colormap 
						 (option :foreground-color))))
		 (background (xlib:alloc-color
			      colormap 
			      (xlib:lookup-color colormap 
						 (option :background-color)))))
	    (when (eql foreground background)
	      (format
	       t
	       "Foreground and backgound color options map to same hardware color")
	      (setf foreground (xlib:screen-black-pixel screen)
		    background (xlib:screen-white-pixel screen)))
	    (setf *character-X-width* (xlib:max-char-width font)
		  *interline-X-space* (1+ (truncate *character-X-width* 10))
		  *line-X-height* (+ (xlib:max-char-ascent font)
				     (xlib:max-char-descent font)
				     *interline-X-space*)
		  *baseline-X-height* (xlib:max-char-ascent font)
		  *border-X-width* (truncate *character-X-width* 3)
		  *margin-X-width* (truncate *character-X-width* 3)
		  *vertical-X-offset* (if (option :title-bars?)
					  (+ *line-X-height* *margin-X-width*)
					  *margin-X-width*)
		  *foreground* foreground
		  *background* background
		  *gcontext* (xlib:create-gcontext
			      :drawable root
			      :background background
			      :foreground foreground
			      :font font)
		 
		  *reverse-gcontext* (xlib:create-gcontext
				      :drawable root
				      :background foreground
				      :foreground background
				      :font font)
		  *cursor-font* (check-and-open-font display
						     (option :cursor-font-name)
						     "cursor")))
	  (setf *selected-window* nil
		*windows-in-use* nil
		*X-window-output-suppressed?* nil)
	  (setf *display* display)
	  (initialize-application-variables))
      (unless *display* (xlib:close-display display)))))


(defun clear-backing-store (window)
  (let ((width (window-property window :width))
	(store (window-property window :backing-store)))
    (dotimes (i (window-property window :height))
      (dotimes (j width)
	(setf (aref store i j) (ichar->font-index *ispace*))))))

(defun adjust-backing-store-size (window w h)
  (let* ((a (window-property window :backing-store))
	 (old-w (array-dimension a 1))
	 (old-h (array-dimension a 0)))	 
    (when (or (< old-w w) (< old-h h))
      (adjust-array a (list (max old-h h) (max old-w w))
		    :element-type 'fixnum
;		    :element-type 'font-index
		    :initial-element (ichar->font-index *ispace*)))))

(defun initialize-backing-store (window)
  (setf (window-property window :backing-store)
	(make-array (list (window-property window :height)
			  (window-property window :width))
		    :element-type 'fixnum
;		    :element-type 'font-index
		    :initial-element (ichar->font-index *ispace*)
		    :adjustable t)))

;;; If reconfiguration-ok? is t, then the position and shape given to the
;;; window may be different than what is specified.
(defun create-window (x y width height &key (reconfiguration-ok? nil))
  (multiple-value-bind (x y width height)
      (if reconfiguration-ok?
	  (contract-geometry-into-frame x y width height)
	  (values x y width height))
    (multiple-value-bind (X-x X-y X-width X-height)
	(geometry->X-geometry x y width height)
      (let* ((window (make-window (create-X-window X-x X-y X-width X-height)))
	     (X-window (window-X-window window)))
	(push window *windows-in-use*)
	(setf (window-property window :width) width
	      (window-property window :height) height)
	(initialize-backing-store window)
	(setf (window-property window :actual-top-level-X-window)
	      X-window)
	(setf (window-property window :cursor-x) 0
	      (window-property window :cursor-y) 0)
	(xlib:with-state (X-window)
	  (setf (xlib:drawable-x X-window) X-x
		(xlib:drawable-y X-window) X-y
		(xlib:drawable-width X-window) X-width
		(xlib:drawable-height X-window) X-height))
	(xlib:map-window X-window)
	(xlib:display-finish-output *display*)
	window))))

(defun destroy-window (window)
  (setf *windows-in-use*
	(remove window *windows-in-use* :test #'window-equal))
  (xlib:destroy-window (window-X-window window)))

(defun set-X-window-title (X-window string)
  (setf (xlib:wm-name X-window) string
	(xlib:wm-icon-name X-window) string)) 

(defun window-in-use? (window)
  (member window *windows-in-use* :test #'window-equal))

;;; Not implemented yet.  One way to do this is to give a window an
;;; identication stamp at creation time.
(defun replace-lost-window (window)
  (declare (ignore window))
  (reset nil)
  (error "Windows can only be destroyed using ^D.  ~
          You must now abort and reinvoke Nuprl (state will be preserved)."))

(defun select-window (window)  
  (when *selected-window*
    (setf (window-property *selected-window* :cursor-x)
	  *selected-window-cursor-x*)
    (setf (window-property *selected-window* :cursor-y)
	  *selected-window-cursor-y*)
    (unless (or (option :no-warp?)
	        (window-in-use? *selected-window*))
      ;; The previously selected window was destroyed, so warp the mouse to
      ;; keep the input focus.
      (xlib:warp-pointer (window-X-window window) 1 1)))
  (setf *selected-window* window
	*selected-window-X-window* (window-X-window window)
	*selected-window-backing-store* (window-property window :backing-store)
	*selected-window-cursor-x* (window-property window :cursor-x)
	*selected-window-cursor-y* (window-property window :cursor-y)
	*selected-window-width* (window-property window :width)
	*selected-window-height* (window-property window :height)))

(defun with-fast-redrawing (window redrawing-function &rest args)
  (let ((result (let ((*X-window-output-suppressed?* t))
		  (apply redrawing-function args))))
    (refresh-window window)
    result))

(defun draw-title-bar (window)
  (unless *X-window-output-suppressed?*
    (let* ((X-window (window-X-window window))
	   (X-w (xlib:drawable-width X-window)))
      (xlib:clear-area X-window :x 0 :y 0 :width X-w :height *line-X-height*)
      (xlib:draw-rectangle X-window *gcontext* 0 0 X-w *line-X-height* t)
      (xlib:draw-glyphs X-window *reverse-gcontext* *margin-X-width* *baseline-X-height*
			(xlib:wm-name X-window)))))

(defun refresh-window (window)
  (when (option :title-bars?) (draw-title-bar window))
  (unless *X-window-output-suppressed?*
    (let ((a (window-property window :backing-store))
	  (X-window (window-X-window window))
	  (w (window-property window :width)))
      (xlib:clear-area X-window
		       :x 0 :y *vertical-X-offset*
		       :width (xlib:drawable-width (window-X-window window))
		       :height (xlib:drawable-height (window-X-window window)))
      (adjust-output-buffer w)
      (dotimes (i (window-property window :height))
	(multiple-value-bind (X-0 X-y) (coordinates->X-coordinates 0 i)
	  (dotimes (j w) (setf (aref *output-buffer* j)
			       (aref a i j)))
	  (xlib:draw-glyphs
	    X-window
	    *gcontext* X-0 (+ *baseline-X-height* X-y)
	    *output-buffer* :start 0 :end w :width (* w *character-X-width*)))))))

(defun redo-backing-store (window)
  (adjust-backing-store-size
    window (window-property window :width) (window-property window :height))
  (clear-backing-store window)
  (let ((*X-window-output-suppressed?* t)
	(initially-selected-window *selected-window*))
    (recompute-window-contents-and-redraw window)
    (select-window initially-selected-window)))

;;; Size may have changed.
(defun redraw-window (window)
  (redo-backing-store window)
  (refresh-window window))

(defun set-cursor (window x y)
  (setf (window-property window :cursor-x) x
	(window-property window :cursor-y) y))

;;; Optional argument because called from prl.  Doesn't touch title-bar area.
(defun clear-window (&optional (window *selected-window*))
  (unless *X-window-output-suppressed?*
    (xlib:clear-area (window-X-window window)
		     :x 0 :y *vertical-X-offset*
		     :width (xlib:drawable-width (window-X-window window))
		     :height (- (xlib:drawable-height (window-X-window window))
				*vertical-X-offset*)))
  (clear-backing-store window)
  (set-cursor window 0 0))

(defun modify-window-title-bar (window start string &optional (clear-to-end? nil))
  ;; the supplied strings must not contain "@"
  (let* ((start (or start 0))  ; prl needs this.
	 (host-name (or (local-host) ""))
	 (suffix (if host-name
		     (format nil " @ ~A" host-name)
		     ""))
	 (long-title (string (xlib:wm-name (window-X-window window))))
	 (title (if (search suffix long-title)
		    (subseq long-title 0 (- (length long-title)
					    (length suffix)))
		    long-title))
	 (title-length (length title))
	 (str-length (length string))
	 (new-title
	  (cond ((>= start title-length)
		 (concatenate 'string title string))
		((or (>= (+ start str-length) title-length)
		     clear-to-end?)
		 (concatenate 'string (subseq title 0 start) string))
		(t
		 (concatenate 'string
			      (subseq title 0 start)
			      string
			      (subseq title (+ start str-length))))))
	 (new-long-title
	  (if (option :host-name-in-title-bars?)
	      (concatenate 'string new-title suffix)
	      new-title)))	       
    (set-X-window-title
     (window-X-window window)
     new-long-title))
  (when (option :title-bars?) (draw-title-bar window)))

(defun run-application (&optional (host nil))
  (unless *initial-key-bindings*
    (setf *initial-key-bindings* *key-bindings*))
  (when host (setf (getf *options* :host) host))
  (unless (or *display*  *init-file-loaded?*)
    (let ((init-file (merge-pathnames *init-file-name*
				      (user-homedir-pathname))))
      (when (probe-file init-file) (load init-file))
      (setf  *init-file-loaded?* t)))
  (when host (setf (getf *options* :host) host)) 
  (unless (getf *options* :host)
     (error "You must supply a host name."))
  (check-options)
  (setf *effected-options* (map 'list #'identity *options*))
  ;; checking options may reset.  This is indicated by *display* = nil.
  (unless *display* (initialize-window-system))
  (application))

(defun X-parent (window)
  (multiple-value-bind (children parent root)
      (xlib:query-tree (window-X-window window))
    (declare (ignore children root))
    parent))

;;; gross hack:  force prl to select new window by generating
;;; a bogus mouse-jump.
(defun get-character ()
  (draw-or-erase-text-cursor t)
  (xlib:event-case (*display* :discard-p t :force-output-p t)
    (exposure  
      (window count)
      (when (zerop count)
	(let ((w (find-window window)))
	  (when w
	    (draw-or-erase-text-cursor nil)
	    (refresh-window w)
	    (draw-or-erase-text-cursor t))))
      nil)
    (button-press
      (window x y code)
      (draw-or-erase-text-cursor nil)
      (multiple-value-bind (x y) (X-coordinates->coordinates x y)
	(or (let ((w (find-window window)))
	      (when w (mouse-blip w code x y)))
	    (draw-or-erase-text-cursor t))))
    (key-press
      (state window code)
      (draw-or-erase-text-cursor nil)
      (or (maybe-process-char-immediately 
	    window (keycode->ichar code state))
	  (draw-or-erase-text-cursor t)))	   
    (configure-notify
      (window width height)
      (draw-or-erase-text-cursor nil)
      (multiple-value-bind (width height)
	  (X-size->size width height)
	(when (or (zerop width)
		  (zerop height))
	  (error "Width or height too small.  Abort and reset."))
	(let* ((window (find-window window)))
	  (when (and window
		     (or (not (= width (window-property window :width)))
			 (not (= height (window-property window :height)))))
	    (setf (window-property window :width) width
		  (window-property window :height) height)
	    ;; no need to refresh since an exposure event is due.
	    (redo-backing-store window))))
      (draw-or-erase-text-cursor t)
      nil)
    (destroy-notify
      (window)
      (when (find-window window) (replace-lost-window window)))
    (reparent-notify
      (window parent)
      (let ((w  (find-window window)))
	(when w (setf (window-property w :actual-top-level-X-window)
		      parent))
	nil))
    (otherwise nil)))


(defun draw-or-erase-text-cursor (drawp)
  (unless *X-window-output-suppressed?*
    (multiple-value-bind (x y)
	(coordinates->X-coordinates
	 *selected-window-cursor-x* *selected-window-cursor-y*)
      (xlib:draw-rectangle
       *selected-window-X-window* (if drawp *gcontext* *reverse-gcontext*)
       x y
       *character-X-width* *line-X-height* t)
      (xlib:draw-glyph
       *selected-window-X-window* (if drawp *reverse-gcontext* *gcontext*)
       x
       (+ *baseline-X-height* y)
       (aref *selected-window-backing-store*
	     *selected-window-cursor-y* *selected-window-cursor-x*)
       :width *character-X-width*)))
  nil)


(defun move-cursor (x y)
  (setf *selected-window-cursor-x* x
	*selected-window-cursor-y* y))

(defun advance-cursor (n)
  (multiple-value-bind (q r)
      (truncate (+ *selected-window-cursor-x* n)
		*selected-window-width*)
    (move-cursor r (mod (+ *selected-window-cursor-y* q)
			*selected-window-height*))))

(defun retreat-cursor (n)
  (let ((k (* *selected-window-width* *selected-window-height*)))
    (advance-cursor (- k (mod n k)))))

(defun move-cursor-to-new-line ()
  (move-cursor 0 (mod (1+ *selected-window-cursor-y*)
		      *selected-window-height*)))

(defun put-character (ch)
  (let* ((index (ichar->font-index ch)))
    (unless *X-window-output-suppressed?*
      (multiple-value-bind (X-x X-y)
	  (coordinates->X-coordinates *selected-window-cursor-x*
				      *selected-window-cursor-y*)
	(xlib:clear-area *selected-window-X-window* :x X-x :y X-y
			 :width *character-X-width* :height *line-X-height*)
	(xlib:draw-glyph
	  *selected-window-X-window* *gcontext* X-x
	  (+ *baseline-X-height* X-y) index :width *character-X-width*)))
    (setf (aref *selected-window-backing-store*
		*selected-window-cursor-y* *selected-window-cursor-x*)
	  index)
    (advance-cursor 1)))

(defun put-string (istring)
  (unless (= 0 (length istring))
    (let* ((x *selected-window-cursor-x*)
	   (y *selected-window-cursor-y*)
	   (k (min (- *selected-window-width* x)
		   (length istring))))
      (adjust-output-buffer k)
      (let ((j 0)) (mapc #'(lambda (ch)
			     (let ((i (ichar->font-index ch)))
			       (setf (aref *selected-window-backing-store*
					   y (+ x j))
				     i)
			       (setf (aref *output-buffer* j)
				     i)
			       (incf j)))
			 (subseq istring 0 k)))
      (unless *X-window-output-suppressed?*
	(multiple-value-bind (X-x X-y) (coordinates->X-coordinates x y)
	  (xlib:clear-area *selected-window-x-window*
			   :x X-x :y X-y :width (* k *character-X-width*)
			   :height *line-X-height*)
	  (xlib:draw-glyphs
	    *selected-window-x-window* *gcontext*
	    X-x (+ *baseline-X-height* X-y)
	    *output-buffer* :start 0 :end k :width (* k *character-X-width*))))
      (advance-cursor k)
      (put-string (subseq istring k)))))

(defun put-new-line ()
  (clear-to-end-of-line)
  (move-cursor-to-new-line)
  (clear-to-end-of-line))  

(defun put-fresh-line ()
  (unless (zerop *selected-window-cursor-x*)
    (move-cursor-to-new-line))
  (clear-to-end-of-line))

(defun put-message (window istring)
  (let ((starting-window *selected-window*))
    (select-window window)
    (put-fresh-line)
    (put-string istring)
    (clear-to-end-of-line t)
    (select-window starting-window)))

(defun clear-forward (m &optional (move-cursor? nil))
  (let ((x *selected-window-cursor-x*)
	(y *selected-window-cursor-y*))
    (clear-forward-moving-cursor m)
    (unless move-cursor? (move-cursor x y))))

(defun clear-forward-moving-cursor (m)
  (unless (<= m 0)
    (let* ((x *selected-window-cursor-x*)
	   (y *selected-window-cursor-y*)
	   (k (min (- *selected-window-width* x)
		   m)))
      (unless *X-window-output-suppressed?*
	(multiple-value-bind (X-x X-y)
	    (coordinates->X-coordinates x y)
	  (xlib:clear-area (window-X-window *selected-window*)
			   :x X-x :y X-y
			   :width (* k *character-X-width*)
			   :height *line-X-height*)))
      (dotimes (j k) (setf (aref *selected-window-backing-store* y (+ x j))
			   (ichar->font-index *ispace*)))
      (advance-cursor k)
      (clear-forward-moving-cursor (- m k)))))

(defun clear-backward (m &optional (move-cursor? nil))
  (let ((x *selected-window-cursor-x*)
	(y *selected-window-cursor-y*))
    (retreat-cursor m)
    (clear-forward m)
    (unless move-cursor? (move-cursor x y))))

(defun clear-to-end-of-line (&optional (move-cursor? nil))
  (clear-forward (- *selected-window-width* *selected-window-cursor-x*)
		 move-cursor?))

(defvar *current-input-line* nil)
(defvar *current-prompt* nil)

;;; Repeatedly selects window until end of input.
(defun get-line (window prompt splicer)
  ;; Print the prompt in the command window, read chars from 'get-character'
  ;; until a (NL) or (EXIT) character and return the list read.
  ;; Whenever the result of 'get-character' is not a fixnum and not (EXIT),
  ;; apply 'splicer' to it, and splice the resulting list into the list
  ;; of characters read so far.  Thus 'splicer' should always yield a
  ;; list of fixnums, unless it yields the atom redisplay-line, in
  ;; which case the prompt and chars typed so far are redisplayed.
    (let ((*current-input-line* nil)
	  (*current-prompt* prompt))
      (select-window window)
      (redisplay-line)
      (flet ((input ()
	       (let ((ch (get-character)))
		 (select-window window)
		 ch)))
	(do ((ch (input) (input)))
	    ((or (equal ch '(NL)) (equal ch '(EXIT)))
	     (put-new-line)
	     (xlib:display-finish-output *display*)
	     (push ch *current-input-line*)
	     (reverse *current-input-line*))
	  (cond ((graphic-ichar? ch)
		 (put-character ch)
		 (push ch *current-input-line*))
		((ichar= ch *idelete*)
		 (when *current-input-line*
		   (clear-backward 1 t)
		   (pop *current-input-line*)))
		((ichar= ch *i-kill-line*)
		 (clear-backward (+ (length prompt) (length *current-input-line*))
				 t)
		 (put-string prompt)
		 (setf *current-input-line* nil))
		(t
		 (let ((splice-str (funcall splicer ch)))
		   (if (eql splice-str 'redisplay-line)
		       (redisplay-line)
		       (progn
			 (put-string splice-str)
			 (setf *current-input-line*
			       (append (reverse splice-str)
				       *current-input-line*)))))))))))

(defun redisplay-line ()
  (put-fresh-line)
  (put-string *current-prompt*)
  (put-string (reverse *current-input-line*)))

(defun snapshot-window (window)
  (with-open-file (s (or *snapshot-file*
			 (merge-pathnames "snapshot.text" (user-homedir-pathname)))
		     :direction :output
		     :if-exists :append
		     :if-does-not-exist :create)
    (format s "~3%~A~2%" (xlib:wm-name (window-X-window window)))
    (let ((a (window-property window :backing-store)))
      (dotimes (y (window-property window :height)) 
	(dotimes (x (window-property window :width))
	  (let* ((x (if *output-for-latexize*
			(font-index->char-for-latexize (aref a y x))
			(font-index->char-or-string (aref a y x)))))
	    (if (stringp x)
		(princ x s)
		(write-char x s))))
	(format s "~%")))))

(defun reset (&optional (reset-key-bindings? t))
  (when reset-key-bindings?
    (setf *key-bindings* *initial-key-bindings*))
  (when *display* (xlib:close-display *display*))
  (setf *display* nil)
  (reset-application))


;;;----------------------------------------------------------------------------------

;;; Remembers arguments to previous call.
(defun nuprl (&optional host)
  (in-package "NUPRL")
  (run-application host))

(defun cl-user::nuprl (&optional host)
  (nuprl host))

(defun createw (top bottom left right &key (library nil) (allow-shift nil))
  (declare (ignore library))
  (create-window left top (1+ (- right left)) (1+ (- bottom top))
		 :reconfiguration-ok? allow-shift))

(defun destroyw (window)
  (destroy-window window))

(defun selectw (window)
  (select-window window))

(defun getchr ()
  (get-character))

(defun Preadline (prl-prompt splicer)
  (get-line *selected-window* prl-prompt splicer))

(defun putc (ch)
  (put-character ch)
  *selected-window-cursor-x*)

(defun changesizew (w y1 y2 x1 x2)
  (declare (ignore w y1 y2 x1 x2))
  ;; A stub.
  nil)

(defun enter-prl-state$ ()
  nil)

(defun leave-prl-state$ ()
  nil)

;;; There's no easy way to do this.  It doesn't matter, since
;;; it's only used as a convenience.
(defmacro with-terminal-io-on-frame (&body body)
  `(progn . ,body))

(defun movecursor (x y) (move-cursor y x) x)

(defun putnl ()
  (put-new-line))

(defun putstr (str)
  (put-string str))

(defun display-message (str)
  (put-message display-message-window str)
  (when (window-equal display-message-window cmd-window$)
    (let ((w *selected-window*))
      (select-window cmd-window$)
      (redisplay-line)
      (select-window w))))

(defun erase-to-end-of-line ()
  (clear-to-end-of-line))

(defun erase-n-chars (n)
  (clear-forward n t))

(defun clear-screen ()
  nil)

(defun setheaderw (start str &optional (clear-to-end-p nil))
  (modify-window-title-bar *selected-window* start
			   (map 'string #'ichar->char str)
			   clear-to-end-p))

(defun get-current-selected-window ()
  ;; An ugly little function for the hacks in lib.lisp.
  *selected-window*)

;;; stub.
(defun initw () (values))

(defun window-width (w)
  (window-property w :width))

(defun window-height (w)
  (window-property w :height))

;;; Note that timing-related problems can occur, since Nuprl asks for
;;; window-shape values separately.
(defun getw-top (w)
  (multiple-value-bind (x y) (window-coordinates w)
    (declare (ignore x))
    y))

(defun getw-bot (w)
  (1- (+ (getw-top w) (window-property w :height))))

(defun getw-left (w)
  (window-coordinates w))

(defun getw-right (w)
  (1- (+ (getw-left w) (window-property w :width))))


