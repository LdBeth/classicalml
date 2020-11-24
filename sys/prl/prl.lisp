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

;-- (module prl)


;--
;-- globals for break/debug handlers
;--


;--
;-- globals having to do with current state of prl system 
;--

(defvar prl-running$ nil)


#|
;;; If t, command and eval processing are disabled so that only ML
;;; can be entered in the command window.  If nil, prl runs as usual.
(defvar *ml-mode-only?* nil
    "Iff command and eval processing have been disabled.")

(defun process-cmd-window-input ()
  (declare (special cmd-window$ cur-window$))
  (cond (*ml-mode-only?*
	 (selectw cmd-window$)
	 (ml-mode$)
	 (selectw cur-window$))
	(t
	 (process-cmd$))))
|#

;--
;-- window descriptors
;--

(global cmd-window$)            ;-- command/status window number
(global lib-window)             ;-- library window number

(global cur-window$)            ;-- Number of currently selected window.  This
                                ;-- is usually a view window, the lib and cmd
                                ;-- windows are selected explicitly for small
                                ;-- periods.  However, it may be the cmd window
                                ;-- if there are no active views.  Reads/writes
                                ;-- to the cmd/status window return to this     
                                ;-- window after completion.  The command parser
                                ;-- returns to this window after completing
                                ;-- commands.  Commands may change this
                                ;-- variable if they wish.



;--
;-- prl()
;--
;--   Main routine of PRL system:
;--     a read-eval-print loop in which chars read
;--     from the window interface are either processed
;--     locally or directed to the appropriate system
;--     module.
;--
(defun prl ()
  (when prl-running$
    (error "Nuprl is already running."))
  (unwind-protect
      (prl-loop)
    (setq prl-running$ nil)))

(defun prl-loop ()
    (prl-init$)
    (<- prl-running$ t)
    (Ploop
        (local cmd-char$ nil
        )
        (while prl-running$)
        (do
            (Pif (zerop num-regions) -->
                (process-cmd$)
        
             || t -->
                (<- cmd-char$ (getchr))
       
                (Pif (and (consp cmd-char$) (eql (car cmd-char$) 'CMD)) -->
                    (process-cmd$)
				    
                 || (zerop num-regions) -->
                    ;-- num-regions could have gone zero as a result of
                    ;-- the call to getchar (a menu-kill-event).
                        (display-message '#.(istring "No active region (ignored)."))

                 || (and (consp cmd-char$) (eql (car cmd-char$) 'REGION)) -->
                    (<- cur-region-index (rem (1+ *-*) num-regions))
                    (<- cur-region (nthelem 
                                       (1+ cur-region-index)
                                       used-regions
                                   )
                    )

                 || (and (consp cmd-char$)
                         (or (eql (car cmd-char$) 'MOUSE-SEL)
                             (eql (car cmd-char$) 'MOUSE-JUMP)
                         )
                    ) -->
                    (process-mouse-char$ cmd-char$)
    
                 || (eql (sel region (cur-region) obj-kind) 'PROOF) -->
                    (red cmd-char$)
                
                 || (member (sel region (cur-region) obj-kind) '(TTREE EVAL)) -->
                    (ted cmd-char$)
            
                 fi)

                (Pif (zerop num-regions) -->
                    ;-- all active regions are gone - return to the cmd window
                        (<- cur-window$ cmd-window$)
                        (selectw cur-window$)
        
                 || (not (window-equal cur-window$
				       (sel region (cur-region) window)
                         )
                    ) -->
                    ;-- the region has changed, cur-window$ should be set
                        (<- cur-window$ (sel region (cur-region) window))
                        (selectw cur-window$)

                 fi)

             fi)
        )
    )
    (clear-screen)
    (leave-prl-state$)
    (patom "PRL Terminated.")
    (terpri)
    nil
)


;--
;-- prl-init$ ()
;--
;--   PRL initialization routine
;--   

;;; Symbolics version: setting this to nil and then reinvoking prl
;;; will cause the window system to be reinitialized, but will 
;;; otherwise not affect the state.  Other versions: this should
;;; never be set to nil (excepting the second form below).
(global prl-initialized$)

(eval-when (load eval)
    (<- prl-initialized$ nil)
)

(defvar cmd-status-hdr$ '#.(istring " Nuprl Command/Status"))

(defconstant *cmd-status-hdr-prefix* '#.(istring " Nuprl Command/Status"))

(defvar *herald-has-been-shown-p* nil)

(defun prl-init$ ()
    (declare (special display-message-window))
    (Pif prl-initialized$ -->
	(selectw cmd-window$)
	(setheaderw nil cmd-status-hdr$ t)	; the header may have changed.
	(selectw cur-window$)
        (enter-prl-state$)

     || t -->
        ;; initialize the window system.
        (<- num-regions 0)
	(<- region (new region-array))
	(<- view-stack nil)
	(<- used-regions nil)
	(<- free-regions nil)
	(Ploop (local i 0)
	       (while (< i max-num-regions))
	       (do
		 (<- free-regions (cons i *-*))
		 (<- i (1+ i))))
        (initw)

	(unless *herald-has-been-shown-p*
	  (show-prl-herald)
	  (setq *herald-has-been-shown-p* t))

        ;-- create appropriately sized library and command/status windows
	;-- cmd after lib so cmd is on top                
            (Plet (top    0
		  third1 (truncate SCRHEIGHT 3)
		  third2 (truncate (* 2 SCRHEIGHT) 3)
                  bot    (- SCRHEIGHT 2)
                 )

                (<- lib-window
		     (createw
		       (+ third2 2)
		       bot
		       1
		       (- SCRWIDTH 1)
		       :library t
		       :allow-shift t)
                )

		(selectw lib-window)
                (setheaderw nil '#.(istring " Library ") t)

                (<- cmd-window$ (createw (+ third1 3)
                                    (- third2 2)
                                    1
                                    (1- (TRUNCATE SCRWIDTH 2))
				    :allow-shift t
                                )
                )
                (selectw cmd-window$)
                (setheaderw nil cmd-status-hdr$ t)

                (<- cur-window$ cmd-window$)
                (<- display-message-window cmd-window$)
		(lib-page 'top)
            )

        (<- prl-initialized$ t)

     fi)
)


;-- initialize ()
;-- 
;-- The initializations that are independent of the terminal type, and thus
;-- which can be done before prl is dumped.  This function should be called
;-- from the make file.
;-- 
(defun initialize ()

  (setq prl-initialized$ nil)
  (setq prl-running$ nil)

  ;; Initialize ML. (idempotent)
  (init-ml)
  (note-primitive-ml-objects)    

  ;; Initialize library routines
  (lib-init)
        
  ;; Initialize library I/O routines.
  (lib-I/O-init$)

  ;; Initialize ref.
  (ref-init)

  ;; Initialize ted.
  (ted-init)

  (red-init)

  ;; Initialize check and parse routines.
  (scan-table-init)
  (parse-table-init)

  ;; Initialize some rules.  (Must be after parser init.)
  (init-monotonicity)		
  (init-division)

  ;; Initialize the evaluator
  (eval-init)

  ;; Initialize the extractor
  (extract-init)

  ;; Initialize the substitution mechanism
  (subst-init)

  (init-equal-terms)
  (init-equal-term-hash)

  t

  )

(defun reset-prl ()
  (declare (special library$))
  (let* ((saved-lib library$))
    (initialize)
    (setq library$ saved-lib))
  t)


;;; "Mouse mode" is obsolete.

;--
;-- enter-mouse-mode ()
;--
;-- Called when explicit-mouse-mode is entered (when MOUSE key is hit).
;-- Changes the header in Cmd/Status window to indicate keyboard
;-- input is in this mode.  After returning, the window that was
;-- selected before 'enter-mouse-mode' was called, is reselected.
#|
(defun enter-mouse-mode ()

   (selectw cmd-window$)
   (setheaderw 13 '#.(istring "(MOUSE-MODE)"))
)
|#

;--
;-- leave-mouse-mode ()
;--
;-- Called when explicit-mouse-mode is exited (when DIAG key is hit).
;-- Changes the header in Cmd/Status window to indicate keyboard input
;-- is back to normal.  After returning, the window that was selected
;-- before calling 'leave-mouse-mode' will be reselected.
;--
#|
(defun leave-mouse-mode ()

   (selectw cmd-window$)
   (setheaderw 13 '#.(istring "            "))
   (setheaderw nil cmd-status-hdr$)
   (reset-menu$)
)
|#

;--
;-- process-mouse-char$ (char:prlchar)
;--
;--     char is (MOUSE-SEL window col row) or (MOUSE-JUMP window col row).
;--     Find the region containing the specified screen location and inform
;--     the manager of that region (ted or red) of the event.
;--     If MOUSE-SEL on library window and ted is active region then "type"
;--     object name into ted window for user.  If MOUSE-JUMP on libary window
;--     then display the object moused is detail.
;--

(defun process-mouse-char$ (char)

    (Plet (kind   (car char)
          window (cadr char)
          col    (caddr char)
          row    (cadddr char)
          reg    nil
         )

	 (Pif (window-equal window lib-window) -->
	     (Plet (obj (map-mouse-to-lib-object row col)
		   str nil
		  )
		  (Pif (and (eql kind 'MOUSE-SEL)
			   (not (null obj))
			   (member (sel region (cur-region) obj-kind) '(TTREE EVAL))
		      ) -->
		      (<- str (istring obj))
		      (Ploop (while str)
			    (do
			      (ted (car str))
			      (<- str (cdr str))
			    )
		      )

		   || (and (eql kind 'MOUSE-JUMP)
			   (not (null obj))
		      ) -->
		      (display-lib-object-in-detail obj)

		   || (eql kind 'MOUSE-JUMP) -->
		      (mouse-scroll-lib row col)

		   fi)
	     )

          || (and (window-equal window cmd-window$)
		  (or (eql kind 'MOUSE-JUMP) (eql kind 'MOUSE-SEL))) -->
	     (process-cmd$)

          || t -->	 
	     ;-- try to find the region containing the mouse event -- if found
	     ;-- set reg to it, else leave reg nil
		 (for (r in used-regions)
		      (do
			(Pif (and (window-equal (sel region (r) window) window)
				 (not (> (sel region (r) top)   row))
				 (not (<    (sel region (r) bot)   row))
				 (not (> (sel region (r) left)  col))
				 (not (<    (sel region (r) right) col))
			    ) -->
			    (<- reg r)
			 fi)
		      )
		 )
    
	     (Pif reg -->
		 (Pif (and (or (eql kind 'MOUSE-JUMP) (eql kind 'MOUSE-SEL))
			  (not (equal reg cur-region))
		     ) -->
		     ;-- MOUSE-JUMP is to non-current region,
		     ;-- just switch to that region
			 (<- cur-region reg)
			 (<- cur-region-index
			     (- (length used-regions)
				(length (member cur-region used-regions))
			     )
			 )
    
		  || t -->
		     ;-- either a MOUSE-JUMP in cur-region, or a MOUSE-SEL
			 (Pif (member (sel region (reg) obj-kind) '(TTREE EVAL)) -->
			     (ted-mouse-char reg row col kind)
			
			  || t -->
			     (red-mouse-char reg row col kind)
    
			  fi)
    
		  fi)
    
	      fi)

          fi)
    
    )
)



;--
;-- PRL command list
;--

(constant prl-command-list$
          (list ;;'#.(istring "archive")
                ;;'#.(istring "autosave")
		'#.(istring "bottom")
                '#.(istring "check")
		'#.(istring "copystate")
                '#.(istring "create")
                '#.(istring "delete")
		'#.(istring "down")
                '#.(istring "dump")
                '#.(istring "eval")
                '#.(istring "exit")
                ;;'#.(istring "gcprint")
                '#.(istring "jump")
		'#.(istring "kill")
                '#.(istring "lisp")
                '#.(istring "load")
                '#.(istring "ml")
                '#.(istring "move")
                '#.(istring "restore")
                '#.(istring "save")
                '#.(istring "scroll")
                ;;'#.(istring "shell")
		'#.(istring "states")
		'#.(istring "top")
		'#.(istring "up")
                '#.(istring "view")
           )
)


;--
;-- process-cmd$
;--
;--   read a line of input, echo it in the command window,
;--   and perform the actions appropriate to the command.
;--

(global cmd-text$)  ;-- text of command (list of fixnum chars)
(global cmd-token$) ;-- lisp atom most recently scanned from cmd-text$
(global cmd-token-kind$) ;-- kind of cmd-token
                         ;--   identifier | number | end-cmd | delimiter

(defun process-cmd$ ()
    (Plet (ret-msg$     nil  ;-- result of 'catch' surrounding calls
                            ;--   to some command procedures
         )

        (<- cmd-text$ (readcmd '#.(istring "P>") #'(lambda (x) (cmd-splicer x))))
        
        (selectw cmd-window$)

        (scan-cmd$)

        (Pif (expand-cmd-word$)  -->

            (display-message '#.(istring "Abbreviated command is ambiguous."))

         || t  -->

            (Pif (eql cmd-token$ '|lisp|) -->
                (lisp-mode$)

             || (eql cmd-token$ '|ml|) -->
                (ml-mode$)

	     || (eql cmd-token$ '|eval|) -->
	        (eval-mode$)

             || (eql cmd-token$ '|shell|) -->
                (display-message '#.(istring "Obsolete command.")) #|(prl-shell$)|#

             || (eql cmd-token$ '|load|) -->
                (Pif (<- ret-msg$ (catch 'CMDERR (load-cmd$)))  -->     ;
                    (display-message ret-msg$)
                 fi)
                
            || (eql cmd-token$ '|dump|) -->
                (Pif (<- ret-msg$ (catch 'CMDERR (dump-cmd$)))  -->
                    (display-message ret-msg$)
                 fi)
    
             || (eql cmd-token$ '|create|) -->
                (Pif (<- ret-msg$ (catch 'CMDERR (create-cmd$)))  -->
                    (display-message ret-msg$)
                 fi)
    
             || (eql cmd-token$ '|delete|) -->
                (Pif (<- ret-msg$ (catch 'CMDERR (delete-cmd$)))  -->
                    (display-message ret-msg$)
                 fi)
    
             || (eql cmd-token$ '|jump|) -->
                (Pif (<- ret-msg$ (catch 'CMDERR (jump-cmd$)))  -->
                    (display-message ret-msg$)
                 fi)
    
             || (eql cmd-token$ '|move|) -->
                (Pif (<- ret-msg$ (catch 'CMDERR (move-cmd$)))  -->
                    (display-message ret-msg$)
                 fi)
    
             || (eql cmd-token$ '|scroll|) -->
                (Pif (<- ret-msg$ (catch 'CMDERR (scroll-cmd$)))  -->
                    (display-message ret-msg$)
                 fi)

             || (eql cmd-token$ '|down|) -->
                (Pif (<- ret-msg$ (catch 'CMDERR (down-cmd$)))  -->
                    (display-message ret-msg$)
                 fi)
    
             || (eql cmd-token$ '|up|) -->
                (Pif (<- ret-msg$ (catch 'CMDERR (up-cmd$)))  -->
                    (display-message ret-msg$)
                 fi)
    
             || (eql cmd-token$ '|bottom|) -->
                (Pif (<- ret-msg$ (catch 'CMDERR (bottom-cmd$)))  -->
                    (display-message ret-msg$)
                 fi)
    
             || (eql cmd-token$ '|top|) -->
                (Pif (<- ret-msg$ (catch 'CMDERR (top-cmd$)))  -->
                    (display-message ret-msg$)
                 fi)
    
             || (eql cmd-token$ '|archive|) -->
	        (display-message '#.(istring "Obsolete command."))
                #|(Pif (<- ret-msg$ (catch 'CMDERR (archive-cmd$)))  -->
                    (display-message ret-msg$)
                 fi)|#
    
             || (eql cmd-token$ '|check|) -->
                (Pif (<- ret-msg$ (catch 'CMDERR (check-cmd$)))  -->
                    (display-message ret-msg$)
                 fi)
                              
             || (eql cmd-token$ '|view|) -->
                (Pif (<- ret-msg$ (catch 'CMDERR (view-cmd$)))  -->
                    (display-message ret-msg$)
                 fi)

             || (eql cmd-token$ '|save|) -->
                (Pif (<- ret-msg$ (catch 'CMDERR (save-cmd$))) -->
                    (display-message ret-msg$)
                 fi)

             || (eql cmd-token$ '|restore|) -->
                (Pif (<- ret-msg$ (catch 'CMDERR (restore-cmd$))) -->
                    (display-message ret-msg$)
                 fi)

	     || (eql cmd-token$ '|kill|) -->
                (Pif (<- ret-msg$ (catch 'CMDERR (kill-cmd$))) -->
                    (display-message ret-msg$)
                 fi)

	     || (eql cmd-token$ '|states|) -->
	        (states-cmd$)

             || (eql cmd-token$ '|copystate|) -->
                (Pif (<- ret-msg$ (catch 'CMDERR (copystate-cmd$))) -->
                    (display-message ret-msg$)
                 fi)
            
             || (eql cmd-token$ '|gcprint|) -->
	        (display-message '#.(istring "Obsolete command."))
                #|(Pif (<- ret-msg$ (catch 'CMDERR (gcprint-cmd$))) -->
                    (display-message ret-msg$)
                 fi)
                |#
            
             || (eql cmd-token$ '|autosave|) -->
	        (display-message '#.(istring "Obsolete command."))
                #|(Pif (<- ret-msg$ (catch 'CMDERR (autosave-cmd$))) -->
                    (display-message ret-msg$)
                 fi)
                |#
    
             || (eql cmd-token$ 'end-cmd) -->
                nil ;-- ignore the empty command

             || (eql cmd-token$ 'exit-token) -->
                (display-message '#.(istring "To leave PRL type 'exit'."))

             || (eql cmd-token$ '|exit|) -->
                (<- prl-running$ nil)
;;;;;;;;;CHECK IF LIB MODIFIED BUT NOT DUMPED
    
             || t --> 
                (display-message '#.(istring "Unrecognized command (ignored)."))
    
             fi)
         fi)

        (selectw cur-window$)

    )
)


;--
;-- readcmd (prompt:prlstring, splicer:function)
;--
;--   Display the prompt in the command window, read a line and echo it
;--   there, and re-select the current window.  Pass the splicer to
;--   readline to translate any special characters that are entered.
;--

(defun readcmd (prompt splicer)
  (let ((result nil))
    (selectw cmd-window$)
    (<- result (Preadline prompt splicer))
    (selectw cur-window$)
    result))


;--
;-- cmd-splicer (char:character)
;--
;--   The special character char has been read during a readline.
;--   If it is a MOUSE-SEL in a ted window then find the def it refers
;--   to and yield a fixnum list of its name.  This means people can
;--   mouse-sel on defs and get their names entered into the cmd.
;--   If MOUSE-SEL on a library window object, then yield the fixnum
;--   list for the name of the moused object.  If MOUSE-JUMP on a library
;--   window, then display the moused object in detail.
;--

(defun cmd-splicer (char)

   (Pif (and (consp char)
            (or (eql (car char) 'MOUSE-SEL) (eql (car char) 'MOUSE-JUMP))
       ) -->

       (Plet (kind   (car char)
	     window (cadr char)
	     col    (caddr char)
	     row    (cadddr char)
	     reg    nil
	    )

	    (Pif (window-equal window lib-window) -->
		(Plet (obj (map-mouse-to-lib-object row col))
		     (Pif (and (not (null obj)) (eql kind 'MOUSE-SEL)) -->
			 (istring obj)

		      || (and (not (null obj)) (eql kind 'MOUSE-JUMP)) -->
		         (display-lib-object-in-detail obj)
			 'redisplay-line  ;-- cause the input so far to be redisplayed

		      || (eql kind 'MOUSE-JUMP) -->
		         (mouse-scroll-lib row col)
			 nil

		      || t -->
			 nil

		      fi)
		)

	     || (eql kind 'MOUSE-SEL) -->
		;-- try to find the region containing the mouse event -- if found
		;-- set reg to it, else leave reg nil
		    (for (r in used-regions)
			 (do
			   (Pif (and (window-equal (sel region (r) window) window)
				    (not (> (sel region (r) top)   row))
				    (not (<    (sel region (r) bot)   row))
				    (not (> (sel region (r) left)  col))
				    (not (<    (sel region (r) right) col))
			       ) -->
			       (<- reg r)
			    fi)
			 )
		    )
       
		(Pif reg -->
		    (Pif (member (sel region (reg) obj-kind) '(TTREE EVAL)) -->
			(ted-splicer reg row col kind)
    
		     || t -->
			nil
    
		    fi)
    
		 || t -->
		    nil
    
		 fi)

	     fi)
       )
   fi)

)





;--
;-- scan-cmd$ ()
;--
;--   Scan the next token (and remove its chars) from cmd-text$.
;--   Leave the result in cmd-token$.  This will be an "alpha-numeric"
;--   atom, a number, an atom containing a single special character,
                       ;--   or the atom end-cmd.
;--

(constant letters$ '#.(istring "@_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"))
(constant digits$  '#.(istring "0123456789"))

(defun scan-cmd$ ()

    ;-- skip over leading blanks
        (Ploop
            (while (equal (car cmd-text$) #.(ichar #\space)))
            (do
                (<- cmd-text$ (cdr cmd-text$))
            )
        )

    (Pif (member (car cmd-text$) letters$) -->

        ;-- build an atom containing the letters and digits
            (<- cmd-token$ nil)
            (Ploop
                (while (or (member (car cmd-text$) letters$)
                           (member (car cmd-text$) digits$)
                       )
                )
                (do
                    (<- cmd-token$ (cons (car cmd-text$) cmd-token$))
                    (<- cmd-text$ (cdr cmd-text$))
                )
            )
            (<- cmd-token$ (implode (nreverse cmd-token$)))
            (<- cmd-token-kind$ 'identifier)

     || (member (car cmd-text$) digits$) -->

        ;-- build a number from the digits
            (<- cmd-token$ 0)
            (<- cmd-token-kind$ 'number)

            (Ploop
                (while (member (car cmd-text$) digits$))
                (do
                    (<- cmd-token$ (+ (* 10 cmd-token$)
                                      (- (car cmd-text$) #.(ichar #\0))
                                   )
                    )
                    (<- cmd-text$ (cdr cmd-text$))
                )            
            )

     || (equal (car cmd-text$) '(NL)) -->

        ;-- end of cmd-text$ found, return end-cmd
            (<- cmd-token$ 'end-cmd)
            (<- cmd-token-kind$ 'end-cmd)

     || (equal (car cmd-text$) '(EXIT)) -->

        ;-- EXIT char found, return exit-token
            (<- cmd-token$ 'exit-token)
            (<- cmd-token-kind$ 'exit-token)


     || t -->

        ;-- build an atom containing this single special character
            (<- cmd-token$ (implode (list (car cmd-text$))))
            (<- cmd-text$ (cdr cmd-text$))
            (<- cmd-token-kind$ 'delimiter)
     fi)
)


;--
;-- expand-cmd-word$ ()
;--
;--   Given a prefix (abbreviation) of some command in 'cmd-token',
;--   check the list of valid unabbreviated commands for one that 
;--   'cmd-token' is a prefix of, and replace 'cmd-token' by the
;--   unabbreviated version of the command. 
;--   Returns...
;--     t   if abbreviated command is ambiguous
;--     nil if not ambiguous or no match in the list
;--

(defun expand-cmd-word$ ()

       (Ploop (local command      (istring cmd-token$)
                    command-list prl-command-list$
                    num-matches  0
             )
             (while command-list)
             (do
                 (Pif (is-prefix$ command (car command-list))  -->
                     (<- cmd-token$ (implode (car command-list)))
                     (<- num-matches (1+ num-matches))
                  fi)
                 (<- command-list (cdr command-list))
             )
             (result (Pif (< num-matches 2)  -->  nil
                      || t  -->  t
                      fi)
             )
       )
)

(defun is-prefix$ (list1 list2)

   ;-- Returns 't' if (equal list1 list2) or if list1 is an
   ;-- 'equal' prefix of list2.
      
      (Ploop (local is-prefix t)
            (while (and list1 is-prefix))
            (do
               (Pif (and list2 (equal (car list1) (car list2)))  -->
                   (<- list1 (cdr list1))
                   (<- list2 (cdr list2))
                || t  -->
                   (<- is-prefix nil)
                fi)
            )
            (result is-prefix)
      )
)


;--
;-- check-cmd$ ()
;--
;--   Check command syntax is
;--         check <object>
;--     or  check <object>-<object>
;--
;--   For each object name specified, check the object and update its
;--   status (and all those objects which reference it). Redisplay
;--   the library window if any of the objects being checked are 
;--   currently being displayed in the library window.
;--

(defun check-cmd$ ()
   (Plet (objname-list nil
         view-item    nil
         num-checked  0
        )
       (scan-cmd$)
       (<- objname-list (lib-member (must-be-last-parm$ (get-objects-cmd$))))
       (Pif objname-list  -->
           ;-- For each object in 'objname-list',
           ;-- Pif not being edited then check it.
           (unwind-protect
	       (let ((redisplay-on-status-change nil))
		 (declare (special redisplay-on-status-change))
		 (for (name in objname-list)
		      (do
			(<- view-item (assoc name view-stack))
			(cond ((and view-item
				    (eql (sel region
					     ((region-of-view view-item))
					     view-kind)
					'EDIT))
			       (display-message
				 (append
				   '#.(istring "Cannot check ")
				   (istring name)
				   '#.(istring " while it is being edited."))))
			      (t 
			       (<- num-checked (1+ num-checked))
			       (check-obj name))))))
	     (if (some #'(lambda (name)
			     (eql 'DEF (sel (object (library-object name))
					   kind))) 
		       objname-list)
		 ;; defs referencing checked defs become BAD.  Since we don't know
		 ;; what these defs are, we redisplay the whole lib window.
		 (lib-display)
		 (update-lib-display objname-list)))

           ;-- Indicate end of checking operation.
              (display-message (append (istring num-checked)
                                       '#.(istring " library object(s) checked.")
                               )
              )

           ;-- indicate success
              nil

        || t  -->
           (throw 'CMDERR '#.(istring "Object not in library or improper range."))
        fi)
   )
)

(defun check-obj (name)

    ;-- Depending on the type of the object named 'name', 
    ;-- call appropriate parsing routine.

        (Plet (curr-obj (library-object name)
              result   nil
              kind     nil
              obj-refd nil
             )
            (<- kind (sel (object curr-obj) kind))
            (Pif (member kind '(DEF ML EVAL)) -->
                ;-- For each object that curr-obj presently references,
                ;-- remove curr-obj from that object's referenced-by list
                ;-- and then set curr-obj's references list to nil.
                    (for (x in (sel (object curr-obj) references))
                         (do
                            (<- obj-refd (library-object x))
                            (<- (sel (object obj-refd) referenced-by)
                                (delete name *-*)
                            )
                         )
                    )
                    (<- (sel (object curr-obj) references) nil)

             fi)

            (<- result
	        (case kind
	            (DEF (parse-defn name))
		    (ML  (process-ml-object name))
		    (EVAL (process-eval-object name))
		    (THM (check-proof-of-object curr-obj name))
		)
	    )

	    (Pif (eql kind 'THM) -->  ;- extract the term, if possible
		(term-of-theorem name)
	     fi)

            (Pif (eql (car result) 'ERR)  -->
                (display-message (append '#.(istring "In ")
                                         (istring name)
                                         '#.(istring ": ")
                                         (istring (cadr result))
                                 )
                )
             || (eql (car result) 'REFERENCED)  -->
                (<- (sel (object curr-obj) references)
                    (cdr result)
                )
                ;-- For each object which 'curr-obj' references,
                ;-- make sure the name of 'curr-obj' is in the
                ;-- 'referenced-by' field of that object.
                    (for (x in (cdr result))
                         (do
                             (<- obj-refd (library-object x))
                             (Pif (null (member name (sel (object obj-refd)
                                                       referenced-by
                                                  )
                                       )
                                 )  -->
                                 (<- (sel (object obj-refd) referenced-by)
                                     (cons name *-*)
                                 )
                              fi)
                         )
                    )
             fi)
        )
)


;--
;-- lib-I/O-init$ ()
;--
;--   Initialize for 'load' and 'dump' commands.
;--

(global last-loaded-file$)   ;-- Complete file name used in last 'load' cmd.

(defun lib-I/O-init$ ()

   ;-- Initialize the filename for the most recent 'load' performed.
      (<- last-loaded-file$ nil)
)


;--
;-- dump-cmd$ ()
;--
;--   Dump command syntax is 
;--        dump <objects> ( to <filename> ]
;--   where
;--        the filename if omitted is taken to be the same as 
;--        the one used in the last load that was done 'last-loaded-file'.
;--        If file opened successfully, calls 'lib-dump' to get
;--        an S-expression representing the selected <objects> from
;--        the current library, and writes them out to the file using 'print'.
;-- 

(defun dump-cmd$ ()

   (Plet (dump-port    nil
         fname        nil
         ndumped      nil
         dump-objects nil
        )
       ;-- Get objects to be dumped.
          (scan-cmd$)
          (<- dump-objects (get-objects-cmd$))

       ;-- Get the name of file to be dumped into.
          (Pif (and (eql cmd-token-kind$ 'identifier) 
                   (eql cmd-token$ '|to|)
              )  -->
              (form-filename$)
           || (eql cmd-token-kind$ 'end-cmd)  -->
              (<- cmd-text$ nil)
           || t  -->
              (throw 'CMDERR '#.(istring "Missing 'to'."))
           fi)   

          (Pif (null cmd-text$)  -->
              ;-- Filename was omitted.
                 (Pif last-loaded-file$  -->
                     (<- fname last-loaded-file$)
                  || t  -->
                     (throw 'CMDERR '#.(istring "Filename must be specified."))
                  fi)
           || t  -->
              (<- fname (merge-pathnames (symbol-name (implode cmd-text$))
					 (concatenate 'string "foo."
						      *lisp-file-extension*)))
           fi)

       ;-- Open the file, return any problems via a 'throw'.
          (<- dump-port (prl-open$ fname 'OUT))
          (Pif (null dump-port)  -->
              (throw 'CMDERR (append '#.(istring "Could not open output file '")
                                      (istring (implode cmd-text$))
                                      '#.(istring "'.")
                              )
              )
           fi)

       (<- ndumped (lib-dump dump-objects dump-port))
       (close dump-port)
       (Pif (numberp ndumped)  -->
           ;-- Dump was successful, print s-expr to dump file.
              (display-message (append (istring ndumped)
                                       '#.(istring " library object(s) dumped to file '")
                                       (istring fname)
                                       '#.(istring "'.")
                               )
              )
           ;-- Result nil = success.
              nil
        || t  -->
           (throw 'CMDERR '#.(istring "No library objects dumped."))
        fi)
   )
)


;;; Convert an old (from versions of Nuprl older than 2.0) library dump
;;; to a form that is directly readable.  This function can only be
;;; applied once to any file.
(defun fix-old-library (input-file output-file)
  (with-open-file (in input-file)
    (with-open-file (out output-file
			 :direction :output
			 :if-exists :new-version)
      (do ((ch (read-char in nil nil)
	       (read-char in nil nil)))
	  ((null ch) (values))
	(when (lower-case-p ch)
	  (write-char #\\ out))
	(write-char ch out)))))
	    

;--
;-- load-cmd$ ()
;--
;--   Load command syntax is 
;--        load <place> from <filename>
;--   where
;--        If the file is opened successfully, one S-expression
;--        (in the format described in 'lib-dump')
;--        is read from the file using 'read' and 'lib-load' is
;--        called to add the contents to the library at location <place>.
;--        If lib-load returns nil, then load was successful,
;--        else it returns an error message describing the problem.
;--
;--        The name of the file just loaded is displayed in
;--        the header of the library window and in variable
;--        'last-loaded-file'.
;--

(defun load-cmd$ ()

   (Plet (load-port       nil
         fname           nil
         short-fname     nil
         lib-sexpr       nil
         load-place      nil
         lib-load-result nil
	 full-load       nil
        )

       ;-- Get place where objects should be loaded.
          (scan-cmd$)

	  (Pif (and (eql cmd-token-kind$ 'identifier)
		   (eql cmd-token$ '|fully|)
	      ) -->
	      (<- full-load t)
	      (scan-cmd$)
	   fi)

          (<- load-place (get-place-cmd$))

       ;-- Get the name of file to be loaded from.
          (Pif (and (eql cmd-token-kind$ 'identifier)
                   (eql cmd-token$ '|from|)
              )  -->
              (form-filename$)
           || t  -->
              (throw 'CMDERR '#.(istring "Missing 'from'."))
           fi)
          (Pif (null cmd-text$)  -->
              (throw 'CMDERR '#.(istring "Filename must be specified."))
           fi)
	  (<- short-fname (implode cmd-text$))
     (<- fname (merge-pathnames
                (symbol-name short-fname) (concatenate 'string "foo."
							      *lisp-file-extension*)))

       (<- load-port (prl-open$ fname 'IN))
       (Pif (null load-port)  -->
           (throw 'CMDERR (append '#.(istring "Could not find/open input file '")
                                   (istring short-fname)
                                   '#.(istring "'.")
                           )
           )
        fi)

       ;-- make Lisp machine avoid conversion to upper case
       (with-reader-character-conversion-disabled
	 (<- lib-sexpr (catch-error (read load-port))))

       (Pif lib-sexpr  -->
           (<- lib-sexpr (car lib-sexpr))
        fi)
       (close load-port)

       (Pif (and lib-sexpr
                (eql (car lib-sexpr) 'PRL-LIB-DUMP)
           )  -->
           (<- lib-load-result (lib-load lib-sexpr load-place full-load))
        || t  -->
           (throw 'CMDERR '#.(istring "Load file not in proper format."))
        fi)

       ;-- Set header of library window to indicate filename just read.
       ;-- (Also in last-loaded-file).
          (selectw lib-window)
          (setheaderw 9 (append '#.(istring "(")
   			        '#.(istring "File: ")
                                 (istring short-fname)
                                 '#.(istring ")")
                         )
		      t
          )
          (selectw cmd-window$)
          (<- last-loaded-file$ short-fname)

       (display-message (append (istring (car lib-load-result))
                                '#.(istring " library object(s) loaded from file '")
                                (istring short-fname)
                                '#.(istring "'.")
                        )
       )

       ;-- Check if any duplicates were encountered in the loading
       ;-- process and display how many there were.
          (Pif (cadr lib-load-result)  -->
              ;-- There were duplicates -- indicate how many.
                 (display-message (append (istring
                                             (length (cadr lib-load-result))
                                          )
                                          '#.(istring " duplicate(s) not loaded.")
                                  )
                 )
           fi)

       ;-- Success -- result is nil.
          nil
   )
)



;;; ******************************************************************************************
;;; Following is the implementation of commands which allow interleavings of different users
;;; within a single Nuprl session.  This is accomplished by providing for the fast storing and
;;; retrieving of named complete Nuprl states.  The state includes the ML environment, the eval
;;; environment, and the library.  There is a special state called "initial" which has an empty
;;; library, an empty eval environment, and an ML environment consisting of the ML objects which
;;; are loaded with Nuprl.  States do not survive rebooting.


(defun object-of-library-member (x)
    (library-object x))

(defparameter *ML-object-property-names*
	  '(REFVAR MLVAL MLTYPE NUMARGS ARITY ABSNAME MLDESCRIPTOR))

(defvar *properties-of-primitive-ML-objects* ())

(defun get-ML-object-properties (name)
  (mapcar #'(lambda (prop) (get name prop))
	  *ML-object-property-names*))

(defun put-ML-object-properties (name properties)
    (mapc #'(lambda (prop prop-value)
	      (cond ((not (null prop-value))
		     (setf (get name prop) prop-value))))
	  *ML-object-property-names*
	  properties)
    nil)

(defun get-prop-from-alist (name prop-name alist)
    (let* ((props (cdr (assoc name alist))))
      (nth (position prop-name *ML-object-property-names*)
	   props)))

(defvar *primitive-ML-objects-noted?* nil)

(defun note-primitive-ML-objects ()
  (unless *primitive-ML-objects-noted?*
    (setq *properties-of-primitive-ML-objects* ())
    (do-symbols (x (find-package 'nuprl))
      (if (get x 'MLDESCRIPTOR) (push (cons x (get-ml-object-properties x))
				      *properties-of-primitive-ML-objects*)))
    (setq *primitive-ML-objects-noted?* t)))


;;; Returns an alist associating the symbols in the current values of
;;; *properties-of-primitive-ML-objects* and global%env, in order, with their
;;; current ML properties.
(defun get-ML-properties ()
    (declare (special global%env))
    (append
      *properties-of-primitive-ML-objects*
      (mapcar #'(lambda (pair) (cons (car pair)
				     (get-ML-object-properties (car pair))))
	      global%env)))

;;; Remove all current ML properties.
(defun remove-ML-properties ()
  (declare (special global%env))
  (flet ((f (pair) (mapc #'(lambda (prop) (remprop (car pair) prop))
			 *ML-object-property-names*)))
    (mapc #'f *properties-of-primitive-ML-objects*)
    (mapc #'f global%env)))

;;; Restore properties of ML objects using and alist.
(defun put-ML-properties (alist)
  (mapc #'(lambda (pair)
	    (put-ML-object-properties (car pair) (cdr pair)))
	alist))

(defun clear-ML-state (&optional (primitives-too-p nil))
  (declare (special global%env %deftypes))
  (remove-ML-properties)
  (setq global%env nil
	%deftypes nil)
  (unless primitives-too-p
    (put-ML-properties *properties-of-primitive-ML-objects*))
  t)



;;; *saved-states* is an alist of all the currently saved states.  Each
;;; state is a list (library library-objects ML-type-env ML-value-env
;;; ML-object-properties eval-env) where ML-object-properties is an a-list
;;; associating names with lists of ML properties (in a certain order).
(defvar *saved-states* '((|initial| () () () () () ())))


;;; Establish a special initial state.  This state is empty exept for the ML environment which
;;; will be the environment that is current when the function is called.  This state cannot be
;;; deleted or overwritten.  
(defun establish-initial-state ()
  (declare (special %deftypes global%env))
    (setf (cdr (assoc '|initial| *saved-states*))
	  (list ()
		()
		%deftypes
		global%env
		(get-ML-properties)
		()))
    nil)



;;; This function assumes that mutations happen only in library objects.
(defun copy-state (state-name)
  (multiple-value-bind
	(library objects ML-type-env ML-value-env ML-props eval)
      (values-list (cdr (assoc state-name *saved-states*)))
    (list library (mapcar #'copy-object objects)
	  ML-type-env (copy-tree ML-value-env) ML-props eval)))

;;; Assumes that the named state exists. 
(defun restore-state (name)
  (declare (special %deftypes global%env eval-env library$))
  (remove-ML-properties)
  (mapc #'(lambda (x) (unbind-library-object x)) library$)
  (multiple-value-bind
	(library objects ML-type-env ML-value-env ML-props eval)
      (values-list (copy-state name))
    (<- library$ library)
    (mapc #'(lambda (x y) (bind-library-object x y))
	  library$
	  objects)
    (<- %deftypes ML-type-env)
    (<- global%env (copy-tree ML-value-env))
    (put-ML-properties ML-props)
    (<- eval-env eval)))

;;; Assumes that the current window is the command window.
(defun restore-state-and-update-windows (name)
  (declare (special library$ lib-window-top$))
  (restore-state name)
  (<- lib-window-top$ (car library$))
  (selectw lib-window)
  (setheaderw 9 (append '#.(istring "(")
			'#.(istring "State: ")
			(istring name)
			'#.(istring ")"))
	      t)
  (selectw cmd-window$)
  (lib-display))


;;; "P> save foo"  causes the saving of the current state under the
;;;  name "foo", and re-establishes the initial state.
(defun save-cmd$ ()
  (declare (special library$ %deftypes global%env eval-env))
  (unless (zerop num-regions)
    (throw 'CMDERR (istring "All windows must be closed.")))

  (scan-cmd$)
  (cond
    ((not (eql cmd-token-kind$ 'identifier))
     (throw 'CMDERR '#.(istring "Must supply name for state.")))
    ((eql '|initial| cmd-token$)
     (throw 'CMDERR '#.(istring "The initial state cannot be overwritten.")))
    ((not (equal (car cmd-text$) '(NL)))
     (throw 'CMDERR
       (istring (format nil "extraneous characters after state name ~a." cmd-token$ )))))

  (<- *saved-states*
      (remove-if #'(lambda (x) (eql (car x) cmd-token$)) *-*))
  (push (list cmd-token$ 
	      library$
	      (mapcar #'object-of-library-member library$)
	      %deftypes
	      global%env
	      (get-ML-properties)
	      eval-env)
	*saved-states*)
  (restore-state-and-update-windows '|initial|))





;;; "P> restore foo" returns Nuprl to the state it was in when "foo" was
;;; saved.  The current state is lost.  "foo" is removed from the list of
;;; saved states.
(defun restore-cmd$ ()
  (declare (special library$))
  (unless (zerop num-regions)
    (throw 'CMDERR (istring "All windows must be closed.")))
  (scan-cmd$)
  (cond ((not (eql cmd-token-kind$ 'identifier))
	 (throw 'CMDERR '#.(istring "Must supply name for state to restore.")))
	((and (not (eql cmd-token$ '|initial|))
	      (not (assoc cmd-token$ *saved-states*)))
	 (throw 'CMDERR '#.(istring "No such state."))))
  (mapc #'(lambda (x) (unbind-library-object x)) library$)
  (remove-ML-properties)
  (restore-state-and-update-windows cmd-token$)
  nil)


;;; "P> copystate foo fooprime".  
(defun copystate-cmd$ ()
    (let* ((source-name
	     (progn (scan-cmd$)
		    (cond ((not (eql cmd-token-kind$ 'identifier))
			   (throw 'CMDERR '#.(istring "Must supply name for state to copy.")))
			  ((not (assoc cmd-token$ *saved-states*))
			   (throw 'CMDERR '#.(istring "State to copy does not exist."))))
		    cmd-token$))
	   (target-name
	     (progn (scan-cmd$)
		    (cond ((not (eql cmd-token-kind$ 'identifier))
			   (throw 'CMDERR '#.(istring "Must supply name for copy of state.")))
			  ((assoc cmd-token$ *saved-states*)
			   (throw 'CMDERR '#.(istring "Name for copy must be new."))))
		    cmd-token$)))
      (push (cons target-name (copy-state source-name)) *saved-states*))
    nil)
    

;;; "P> states"  lists the currently saved states.
(defun states-cmd$ ()
    (display-message
      (apply #'nconc
	     (mapcar #'(lambda (x) (cons (ichar #\space) (istring (car x))))
		     *saved-states*)))
    nil)

;;; "P> kill foo"  removes the state "foo" from the list of saved states.
(defun kill-cmd$ ()
    (scan-cmd$)
    (cond ((not (eql cmd-token-kind$ 'identifier))
	   (throw 'CMDERR '#.(istring "Must supply name of state to kill.")))
	  ((not (assoc cmd-token$ *saved-states*))
	   (throw 'CMDERR '#.(istring "Named state does not exist.")))
	  ((eql '|initial| cmd-token$)
	   (throw 'CMDERR '#.(istring "Cannot kill the initial state."))))
    (<- *saved-states* (remove-if #'(lambda (x) (eql cmd-token$ (car x))) *-*))
    nil)

(defun kill-state-saves ()
    (<- *saved-states* nil))

(defun restore-library-from-state (state-name)
  (declare (special library$ lib-window-top$))
  (mapc #'(lambda (x) (unbind-library-object x)) library$)
  (let ((state (copy-state state-name)))
    (<- library$ (first state))
    (mapc #'(lambda (x y) (bind-library-object x y))
	  library$
	  (second state))
    (<- lib-window-top$ (car library$))
    (lib-display)))


;;; End of "states" section.
;;; ***************************************************************************

(defun form-filename$ ()

   ;-- Skip over any blanks before filename,
   ;-- remove (NL) from end of cmd-text and return in 'cmd-text'.
      (Ploop (while (equal (car cmd-text$) #.(ichar #\space)))
            (do (<- cmd-text$ (cdr cmd-text$)))
      )
      (<- cmd-text$ (nreverse (cdr (reverse cmd-text$))))
)


(defun prl-open$ (fname in-or-out)

   ;-- Returns the port corresponding to file 'fname',
   ;-- or nil if problem opening the file.
      (Pif (eql in-or-out 'IN)  -->
          (open fname :direction :input :if-does-not-exist nil)
       || t  -->
          (open fname :direction :output :if-does-not-exist :create)
       fi)
)


;--
;-- create-cmd$ ()
;--
;--   Create command syntax is
;--          create name kind <place>
;--   where 
;--        <place> is 'top', 'bot', 'after' <object>, 'before' <object>
;--

(defun create-cmd$ ()

       (Plet (name nil
             kind nil
            )
           (scan-cmd$)
           (<- name (get-id-cmd$ '#.(istring "object name")))
           (<- kind (get-id-cmd$ '#.(istring "object kind")))
           (Pif (not (member kind '(|thm| |def| |ml| |eval|)))  -->
               (throw 'CMDERR '#.(istring "Object kind not 'thm  def eval or ml'."))
            || t  -->
               (throw 'CMDERR 
                       (lib-create name 
                                   (Pif (eql kind '|thm|)  -->  'THM
                                    || (eql kind '|def|)  -->  'DEF
                                    || (eql kind '|ml|)   -->  'ML
				    || (eql kind '|eval|) -->  'EVAL
                                    fi)
                                   (must-be-last-parm$ (get-place-cmd$))
                       )
               )
            fi)
       )
)


;--
;-- delete-cmd$ ()
;--
;--   Delete command syntax is
;--          delete <objects>
;--   where <objects> is <object>[-<object>]
;--                           

(defun delete-cmd$ ()

       (scan-cmd$)
       (throw 'CMDERR
               (lib-delete (must-be-last-parm$ (get-objects-cmd$)))
       )
)

;
;;--
;;-- eval-cmd$ ()
;;--
;;--   Eval command syntax is
;;--     eval
;;--   Create a ted window, allow user to enter term to be evaluated,
;;--   then upon EXIT key, parse the term, evaluate it, and display
;;--   the resulting term in the window.  Keep doing this until an
;;--   EXIT is done without the window contents first being modified,
;;--   then kill the window.
;;--
;  
;(defun eval-cmd$ ()
;
;    (Plet (view-descr nil        ;-- structure returned from createview
;          bot        0          ;-- bottom line within new view (0..bot)
;          right      0          ;-- rightmost position in new view (0..right)
;         )
;
;         ;-- grab a free region, insert it into used-regions list just
;         ;-- after cur-region, and make the new region current
;             (Pif (null free-regions) -->
;                 (*throw 'CMDERR '#.(istring "Too many active views.  Please kill some."))
;              fi)
;
;             (<- num-regions (add1 *-*))
;             (<- cur-region (car free-regions))
;             (<- free-regions (cdr free-regions))
;
;             (Pif (onep num-regions) -->
;                 (<- used-regions (list cur-region))
;                 (<- cur-region-index 0)
;
;              || t -->
;                 (<- (cdr (nthcdr cur-region-index used-regions))
;                     (cons cur-region *-*)
;                 )
;                 (<- cur-region-index (add1 *-*))
;
;              fi)
;
;         ;-- create new view of proper size, position,and header
;             (<- view-descr (createview nil cur-region 'small))
;             (<- cur-window$ (car view-descr))
;             (<- bot (cadr view-descr))
;             (<- right (caddr view-descr))
;
;             (selectw cur-window$)
;             (setheaderw nil '#.(istring "EVAL"))
;   
;         ;-- fill in the fields of this new region
;             (<- (sel region (cur-region) obj-name)       nil)
;             (<- (sel region (cur-region) obj-kind)       'EVAL)
;             (<- (sel region (cur-region) view-kind)      'EDIT)
;             (<- (sel region (cur-region) window)         cur-window$)
;             (<- (sel region (cur-region) top)            0)
;             (<- (sel region (cur-region) left)           0)
;             (<- (sel region (cur-region) bot)            bot)
;             (<- (sel region (cur-region) right)          right)
;             (<- (sel region (cur-region) allowed-events) '(KILL SIZE))
;             (<- (sel region (cur-region) assoc-region)   nil)
;             (<- (sel region (cur-region) modified)       nil)
;
;         ;-- create new ted descriptor for this region
;
;             (new-ted-region
;                     cur-region
;                     (copy raw-object-Ttree)
;             )
;
;         ;-- indicate success
;             nil
;
;    )
;)


;-- 
;-- jump-cmd$ ()
;--
;--   Jump command syntax is
;--        jump <object>
;--   where <object> is 'first', 'last', or an objectname
;--

(defun jump-cmd$ ()

       (scan-cmd$)
       (throw 'CMDERR
               (lib-jump (must-be-last-parm$ (get-object-cmd$)))
       )
)


;-- 
;-- move-cmd$ ()
;--
;--   Move command syntax is
;--        move <objects> <place>
;--

(defun move-cmd$ ()

       (Plet (objects nil)
           (scan-cmd$)
           (<- objects (get-objects-cmd$))
           (throw 'CMDERR
                   (lib-move objects (must-be-last-parm$ (get-place-cmd$)))
           )
       )
)




;--
;-- scroll-cmd$ ()
;--
;--   Scroll command syntax is
;--          scroll [[up] number]
;--

(defun scroll-cmd$ ()

       (Plet (direction 1
             amt       1
            )
           (scan-cmd$)
           (Pif (and (eql cmd-token-kind$ 'identifier)
                    (eql cmd-token$ '|up|)
               )  -->
               ;-- Scroll up by setting direction minus.
                  (scan-cmd$)
                  (<- direction -1)
            fi)

           (Pif (eql cmd-token-kind$ 'end-cmd)  -->
               ;-- Scroll up or down by 1.
                  (throw 'CMDERR (lib-scroll (* direction amt)))
            || (eql cmd-token-kind$ 'number)  -->
               (<- amt cmd-token$)
               (scan-cmd$)
               (throw 'CMDERR
                       (lib-scroll (must-be-last-parm$ (* direction amt)))
               )
            || t  -->
               (throw 'CMDERR '#.(istring "Characters after command end."))
            fi)
       )
)


;--
;-- down-cmd$ ()
;--
;--   Down command syntax is
;--          down [number]
;--   This moves down 1 or specified number of library pages
;--

(defun down-cmd$ ()

       (Plet (amt       1
            )
           (scan-cmd$)
           (Pif (eql cmd-token-kind$ 'end-cmd)  -->
               ;-- page down by 1.
                  (throw 'CMDERR (lib-page amt))
            || (eql cmd-token-kind$ 'number)  -->
               (<- amt cmd-token$)
               (scan-cmd$)
               (throw 'CMDERR
                       (lib-page (must-be-last-parm$ amt))
               )
            || t  -->
               (throw 'CMDERR '#.(istring "Characters after command end."))
            fi)
       )
)


;--
;-- up-cmd$ ()
;--
;--   Up command syntax is
;--          up [number]
;--   This moves up 1 or specified number of library pages
;--

(defun up-cmd$ ()

       (Plet (amt       1
            )
           (scan-cmd$)
           (Pif (eql cmd-token-kind$ 'end-cmd)  -->
               ;-- page up by 1.
                  (throw 'CMDERR (lib-page (- amt)))
            || (eql cmd-token-kind$ 'number)  -->
               (<- amt cmd-token$)
               (scan-cmd$)
               (throw 'CMDERR
                       (lib-page (must-be-last-parm$ (- amt)))
               )
            || t  -->
               (throw 'CMDERR '#.(istring "Characters after command end."))
            fi)
       )
)


;--
;-- bottom-cmd$ ()
;--
;--   Bottom command syntax is
;--          bottom
;--   This moves to bottom of library.
;--

(defun bottom-cmd$ ()

    (scan-cmd$)
    (throw 'CMDERR (lib-page (must-be-last-parm$ 'bottom)))

)


;--
;-- top-cmd$ ()
;--
;--   Top command syntax is
;--          top
;--   This moves to top of library.
;--

(defun top-cmd$ ()

    (scan-cmd$)
    (throw 'CMDERR (lib-page (must-be-last-parm$ 'top)))

)



(defun get-id-cmd$ (kind-of-id)

   ;-- Checks that 'cmd-token' is an identifier, and if so, returns it.
   ;-- Else does a throw with an error message indicating that
   ;-- 'kind-of-id' was expected when 'cmd-token-kind' was found.

      (Plet (id cmd-token$)
          (Pif (not (eql cmd-token-kind$ 'identifier))  -->
              (throw 'CMDERR
                      (append '#.(istring "Expecting: ") kind-of-id 
                              '#.(istring ". Found: ") (istring cmd-token-kind$)
                      )
              )
           fi)
          (scan-cmd$)
          ;-- Result is 'cmd-token' upon entry.
             id
       )
)

(defun get-object-cmd$ ()

   ;-- Returns one of the following atoms
   ;--       FIRST
   ;--       LAST
   ;--       object-name

      (Plet (obj (get-id-cmd$ '#.(istring "object-name")))
          (Pif (eql obj '|first|)  -->
              'FIRST
           || (eql obj '|last|)  -->
              'LAST
           || t  -->
	      (complete-object-name obj)
           fi)
      )
) 

;;; symbol -> symbol.  Return the name in the library which
;;; most "closely matches" the given name (returning the given
;;; name if no library member comes "close").  If the optional
;;; argument, a predicate, is supplied then only object names
;;; satisfying it will be examined.
(defun complete-object-name (x &optional filter)
  (declare (special library$))
  (let* ((y (symbol-name x)))
    (or (and (lib-member x) x)
	(car (member-if
	       #'(lambda (z)
		   (and (or (null filter) (funcall filter z))
			(= 0 (or (search y (symbol-name z))
				 1))))
	       library$))
	x)))


(defun get-objects-cmd$ ()

   ;-- Returns a list of two objectnames.

      (Plet (obj1 nil
            obj2 nil
           )
          (<- obj1 (get-object-cmd$))
          ;-- Assume a '-' does not follow the object name.
             (<- obj2 obj1)
          (Pif (and (eql cmd-token-kind$ 'delimiter)
                   (eql cmd-token$ '|-|)
              )  -->
              ;-- Call scan to skip over the '-'.
                 (scan-cmd$)
              (<- obj2 (get-object-cmd$))
           fi)
          (list obj1 obj2)
      )
)

(defun get-place-cmd$ ()

   ;-- Returns one of the following four forms
   ;--      (AFTER <object>)
   ;--      (BEFORE <object>)
   ;--      (TOP)
   ;--      (BOTTOM)

      (Plet (pos nil)
          (<- pos (get-id-cmd$ '#.(istring "before, after, top, bot")))

          (Pif (eql pos '|before|)  -->
              (list 'BEFORE (get-object-cmd$))

           || (eql pos '|after|)  -->
              (list 'AFTER (get-object-cmd$))

           || (eql pos '|top|)  -->
              (list 'TOP)

           || (eql pos '|bot|)  -->
              (list 'BOTTOM)

           || t  -->
              (throw 'CMDERR '#.(istring "Place must be 'before,after,top,bot'."))
           fi)
      )
)

(defun must-be-last-parm$ (val)

   ;-- if 'cmd-token-kind' is end-cmd, then returns val
   ;-- else throws an error message.

      (Pif (not (eql cmd-token-kind$ 'end-cmd))  -->
          (throw 'CMDERR '#.(istring "Characters after end of command."))
       fi)
      val
)


;--
;-- view-cmd$ ()
;--
;--   command syntax is
;--        view <object>
;--      
;--   process the view command, throwing a CMDERR and error
;--   message if any problems arise and returning nil otherwise
;--

(defun view-cmd$ ()
     (Plet (name       nil        ;-- name of object being viewed
          obj-name   nil        ;-- name prefixed by OBJ- 
          obj        nil        ;-- object to be viewed
          view-kind  'EDIT      ;-- EDIT or SHOW
          view-descr nil        ;-- structure returned from createview
          bot        0          ;-- bottom line within new view (0..bot)
          right      0          ;-- rightmost position in new view (0..right)
         )

         (scan-cmd$)

    
         ;-- get name and verify that it appears in library
             (<- name (lib-member (must-be-last-parm$ (get-object-cmd$))))

             (Pif (null name) -->
                 (throw 'CMDERR '#.(istring "Object not found in library."))
              fi)
    
	 (<- obj-name name)
    
            
         (<- obj (library-object obj-name))

         ;-- grab a free region, insert it into used-regions list just
         ;-- after cur-region, and make the new region current
             (Pif (null free-regions) -->
                 (throw 'CMDERR '#.(istring "Too many active views.  Please kill some."))
              fi)

             (<- num-regions (1+ *-*))
             (<- cur-region (car free-regions))
             (<- free-regions (cdr free-regions))

             (Pif (onep num-regions) -->
                 (<- used-regions (list cur-region))
                 (<- cur-region-index 0)

              || t -->
                 (<- (cdr (nthcdr cur-region-index used-regions))
                     (cons cur-region *-*)
                 )
                 (<- cur-region-index (1+ *-*))

              fi)

         ;-- if the object is being viewed already, make sure
         ;-- that view is SHOW mode and make this view SHOW also
	     (for (view in view-stack)
		  (do
		      (Pif (and
			      (Pif (eql (name-of-view view) obj-name) -->
				  (<- view-kind 'SHOW)
			       || t -->
				  nil
			       fi)
			      (eq
				  (sel
				      region ((region-of-view view))
				      view-kind
				  )
				  'EDIT
			      )
			  ) -->

			  (<- (sel
				    region ((region-of-view view))
				    view-kind
			      )
			      'SHOW
			  )
			  (selectw
			      (sel
				  region ((region-of-view view))
				  window
			      )
			  )
			  (setheaderw 0 '#.(istring "SHOW"))
		       fi)
		  )
	     )

         ;-- create new view of proper size, position,and header
	     (Pif (eql 'THM (sel (object obj) kind)) -->
		 (<- view-descr (createview obj-name cur-region 'large))

	      || t -->
		 (<- view-descr (createview obj-name cur-region 'small))

	      fi)
             (<- cur-window$ (car view-descr))
             (<- bot (cadr view-descr))
             (<- right (caddr view-descr))
	   

             (selectw cur-window$)
             (setheaderw nil (append
                                 (Pif (eql view-kind 'SHOW) --> '#.(istring "SHOW ")
                                    || t                   --> '#.(istring "EDIT ")
                                  fi)
                                 (istring (sel (object obj) kind))
                                 '#.(istring " ")
                                 (istring name)
                             )
             )
   
         ;-- fill in the fields of this new region
             (<- (sel region (cur-region) obj-name)       name)
             (<- (sel region (cur-region) view-kind)      view-kind)
             (<- (sel region (cur-region) window)         cur-window$)
             (<- (sel region (cur-region) top)            0)
             (<- (sel region (cur-region) left)           0)
             (<- (sel region (cur-region) bot)            bot)
             (<- (sel region (cur-region) right)          right)
             (<- (sel region (cur-region) allowed-events) '(KILL SIZE))
             (<- (sel region (cur-region) assoc-region)   nil)
             (<- (sel region (cur-region) modified)       nil)

         (Pif (eql 'THM (sel (object obj) kind)) -->

             (<- (sel region (cur-region) obj-kind) 'PROOF)

	     (unwind-protect
		 (progn
		   (check-proof-of-object obj name)
		   (new-red-region cur-region
				   (sel (object obj) value)))
	       (unless (eql (sel (theorem-object (sel (object obj) value))
				   proof-rep-type)
			   'PROOF-TREE)
		 (remove-active-region)
		 (<- cur-window$ cmd-window$)
		 (selectw cur-window$)))	     


          || t --> 
             
             (<- (sel region (cur-region) obj-kind) 'TTREE)

             ;-- create new ted descriptor for this region

                 (Pif (eql (sel (object obj) kind) 'DEF) -->
                     (new-ted-region
                         cur-region
                         (sel (definition-object
                                  (sel (object obj) value)
                              ) 
                              body
                         )
                     )

		  || (eql (sel (object obj) kind) 'EVAL) -->
		     (new-ted-region
		         cur-region
			 (sel (eval-object
                                  (sel (object obj) value)
                              )
                              body
                         )
		     )

                  || t -->
                     (new-ted-region
                         cur-region
                         (sel (ml-object
                                  (sel (object obj) value)
                              )
                              body
                         )
                     )

                  fi)

          fi)
    )
    nil     ;-- value if no CMDERR is thrown
)


;--
;-- createview (name:atom ,region:region#, size:atom)
;--
;--     Create a new window to hold a view at the most appropriate
;--     place on the screen.  The goal is to try to avoid obscuring
;--     any previously created windows.  Add this view to the view-stack
;--     with the specified name and region.  size is small or large --
;--     try to choose a view slot of the specified size.
;--

(defun createview (name region size)

    (Plet (top             0             ;-- coordinates on screen of
          bot             0             ;--   new view corners
          left            0
          right           0
          view-slot       (createview-no-window name region size)
	 )
     
	 (Pif (zerop view-slot) --> ;top 2/3 of right screen half
		 (<- top 3)
		 (<- bot (1- (TRUNCATE (* SCRHEIGHT 2) 3)))
		 (<- left (1+ (TRUNCATE SCRWIDTH 2)))
		 (<- right (- SCRWIDTH 2))
	 
	  || (equal view-slot 1) --> ; top 1/3 of left screen half
		 (<- top 3)
		 (<- bot (1- (TRUNCATE SCRHEIGHT 3)))
		 (<- left 1)
		 (<- right (1- (TRUNCATE SCRWIDTH 2)))
     
	  || (equal view-slot 2) --> ; bottom third of right screen half
		 (<- top (+ (truncate (* 2 SCRHEIGHT) 3) 3))
		 (<- bot (- SCRHEIGHT 2))
		 (<- left (1+ (TRUNCATE SCRWIDTH 2)))
		 (<- right (- SCRWIDTH 2))
     
	  || (equal view-slot 3) --> ; middle third of left screen half
		 (<- top (+ (TRUNCATE SCRHEIGHT 3) 3))
		 (<- bot (1- (TRUNCATE (* SCRHEIGHT 2) 3)))
		 (<- left 1)
		 (<- right (1- (TRUNCATE SCRWIDTH 2)))
     
	  || (equal view-slot 4) --> ; middle third of right screen half
		 (<- top (+ (TRUNCATE SCRHEIGHT 3) 3))
		 (<- bot (1- (TRUNCATE (* SCRHEIGHT 2) 3)))
		 (<- left (1+ (TRUNCATE SCRWIDTH 2)))
		 (<- right (- SCRWIDTH 2))
     
	  fi)

	(let ((w (createw top bot left right :allow-shift t)))
	  (list w
		(1- (window-height w))
		(1- (window-width w))))
    )    
)


(defun createview-no-window (name region size)

    (Plet (available-slots nil           ;-- available-slots is the set of
          active-views    view-stack    ;-- slots not present in the set
                                        ;--    {view-stack} - {active-views}
          view-slot       0             ;-- slot number chosen for view
         )

	(Pif (eql size 'large) -->
	    (<- available-slots (copy '(0 1 2 3 4)))

	 || t -->
	    (<- available-slots (copy '(1 0 2 3 4)))
	 fi)

        (Ploop
            (while (and (> (length available-slots) 1)
                        (not (null active-views))
                   )
            )
            (do
                (<- available-slots (delete (slot-of-view (car active-views))
                                            available-slots
                                    )
                )
                (<- active-views (cdr *-*))
            )
        )

        (<- view-slot (car available-slots))

        (<- view-stack (cons (view name region view-slot) *-*))

	view-slot
    )
)


;--
;-- destroyview (view:view)
;--
;--     Remove the specified view from the view stack.
;--

(defun destroyview (view)

    (<- view-stack (delete view view-stack))

)



;--
;-- set-object-status (name status)
;--
;-- Sets the status field for the object named 'name',
;-- and if status not COMPLETE, propagate BAD status to all
;-- objects which reference it.  Redisplays library window
;-- if any visible objects have their status changed and
;-- redisplay-on-status-change is not NIL.
;-- 

(global redisplay-on-status-change)
(eval-when (load eval)
    (<- redisplay-on-status-change t)
)

(defun set-object-status (name status) 

   (Plet (curr-obj (library-object name))
                   
       (Pif (not (eql status (sel (object curr-obj) status))) -->

           ;-- Set status for current object.
               (<- (sel (object curr-obj) status) status)

           ;-- Redisplay library window if it's being shown and redisplay is enabled.
               (Pif redisplay-on-status-change -->
		   (update-lib-display (list name))
		fi)

           (Pif (not (eql status 'COMPLETE))  -->
               ;-- Must propagate BAD object status to all other objects
               ;-- which reference OBJ-name.
                  (<- (sel (object curr-obj) references) nil)
                  (for (x in (sel (object curr-obj) referenced-by))
		       (do (if (is-lib-member x)
			       (propagate-bad-status$ x)))
                  )
                  (<- (sel (object curr-obj) referenced-by) nil)
            fi)

        fi)
   )
)

(defun propagate-bad-status$ (name)

   ;-- Set status of object OBJ-name to BAD and propagate BAD
   ;-- status to all the objects which reference it.  If object
   ;-- 'name' is in lib window, then update the lib display.
   ;-- If object already has BAD status, don't do anything.
      (Plet (curr-obj (library-object name))
          (Pif (not (eql 'BAD (sel (object curr-obj) status))) -->
              (<- (sel (object curr-obj) status) 'BAD)
              (Pif redisplay-on-status-change -->
                  (update-lib-display (list name))
               fi)
              (<- (sel (object curr-obj) references) nil)
              (for (x in (sel (object curr-obj) referenced-by))
                  (do (if (is-lib-member x) (propagate-bad-status$ x)))
              )
              (<- (sel (object curr-obj) referenced-by) nil)
           fi)
      )
)


;--
;-- menu-kill-event (window-to-kill:window#, window-with-cursor:window#)
;--
;--   This is called when the user invokes the Kill function on the mouse
;--   menu.  It destroys the window-to-kill, if that is possible.
;--   window-with-cursor is the number of the window on which
;--   selectw was performed most recently.
;--

(fluid window-to-kill)

(defun menu-kill-event (window-to-kill window-with-cursor)

    (Pif (window-equal window-to-kill lib-window) -->
        (display-message '#.(istring "Cannot kill library window."))

     || (window-equal window-to-kill cmd-window$) -->
        (display-message '#.(istring "Cannot kill cmd/status window."))
    
     || t -->
        (Plet (view (car (Psome #'(lambda (v)
                                   (window-equal (sel region
                                                   ((region-of-view v))
                                                   window
                                                 )
						 window-to-kill
                                   )
                               )
                              view-stack
                        )
                   )
             )
             (Pif (member 'KILL
                         (sel region ((region-of-view view)) allowed-events)
                 ) -->
                 ;-- The view associated with window-to-kill has been
                 ;-- found and KILL is an event allowed on it.  Invoke
                 ;-- the proper routine to re-organize the region info.
                     (Pif (member (sel region ((region-of-view view)) obj-kind)
                               '(TTREE EVAL)
                         ) -->
                         (ted-kill-view view)
      
                      || t -->
                         (red-kill-view view)
                
                      fi)
     
                 ;-- destroy the view, select the proper window,
                 ;-- and destroy the window

                     (remove-view view)
                  
                     (Pif (zerop num-regions) -->
                         (<- cur-window$ cmd-window$)
     
                      || t -->
                         (<- cur-window$
                             (sel region (cur-region) window)
                         )
     
                      fi)
     
                     (Pif (window-equal window-to-kill window-with-cursor) -->
                         ;-- the window containing the screen cursor is
                         ;-- being killed, select a new cur-window.
                              (selectw cur-window$)
                      fi)
     

              || t -->
                 (display-message '#.(istring "Cannot kill this window now."))

              fi)
        )

     fi)
)


;--
;-- menu-size-event (window-to-size:window#, window-with-cursor:window#,
;--                  top:row, left:col, bot:row, right:col)
;--
;--   This is called when the user invokes the Size function on the mouse
;--   menu.  It changes the size of the window-to-size to match the specified
;--   screen coordinates, if that is possible.  If the SIZEed window is an
;--   object view, it invokes the appropriate routine in the view's manager.
;--   After a size change, it redraws the current contents of the window,
;--   if it knows how.  window-with-cursor is the number of the window on
;--   which selectw was most recently performed (it is not used here).
;--

(fluid window-to-size)

(defun menu-size-event (window-to-size window-with-cursor top left bot right)
  (declare (ignore window-with-cursor))

    (Pif (window-equal window-to-size lib-window) -->
        (changesizew window-to-size top bot left right)
        (lib-display)

     || (window-equal window-to-size cmd-window$) -->
        (changesizew window-to-size top bot left right)
	(selectw cmd-window$)
	(movecursor 0 0)
	;; Only the most recent unprocessed line is remembered, so
	;; we have to settle for redisplaying only it.
	(redisplay-line)			
	(selectw cur-window$)

     || t -->
        (Plet (view (car (Psome #'(lambda (v)
                                   (window-equal (sel region
                                                   ((region-of-view v))
                                                   window
                                                 )
						 window-to-size
                                   )
                               )
                              view-stack
                        )
                   )
             )
             (Pif (member 'SIZE
                         (sel region ((region-of-view view)) allowed-events)
                 ) -->
                 ;-- The view associated with window-to-size has been
                 ;-- found and SIZE is an event allowed on it.  Change
                 ;-- the window's size and invoke the proper routine to
                 ;-- redraw it's contents.

                     (Pif (and (eql (sel region ((region-of-view view)) obj-kind)
                                  'PROOF
                              )
                              (> (+ left 10) right)
                         ) -->
                         ;-- red views must be at least 10 columns wide
                            (<- right (+ left 10))
                            (display-message
                               '#.(istring "This view must be at least 10 columns wide.")
                            )
                      fi)

                     (changesizew window-to-size top bot left right)

                     (<- (sel region ((region-of-view view)) top)  0)
                     (<- (sel region ((region-of-view view)) bot)  (- bot top))
                     (<- (sel region ((region-of-view view)) left) 0)
                     (<- (sel region ((region-of-view view)) right) 
                         (- right left)
                     )

                     (Pif (member (sel region ((region-of-view view)) obj-kind)
                               '(TTREE EVAL)
                         ) -->
                         (ted-size-view view)
      
                      || t -->
                         (red-size-view view)
                
                      fi)
     
              || t -->
                 (display-message '#.(istring "Cannot size this window now."))

              fi)
        )

     fi)
)



;--
;-- lisp-mode$ ()
;--
;--   Run Lisp in cmd-window until (EXIT) read.  This is a Lisp
;--   read-eval-print loop.
;--   Must extract the (NL) character from the end of text before
;--   doing a 'readlist'.
;--

(defun lisp-mode$ ()

    (Ploop
        (local text$ (Preadline '#.(istring "L>") #'(lambda (x) (cmd-splicer x)))
               expr$ nil
        )
        (while (not (equal (car (last text$)) '(EXIT))))
        (do
            (<- expr$ (catch-error (readlist 
                                  (append '#.(istring "(")
                                          (nreverse (cdr (nreverse text$)))
                                          '#.(istring ")")
                                  )
                              )
                              nil
                      )
            )
            (Pif expr$ -->
                (mapcar #'(lambda (x) 
                             (putstr
                                 (istring
                                      (Plet (value (catch-error (eval x)
                                                          nil
                                                  )
                                           )
                                          (selectw cmd-window$)
                                          (Pif value  -->  (car value)
                                           || t  -->  nil
                                           fi)
                                      )
                                 )
                             )
                             (putnl)
                         )
                        (car expr$)
                )
             || t -->
                (putstr '#.(istring "Unable to read expression (no evaluation)."))
                (putnl)
            fi)
            (<- text$ (Preadline '#.(istring "L>") #'(lambda (x) (cmd-splicer x))))
        )
    )

;    (putstr '#.(istring "Returning to PRL."))  ; This was annoying.
;    (putnl)
)


;--
;-- ml-mode$ ()
;--
;--   Run ML in cmd-window until (EXIT) read.  This is a
;--   read-eval-print loop that calls ML to process text.
;--   All text up to a line containing ';;' is collected
;--   and sent to ML.
;--

(defvar mlrun$ nil)  ; t if still in ml-mode, nil otherwise.

(defun ml-mode$ ()

    (<- mlrun$ t)

    (Ploop
        (local result$  nil ;-- the result of invoking ML.  This is a pair
                            ;--   (status,message).  status=SUCCESS means
                            ;--   message is the result of the ML eval,
                            ;--   status=FAIL means ML found an error and
                            ;--   message is it, status=ERROR means a Lisp
                            ;--   error occurred in the ML eval and message
                            ;--   is the 'error value' (not a fixnum list).
               text$    nil ;-- the text to send to ML
               line$    nil ;-- an individual line of text being collected
        )
        (while mlrun$)
        (do
            ;-- collect a series of lines up to ';;' and place in text$
            ;-- if line$ end with ';;' or (EXIT) then don't append it to text$.
                (<- text$ nil)
                (<- line$ (Preadline '#.(istring "M>") #'(lambda (x) (cmd-splicer x))))
                (Ploop
                    (while (and (not (equal (car (last line$)) '(EXIT)))
                                (not (semi-semi$ (cdr (reverse line$))))
                           )
                    )
                    (do
                        (<- text$ (append text$
                                          (nreverse (cdr (nreverse line$)))
                                  )
                        )
                        (<- line$ (Preadline '#.(istring "M>")
					     #'(lambda (x) (cmd-splicer x))))
                    )
                )

            (Pif (equal (car (last line$)) '(EXIT)) -->
                (<- mlrun$ nil)

             || t -->
                (<- text$ (append '(Ttree) text$
                                  (nreverse (cdr (nreverse line$)))
                                  (list LF)
                          )
                )
                (<- result$ (subst CR NL (ML text$)))
                (selectw cmd-window$)
                ;-- print (cdr result$) with the leading CR deleted
                ;-- and other CRs turned into calls of putnl
                    (for
                        (ch in (cdr result$))
                        (do
                            (Pif (equal ch CR) --> (putnl)
;--NEXT LINE IS TEMPORARY
                             || (equal ch LF) --> nil
                             || t --> (putstr (list ch))
                             fi)
                        )
                    )

             fi)
  
        )
    )

;   (putstr |)Returning to PRL.^|)  ; This was annoying.
;   (putnl)
)


;;-
;;-
;;-  eval mode
;;-
;;-  



(global eval-env)
(<- eval-env nil)

(deftuple let-term-eval-term kind id prlterm) ;;- kind is EVAL-LET
(deftuple prlterm-eval-term kind prlterm)     ;;- kind is EVAL-TERM

(defun parse-eval-term (ttree)
    (Plet (id   nil
	  term nil
	 )
	 (scan-init ttree)
	 (scan)
	 (Pif (eql token-type TLet) -->
	     (scan)
	     (Pif (eql token-type TId) -->
		 (<- id token-val)
		 (scan)
		 (Pif (eql token-type TEqual) -->
		     (scan)
		     (<- term (parse-from-current-Ttree))
		     (let-term-eval-term 'EVAL-LET id term)
		  || t -->
		     (list 'ERR '|expecting = after id |)
		  fi)
		  
	      || t -->
	         (list 'ERR '|expecting an id after 'let' |)
	      fi)
	     
	  || t -->
	     (<- term (parse-from-current-Ttree))
	     (prlterm-eval-term 'EVAL-TERM term) 
	  fi)
    )
)

;;-
;;- eval-eval-term
;;- 
;;- evaluate eval-term. if it is a binding "let x = e" then evaluate e and bind
;;- this value to x in the (global) eval environment eval-env
;;-
(defun eval-eval-term (eval-term)
    (Pif (eql (car eval-term) 'EVAL-LET) -->
	(Plet (id       (id-of-let-term-eval-term eval-term)
	      new-term ; (subst-for-free-vars
		       ;   (teval (prlterm-of-let-term-eval-term eval-term) eval-env)
		       ; )
	               (iterated-eval
			 (prlterm-of-let-term-eval-term eval-term)
			 eval-env)
	     )
	     (<- eval-env (eval-update id new-term  nil eval-env))
	     new-term
	)
	
     || t  -->
	;(subst-for-free-vars (teval (prlterm-of-prlterm-eval-term eval-term) eval-env))
        (iterated-eval (prlterm-of-prlterm-eval-term eval-term) eval-env)
     fi)
)

;;-
;;- process-eval-expressions
;;-
;;- process "e1 ;; e2 ;; ... ;; en ;;" where each ei is an eval-expression (that is, ei
;;- is either a prl term or an eval binding of the form "let x = e" where e is a prl term
;;-
(defun process-eval-expressions (ttree)
    (Plet (eval-exp nil
	  str1     (cdr ttree)
	  str      nil
	  error    nil
	  result   nil
	  temp     nil
	 )
	 (Ploop
	   (while str1)
	   (do
	     (Pif (or (eql (car str1) CR) (eql (car str1) LF)) -->
		 (<- str1 (cdr str1))
	      || t -->
	         (<- str (cons (car str1) str))
	         (<- str1 (cdr str1))
	      fi)
	   )
	 )
	 (<- str (nreverse str))
	 (Ploop
	   (while (and (some #'(lambda (x) (not (member x white-space)))
			     str)
		       (not error)))
	   (do
	     (Ploop
	       (while (and str (not (semi-semi$ str))))
	       (do
		 (<- eval-exp (cons (car str) eval-exp))
		 (<- str (cdr str))
	       )
	     )
	     (<- eval-exp (nreverse eval-exp))
	     (<- temp (catch 'process-err (parse-eval-term (cons 'Ttree eval-exp))))
	     (Pif (eql (car temp) 'ERR) -->
		 (<- error t)
		 (<- result (cons 'FAILURE (istring (cadr temp))))
	      || t -->
		 (<- temp (catch 'process-err (eval-eval-term temp)))
		 (Pif (eql (car temp) 'ERR) -->
		     (<- error t)
		     (<- result (cons 'FAILURE (istring (cadr temp))))
		  || t -->
		     (<- result
			 (append result (cons CR (Ttree-to-list (term-to-Ttree temp))))
		     )
		  fi)
		   
	    fi)
	   (<- eval-exp nil)
	   (Pif (semi-semi$ str) -->
	       (<- str (cddr str))
	    || t -->
	       (<- error t)
	       (Pif (not (and result (eql (car result) 'FAILURE))) -->
		   (<- result
		       (cons
		          'FAILURE
		          (istring '|Premature end of input - expecting terminating ";;" |)
		       )
	           )
		fi)
	       
	    fi)
	 )
       )
       result
   )
)


;;- 
;;- eval-mode$
;;-
;;- eval - display loop for eval-expressions. 
;;-
(defun eval-mode$ ()
    (Ploop
        (local result$  nil 
               text$    nil ;-- the text to send to eval
               line$    nil ;-- an individual line of text being collected
               evalrun$ t   ;-- t if still in eval-mode, nil otherwise
        )
        (while evalrun$)
        (do
            ;-- collect a series of lines up to ';;' and place in text$
            ;-- Pif line$ end with ';;' or (EXIT) then don't append it to text$.
                (<- text$ nil)
                (<- line$ (Preadline '#.(istring "E>") #'cmd-splicer))
                (Ploop
                    (while (and (not (equal (car (last line$)) '(EXIT)))
                                (not (semi-semi$ (cdr (reverse line$))))
                           )
                    )
                    (do
                        (<- text$ (append text$
                                          (nreverse (cdr (nreverse line$)))
                                  )
                        )
                        (<- line$ (Preadline '#.(istring "E>") #'cmd-splicer))
                    )
                )

            (Pif (equal (car (last line$)) '(EXIT)) -->
                (<- evalrun$ nil)

             || t -->
                (<- text$ (append '(Ttree) text$
                                  (nreverse (cdr (nreverse line$)))
                                  (list CR)
                          )
                )
		(<- result$ (process-eval-expressions text$))
                (selectw cmd-window$)
                ;-- print (cdr result$) with the leading CR deleted
                ;-- and other CRs turned into calls of putnl
                    (for
                        (ch in (cdr result$))
                        (do
                            (Pif (equal ch CR) --> (putnl)
;--NEXT LINE IS TEMPORARY
                             || (equal ch LF) --> nil
                             || t --> (putstr (list ch))
                             fi)
                        )
                    )

             fi)
  
        )
    )

;    (putstr '#.(istring "Returning to PRL."))  ; This was annoying.
;    (putnl)
)



;--
;-- process-eval-object
;-- 
;-- process library object of type EVAL.
;--
(defun process-eval-object (name)
    (Plet (obj       nil     ;-- the library object named by name
          Tt        nil     ;-- the Ttree contained in obj
          message   nil     ;-- error message 
	  result$   nil
         )

        (<- obj (library-object name))

        (<- Tt (sel (eval-object (sel (object obj) value)) body))

        (<- result$ (process-eval-expressions Tt))

        (Pif (eql (car result$) 'FAILURE) -->
            ;-- append to messages the (cdr result$)
            ;-- without the leading CR and any trailing CR
            ;-- and with other CRs turned into ' / '
                (<- message
                    (append
                        (mapcon
			 #'(lambda (c)
			     (Pif (null c) -->
				  nil
				  || (equal c (list CR)) -->
				  nil
				  || (equal (car c) CR) -->
				  (copy '#.(istring " / "))
                                ;;;NEXT LINE IS TEMPORARY
				  || (equal (car c) LF) --> nil
				  || t -->
				  (list (car c))
				  fi)
			     )
                         (cdr result$)
                        )
                        '#.(istring ".  ")
                    )
                )

         fi)

        (Pif (null message) -->
            (set-object-status name 'COMPLETE)
            '(REFERENCED)

         || t -->
            (set-object-status name 'BAD)
            (list 'ERR (implode message))

         fi)

    )
)

;--
;-- semi-semi$ (l)
;--
;--     Return t if the fixnum for ';' occurs twice in a row at
;--     the beginning of l, else nil.

(defun semi-semi$ (l)

    (and (> (length l) 1)
         (equal (car l) #.(ichar #\;))
         (equal (cadr l) #.(ichar #\;))
    )

)


;--
;-- process-ml-object (name:object-name)
;--
;--     Expand the Ttree that is the body of the library object named name.
;--     Send the individual forms contained therein to ML.  If an error
;--     occurs return (ERR atom-whose-printname-is-message).  If no errors
;--     occur then return (REFERENCED), claiming that the ML object depends
;--     on no other objects in the Prl library.
;--

(defun process-ml-object (name)
    (Plet (obj       nil     ;-- the library object named by name
          Tt        nil     ;-- the Ttree contained in obj
          message   nil     ;-- error message produced by ML
	  result$   nil
         )

        (<- obj (library-object name))
        (<- Tt
            ;(change-NL-to-LF
                 (sel (ml-object (sel (object obj) value)) body)
            ;)
        )

	(<- result$ (catch 'process-err
		      	(let ((*hack-ttree?* nil))
			  (ML Tt))))

        (<- result$ (subst CR NL (if (eql (car result$) 'ERR)
				     (cons 'FAILURE (istring (cadr result$)))
				     result$)))

        (Pif (eql (car result$) 'FAILURE) -->
            ;-- append to messages the (cdr result$)
            ;-- without the leading CR and any trailing CR
            ;-- and with other CRs turned into ' / '
                (<- message
                    (append
                        (mapcon
			 #'(lambda (c)
			     (Pif (null c) -->
				  nil
				  || (equal c (list CR)) -->
				  nil
				  || (equal (car c) CR) -->
				  (copy '#.(istring " / "))
                                ;;;NEXT LINE IS TEMPORARY
				  || (equal (car c) LF) --> nil
				  || t -->
				  (list (car c))
				  fi)
			     )
                         (cdr result$)
                        )
                        '#.(istring ".  ")
                    )
                )

         fi)

        (Pif (null message) -->
            (set-object-status name 'COMPLETE)
            '(REFERENCED)

         || t -->
            (set-object-status name 'BAD)
            (list 'ERR (implode message))

         fi)

    )
)



(defun change-NL-to-LF (Tt)
    (cons
        'Ttree
	(mapcar
	    #'(lambda (x)
		 (Pif (consp x) -->
		     (cons
		         (car x)
			 (mapcar #'change-NL-to-LF (cdr x))
		     )
		  || (= x NL) -->
		     LF
		  || t -->
		     x
		  fi)
	     )
	    (cdr Tt)
	)
    )
)



