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


;**************************************************************************
;*                                                                        *
;*      Projet     Formel                       LCF    Project            *
;*                                                                        *
;**************************************************************************
;*                                                                        *
;*            Inria                         University of Cambridge       *
;*      Domaine de Voluceau                   Computer Laboratory         *
;*      78150  Rocquencourt                    Cambridge CB2 3QG          *
;*            France                                England               *
;*                                                                        *
;**************************************************************************

; Pretty printer for ML and OL values and types
; Created by L. Paulson in unix version 3.1
; V4.1 added "inconsistent breaks", record macros, depth limit,
;       hypenated some names

; method based on
; Oppen, Derek C., "Pretty Printing",
;      Technical report STAN-CS-79-770, Stanford University, Stanford, CA.
;      Also in ACM TOPLAS, October 1980, P. 465.

(declaim (special %margin %infinity %ml-space %left-total %right-total
                  %pstack %scan-stack %qleft %qright %prettyon
                  %curr-depth %max-depth))


; constant definitions

(setq %margin 72)               ; right margin
(setq %infinity 999999)         ; large value for default token size


; global variables

(setq %max-depth 30)    ; max be re-set by user

; %ml-space             ; ml-space remaining on this line
; %left-total           ; total width of tokens already printed
; %right-total          ; total width of tokens ever put in queue
; %pstack               ; printing stack with indentation entries
; %prettyon             ; indicates if pretty-printing is on
; %curr-depth           ; current depth of "begins"
; %max-depth            ; max depth of "begins" to print

; data structures

; a token is one of
;    ('string  text)
;    ('break   width  offset)
;    ('begin   indent  [in]consistent )
;    ('end)
(defmacro tok-class (tok) `(car ,tok))
(defmacro get-string-text (tok) `(cadr ,tok))
(defmacro get-break-width (tok) `(cadr ,tok))
(defmacro get-break-offset (tok) `(caddr ,tok))
(defmacro get-block-indent (tok) `(cadr ,tok))
(defmacro get-block-break (tok) `(caddr ,tok))


; the Scan Stack
; each stack element is (left-total . qi)
;   where left-total the value of %left-total when element was entered
;   and qi is the queue element whose size must later be set 
(defmacro make-ss-elem (left qi) `(cons ,left ,qi))
(defmacro get-left-total (x) `(car ,x))
(defmacro get-queue-elem (x) `(cdr ,x))


; the Queue
; elements (size token len)   
(defmacro make-queue-elem (size tt len) `(list ,size ,tt ,len))
(defmacro get-queue-size (q) `(car ,q))
(defmacro get-queue-token (q) `(cadr ,q))
(defmacro get-queue-len (q) `(caddr ,q))
(defmacro put-queue-size (q size) `(rplaca ,q ,size))


; the Printing Stack, %pstack 
;  each element is (break . offset)
(defmacro get-print-break (x) `(car ,x))
(defmacro get-print-indent (x) `(cdr ,x))


(defun push-print-stack (break offset)
    (push (cons break offset) %pstack))


; print n blanks
(defun print-blanks (n)
    (do ((i n (1- i))) ((eql i 0)) (llprinc '| |)))

;-- Changed patom to llprinc in this function.  TBK.
; print a token  
(defun print-token (tt size)
  (case (tok-class tt)
    (string  (llprinc (get-string-text tt)) (decf %ml-space size))
    (begin
     (let ((offset (- %ml-space (get-block-indent tt)))
           (brtype (if (and %prettyon (> size %ml-space)) 
                       (get-block-break tt)
                       'fits)))
       (push-print-stack brtype offset)))
    (end  (pop %pstack))
    (break
      (case (get-print-break (car %pstack))
        (consist (break-new-line tt))
        (inconsist
           (if (> size %ml-space) (break-new-line tt) (break-same-line tt)))
        (fits (break-same-line tt))
        (otherwise (syserror '|bad break in pretty printer|))))
    (otherwise (syserror (cons tt '(bad print-token type))))
    ))                          ; print-token


; print a break, indenting a new line
(defun break-new-line (tt)
    (setq %ml-space (- (get-print-indent (car %pstack)) (get-break-offset tt)))
    (llterpri)
    (print-blanks (- %margin %ml-space))
)                       ; break-new-line


; print a break that fits on the current line
(defun break-same-line (tt)
  (let ((width (get-break-width tt)))
    (decf %ml-space width)
    (print-blanks width)))      ; break-same-line




; routines for scan stack
; determine sizes of blocks


(defun clear-scan-stack nil
    (setq %scan-stack (list (make-ss-elem -1 nil)))
    )   


(defun scan-push nil
    (push (make-ss-elem %right-total (car %qright)) %scan-stack)
    nil)                        ; scan-push


; Pop scan stack and return its value of %qright
(defun scan-pop nil
     (get-queue-elem (pop %scan-stack)))


; test if scan stack contains any data that is not obsolete
(defun scan-empty  nil
    (< (get-left-total (car %scan-stack)) %left-total))


; return the kind of token pointed to by the top element of the scan stack
(defun scan-top nil
    (tok-class (get-queue-token (get-queue-elem (car %scan-stack)))))



; the queue
; size is set when the size of the block is known
; len is the declared length of the token


(defun clear-queue nil
    (setq %left-total 1)
    (setq %right-total 1)
    (setq %qleft nil)
    (setq %qright nil))


; perhaps should use a dummy list header so %qleft is never nil
(defun enqueue (tt size len)
     (incf %right-total len)
     (let ((newcell (ncons (make-queue-elem size tt len))))
       (if %qleft (rplacd %qright newcell) (setq %qleft newcell))
       (setq %qright newcell))
    )


; Print if token size is known or printing is lagging
; Size is known if not negative
; Printing is lagging if the text waiting in the queue requires
;   more room to print than exists on the current line
(defun advance-left nil
     (while (and %qleft
                 (or (not (< (get-queue-size (car %qleft)) 0))
                     (> (- %right-total %left-total) %ml-space)))
        (let ((no-destruct-let (pop %qleft))
             )
           (let ((size (car no-destruct-let))
                 (token (cadr no-destruct-let))
                 (len (caddr no-destruct-let))
                )
               (print-token token (if (< size 0) %infinity size))
               (incf %left-total len)))))



; set size of block on scan stack
(defun setsize (tok)
  (cond ((scan-empty) (clear-scan-stack))
        ((eql (scan-top) tok)
         (let ((qi (scan-pop)))
            (put-queue-size qi (+ %right-total (get-queue-size qi))))))
  nil)                          ; setsize



; *************************************************************
; procedures to control prettyprinter from outside

; the user may set the depth bound %max-depth
; any text nested deeper is printed as the character &


; print a literal string of given length
(defun pstringlen (str len)
   (if (< %curr-depth %max-depth)
    (enqueue-string str len)))  ; pstringlen


(defun enqueue-string (str len)
    (enqueue `(string ,str) len len)
    (advance-left))             ; enqueue-string



; print a string
; in Franz Lisp, flatc does not work on bignums
(defun pstring (str)
    (pstringlen str (length (explodec str))))


; open a new block, indenting if necessary
(defun pbegin-block (indent break)
  (incf %curr-depth)
  (cond ((< %curr-depth %max-depth)
         (enqueue `(begin ,indent ,break) (- 0 %right-total) 0)
         (scan-push))
        ((eql %curr-depth %max-depth)
         (enqueue-string '& 1)))
 )                              ; pbegin-block


; special cases: consistent, inconsistent
(defun pbegin (indent) (pbegin-block indent 'consist))
(defun pibegin (indent) (pbegin-block indent 'inconsist))


; close a block, setting sizes of its subblocks
(defun pend (&optional ignore)
  (cond ((< %curr-depth %max-depth)
         (enqueue '(end) 0 0)
         (setsize 'break)
         (setsize 'begin)))
  (decf %curr-depth))           ; pend


; indicate where a block may be broken
(defun pbreak (blankspace offset)
  (cond ((< %curr-depth %max-depth)
         (enqueue `(break ,blankspace ,offset)
                  (- 0 %right-total)
                  blankspace)
         (setsize 'break)
         (scan-push))))         ; pbreak



; Initialize pretty-printer.
(defun pinit ()
    (clear-queue)
    (clear-scan-stack)
    (setq %curr-depth 0)
    (setq %ml-space %margin)
    (setq %prettyon t)
    (setq %pstack nil)
    (pbegin 0)
    )                           ; pinit


; Turn formatting on or off
;   prevents the signalling of line breaks
;   free ml-space is set to zero to prevent queuing of text
(defun setpretty (pp)
    (setq %prettyon pp)
    (cond (pp (setq %ml-space %margin))
          (t  (setq %ml-space 0)))
)                               ; setpretty



; Print a new line after printing all queued text
(defun pnewline (&optional ignore)
    (pend)
    (setq %right-total %infinity)
    (advance-left)
    (llterpri)
    (pinit)
    )


; Print all remaining text in queue.
; Reinitialize (or turn off) prettyprinting
(defun ml-set_prettymode (pp)
    (pnewline)
    (setpretty pp))

(pinit)
(setpretty t)

(defmlfun (|max_print_depth| ml-max_print_depth) (md) (int -> void)
  (setq %max-depth md))

(dml |set_prettymode| 1 ml-set_prettymode (bool -> void))
(dml |print_newline| 1 pnewline (void -> void))
(dml |print_begin| 1 pbegin (int -> void))
(dml |print_ibegin| 1 pibegin (int -> void))
(dml |print_end| 1 pend (void -> void))
(defmlfun |print_break| (a b) (int -> (int -> void))
  (pbreak a b))
