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

; F-parser.lisp   Original code: parser (lisp 1.6) part of Edinburgh LCF
;                 by M. Gordon, R. Milner and C. Wadsworth   (1978)
;                 Transported by G. Huet in Maclisp on Multics, Fall 1981
;
; V1.4 :idents may not start with ', but may include _.
;       tokens may include %
; V2.2 :breakout instead of err in function fail
; V3.1 : |...| notation for literal atoms
;
; to do:
;    replace parser completely
;    speed it up


(declaim (special token tokchs toktyp char cflag ptoken ptokchs ptoktyp pchar
        parsedepth arg1 lang1 atom-rtn langlp juxtlevel juxt-rtn lang2 msg1
        msg2 ml-space ml-cr ml-lf ml-tab lparen rparen period comma colon scolon lbrkt
        rbrkt tml-sym tokqt-sym arrow-sym sum-sym prod-sym null-sym nulltyptok
        cmntchr tokbearer toklbearer escape-sym mul-sym declnconstrs olinprec
        spec-toks anticnr-tok else-tok metaprec sum-tok
        arrow-tok prod-tok spec-syms rsvdwds eq-sym trap-syms
        trap-then-sym trap-loop-sym trapif-then-sym  
        trapif-loop-sym trapbind-then-sym trapbind-loop-sym 
        bastypes else-sym condl-sym endcnr-sym
        %skiplimit
        start-term-sym end-term-sym  ;-- USED by PRL.
        term-bearer
        ))


(setq %skiplimit 30)                ; number of tokens to print when skipping

(setq cmntchr '%)
(setq ml-space '| |)
(setq ml-cr (implode (list CR))) ;carriage return
(setq ml-lf (implode (list LF))) ;line feed
(setq ml-tab (implode (list TAB)))
(setq lparen '|(|)
(setq rparen '|)|)
(setq period '|.|)
(setq comma '|,|)
(setq colon '|:|)
(setq scolon '|;|)
(setq lbrkt '|[|)
(setq rbrkt '|]|)

(defparameter starttermtok '|'|)    ;-- PRL  terms.
(defparameter endtermtok '|'|)

; Object language tokens  ;-- removed for PRL
;-- (setq endcnrtok '|"|)
;-- (setq anticnr-tok '|^|)
;-- (setq condl-tok '|=>|)
;-- (setq else-tok '\|)  ; |
;-- (setq lambda-tok '|\\|)    ; \\
;-- (setq eq-tok '|==|)
;-- (setq ineq-tok '|<<|)
;-- (setq neg-tok '|~|)
;-- (setq conj-tok '|/\\|)
;-- (setq disj-tok '|\\/|)
;-- (setq imp-tok '|==>|)
;-- (setq iff-tok '|<=>|)
;-- (setq forall-tok '|!|)
;-- (setq exists-tok '|?|)
;-- (setq arrow-tok '|->|)
;-- (setq sum-tok '|+|)
;-- (setq prod-tok '|#|)
;-- (setq nulltyptok '|.|)


;-- (setq spec-toks
;--     '(|\\|  \|  |:|  |(|  |)| |^|  |=>|  |,|  |.| 
;--       |==|  |<<|  |~|  |/\\|  |\\/|  |==>|  |<=>|  |?|  |!|  |"| ))


; Meta language symbols
(setq tml-sym '|;;|)
(setq tokqt-sym '|`|)
(setq escape-sym '|\\|)
(defparameter exfix-sym '|$|)
(defparameter neg-sym '|not|)   ;lc
(setq arrow-sym '|->|)
(setq prod-sym '|#|)
(setq sum-sym '|+|)
(defparameter list-sym '|list|)  ;lc
(setq null-sym '|.|)
;-- (setq cnr-sym '|"|)   Removed for PRL.
;-- (setq endcnr-sym '|"|)

(setq start-term-sym '|'|) ;-- Added for PRL.
(setq end-term-sym '|'|)   ;--  ditto

(setq mul-sym '|*|)
(defparameter div-sym '|/| #|||#)
(defparameter plus-sym '|+|)
(defparameter mns-sym '|-|)
(defparameter conc-sym '|@|)
(setq eq-sym '|=|)
(defparameter lt-sym '|<|)
(defparameter gt-sym '|>|)
(defparameter conj-sym '|&|)
(defparameter disj-sym '|or|)  ;lc
(setq condl-sym '|=>|)
(defparameter lam-sym '|\\|)
(defparameter asgn-sym '|:=|)
(setq else-sym '\| #|||#)   ; This crap to keep zmacs happy.
(setq trap-then-sym '|?|)
(setq trapif-then-sym '|??|)
(setq trapbind-then-sym '|?\\|)
(setq trap-loop-sym '|!|)
(setq trapif-loop-sym '|!!|)
(setq trapbind-loop-sym '|!\\|)

(setq trap-syms
    (list trap-then-sym trap-loop-sym trapif-then-sym trapif-loop-sym
          trapbind-then-sym trapbind-loop-sym))


(setq spec-syms
     (nconc (list div-sym else-sym escape-sym
                  trapbind-then-sym trapbind-loop-sym)
;                         /       |        \\        ?\\     !\\    |
        '(|:| |(|  |)|  |#|  ->  |,|  |.|  |[|  |]|  |;|  |;;|  :=
          |'|   %  $  |`|  |``|  _  *  +  -  @  =  <  >  &  =>
          ?  ?? !  !! )))  ;-- PRL: removed ", added '.


(setq rsvdwds '(|let| |letref| |letrec| |and| |with| |in|
                |deftype| |lettype| |abstype| |absrectype|
                |where| |whereref| |whererec|
                |wheretype| |whereabstype| |whereabsrectype|
                |begin| |end| |do| |it| |or|
                |not| |true| |false|
                |if| |then| |loop| |else|))
;--
;--  fail and failwith have been removed from the above list since
;--  we re-work them to give back-trace information.
;--


(setq declnconstrs '(mk-let mk-letrec mk-letref mk-deftype
                     mk-defrectype mk-abstype mk-absrectype))

(defparameter exprconstrs '(mk-boolconst mk-intconst mk-tokconst mk-var
                       mk-termconst mk-formconst  ;-- PRL
          mk-appn mk-abstr mk-null-abstr    ;-- last new for PRL
          mk-dupl mk-empty
          mk-fail  mk-binop mk-unop
          mk-assign mk-list mk-seq mk-trap mk-test
          mk-straint mk-in mk-ind mk-quot mk-tyquot))


(setq tokbearer '|<TOKEN>|)
(setq toklbearer '|<TOKEN-LIST>|)
(setq term-bearer '|<PRL-TERM>|)  ;-- for prl.
(defparameter pp-sym " ... ")





; get next char
(defun gnc ()
       (let ((ch (nextch)))
            ;not possible to skip blanks because of vartypes
          (cond ((eql ch cmntchr)(while (not (eql (nextch) cmntchr)))
                            (gnc))   ;skip comments;
                (t ch))))  ;gnc;

;--  initialize lexical analyzer. Complicated by the fact that an eof
;-- durring initialization, this is not an error, but a normal end of
;-- ml.  We skip characters until we have something that is not
;-- part of a comment or a space.  If an eof occurs, then we throw
;-- a new token that indicates normal termination.

(defun initlean ()
    (setq token nil)
    (setq tokchs nil)
    (setq toktyp nil)
    (setf (get tokbearer 'tokval) nil)
    (setf (get toklbearer 'toklval) nil)
    (setf (get term-bearer 'term-val) nil)
    (cond            ;-- eof will be indicated with value t.
        ((tag eoftag        
             (setq char (gnc))  ;-- get a character.  Skip comments.
             (while
                 (spacep char)
                 (setq char (gnc))  ;-- skip spaces.
             )
             nil      ;-- No problems were encountered. If eof occurs,
                      ;-- this is not evaluated.
         )
            (breakout tmltag t)    ;-- eof occured.  Stop.
        )
    )
)  ;initlean

; get next token
(defun gnt ()
       (setq cflag (spacep char))                     ;for vartypes (berk)
       (setq ptoken token)
       (setq ptokchs tokchs)
       (setq ptoktyp toktyp)
       (setq pchar char)
       (while (spacep char)(setq pchar (setq char (gnc)))) ;remove spacing
       (cond ((letterp char) (setq tokchs (list char))     ;ident
                         (setq toktyp 1)
                         (ident))
           ((digitp char) (setq tokchs (list char))      ;number (ML only)
                        (setq toktyp 1)
                        (if (eql lang1 'ml1) (numb) (ident)))
           ((eql char tokqt-sym) (setq tokchs nil)         ;token(list?)
                           (setq toktyp 1)
                           (if (eql (setq char (nextch)) tokqt-sym)
                               (tcnl)                ;token list
                               (tcn)))               ;single token
           ((eql char start-term-sym)   ;-- PRL terms
               (setq toktyp 1)
               (set-term-token)
           )
           (t (setq toktyp 2)
              (setq char (gnc))
              (setq token pchar)
              (if (and (eql token scolon) (eql char ml-lf)) ;on multics: lines end
                (setq char (gnc)))            ; with ml-lf ;was (prog2 (gnc)(gnc))
              (while (member char (get token 'double))
                  (setq token (concat token char))
                (setq char (gnc)))))
       token    
)  ;gnt

; scan a number and return its numeric value
(defun numb ()
  (while (digitp (setq char (gnc))) (push char tokchs))
  (setq token (readlist (reverse tokchs)))
  )  ;numb

; scan an identifier as a symbol (used also for numbers in OL)
(defun ident ()
  (while (alphanump (setq char (gnc))) (push char tokchs))
  (setq token (implode (reverse tokchs)))
  )  ;ident

(defun tcn ()
  (prog nil
   l    (cond ((eql char escape-sym)
               (setq char (nextch))  ;NEW nextch was gnc
               (setq tokchs (append (escape-rtn) tokchs)))
              ((eql char tokqt-sym)
               (setq char (gnc))
               (setq token tokbearer)
               (setf
                (get tokbearer 'tokval)
                (append (get tokbearer 'tokval)
                        (list (implode (reverse tokchs)))))
               (return token))
              (t (setq tokchs (cons char tokchs))))
        (setq char (nextch))  ;NEW nextch was gnc
        (go l))
  )  ;tcn

(defun tcnl ()
  (prog (tokl)
        (setq tokl nil)
   l1   (setq char (nextch))  ;NEW nextch was gnc
   l2   (cond
         ((eql char escape-sym)
          (setq char (nextch))  ;NEW nextch was gnc
          (setq tokchs (append (escape-rtn) tokchs))
          (go l1))
         ((eql char tokqt-sym)
          (cond
           ((eql (setq char (nextch)) tokqt-sym)  ;NEW nextch was gnc
            (cond
             (tokchs (setq tokl (cons (implode (reverse tokchs)) tokl))))
            (setq token toklbearer)
            (setf
             (get toklbearer 'toklval)
             (append (get toklbearer 'toklval)
                     (list (reverse tokl))))
            (setq char (gnc))
            (return token))
           (t (setq tokchs (cons tokqt-sym tokchs)) (go l2))))
         ((spacep char)
          (while (spacep (setq char (gnc))))   ;remove spaces
          (if tokchs (setq tokl (cons (implode (reverse tokchs)) tokl)))
          (setq tokchs nil)
          (go l2))
         (t (setq tokchs (cons char tokchs)) (go l1))))
  )  ;tcnl


(defun set-term-token ()
    (prog (result)
        (setq result (prl-parse-term))
        (setf (get term-bearer 'term-val)
		 (append
		   (get term-bearer 'term-val)
                   (list result)
		 )
	)
        (setq token term-bearer)
        (gnc)               ;-- skip over '
        (setq char (gnc))
        (return token)
    )
)




(defun escape-rtn ()
  (cond ((eql char '|0|) (charseq ml-space 10.))                   ;NEW '|0| was 0
        ((digitp char) (charseq ml-space (readlist (list char)))) ;NEW same
        ((get char 'stringmacro))
        (t (list char)))
  )  ;escape-rtn

(defun vartype-rtn ()
  (prog (n)
        (cond (cflag (return mul-sym)))
        (setq n 1)
   loop (cond ((or (numberp token) (eql toktyp 1) (eql token mul-sym)))
              (t (return (implode (charseq mul-sym n)))))
        (gnt)
        (cond
         ((and (eql ptoken mul-sym) (not cflag))
          (setq n (1+ n))
          (go loop)))
        (return (implode (append (charseq mul-sym n) (explode ptoken)))))
  )  ;vartype-rtn

(setq token nil)  (setq ptoken nil)
(setq tokchs nil) (setq ptokchs nil)
(setq toktyp nil) (setq ptoktyp nil)
(setq char ml-space)

; Assumes a is a non-numeric atom, returns  number which is ascii-code of the
; first char of a's print-name
(defun getascii (a) (char->ichar (aref (string a) 0) LF))

(defun asciip (n1 a n2) (< (1- n1) (getascii a) (1+ n2)))  ;asciip

; Unix -- changed character codes to decimal
(defun charp (a)   (asciip  33. a 125.))    ; octal  41 - 175
(defun upperp (a)  (asciip 65. a 90.))      ; octal 101 - 132
(defun lowerp (a)  (asciip 97. a 122.))     ; octal 141 - 172
(defun digitp (a)  (asciip  48. a  57.))    ; octal  60 -  71
(defun digit8p (a) (asciip  48. a  55.))    ; octal  60 -  67

(defun letterp (a) (or (upperp a) (lowerp a)))
(defun alphanump (a) (or (letterp a) (digitp a) (eql a '|'|)(eql a '|_|)))
(defun upperordigitp (a) (or (upperp a) (digitp a)))
(defun spacep (a) (member a (list ml-space ml-cr ml-lf ml-tab)))

; set up token escape codes
(setf (get 'L 'stringmacro) (list ml-lf))
(setf (get 'R 'stringmacro) (list ml-cr))
(setf (get 'S 'stringmacro) (list ml-space))
(setf (get 'T 'stringmacro) (list ml-tab))


; set up lexical analysis of multi-character special symbols
; ideally should be divided ML from OL
(setf (get '|=| 'double) '(|>| |=|))
(setf (get '|-| 'double) '(|>|))
(setf (get '|<| 'double) '(|<| |=|))
(setf (get '|:| 'double) '(|=|))
(setf (get '|`| 'double) '(|`|))
(setf (get '|?| 'double) '(|?| |\\|))
(setf (get '|;| 'double) '(|;|))
(setf (get '|!| 'double) '(|!| |\\|))
(setf (get '|/| 'double) '(|\\|))
(setf (get '|\\| 'double) '(|/|))
(setf (get '|==| 'double) '(|>|))
(setf (get '|<=| 'double) '(|>|))


(defun unop (op code) (setf (get op lang1) code))  ;unop

(defun bnop (op code) (setf (get op lang2) code))  ;bnop

(defun binop (op lp code)
  (setf (get op lang2) code) (setf (get op langlp) lp)
  )  ;binop

(defun check (tok rslt msg)
  (cond ((eql tok token) (gnt) rslt) (t (fail msg)))
  )  ;check

(defun fail (msg)
    (llprinc msg) (llterpri)
    (llprint '|skipping:|)
    (llprinc ptoken)
    (llprinc ml-space)
    (llprinc token)
    (llprinc ml-space)
    (do ((i %skiplimit (1- i)))
        ((eql token tml-sym) (ifn (> i 0) (llprinc '|. . .|)))
        (gnt)
        (if (> i 0) (progn (llprinc token) (llprinc ml-space))))
 ;--   (initlean)   leave this to PRL
    (eqsetup)
    (persetup)
    (scolonsetup)
    (breakout parse nil)
  ) ;fail


(setq arg1 nil)

; main parse routine
; parses text until reaching level cpl
; saves its result in the *special arg1
(defun parse-pop (cpl)
 (prog  (x)
   (incf parsedepth)
   (gnt)
   (setq arg1
         (cond ((not (or (numberp ptoken)
                     (null (setq x (get ptoken lang1)))))
              (eval x))
             (t (eval atom-rtn))))
l  (setq x (cond ((numberp token) nil) (t (get token langlp))))
   (cond ((and (null x) (not (< cpl juxtlevel)))
          (decf parsedepth) (return arg1))
         ((null x) (setq arg1 (eval juxt-rtn)) (go l))
         ((not (< cpl x))
          (decf parsedepth) (return arg1))
         (t nil))
   (cond
    ((member (car arg1) declnconstrs)
     (fail '|non top level decln must have IN clause|)))
   (setq x (get token lang2))

    (if (null x) (fail (concat token '| in the wrong place|)))
   (gnt)
   (setq arg1 (eval x))
   (go l))
  )  ;parse-pop

