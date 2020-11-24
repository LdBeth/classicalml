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


;*************************************************************************
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



; F-parsml.lisp   Original code: parsml (lisp 1.6) part of Edinburgh LCF
;                 by M. Gordon, R. Milner and C. Wadsworth   (1978)
;                 Transported by G. Huet in Maclisp on Multics, Fall 1981
; V4-1 Added primitive type obj  GH
;      Corrected bug sec-rtn




(declaim (special token tokchs toktyp char cflag ptoken ptokchs ptoktyp pchar
    parsedepth arg1 lang1 atom-rtn langlp juxtlevel juxt-rtn lang2 msg1 msg2
    ml-space ml-cr ml-lf ml-tab lparen rparen period comma colon scolon lbrkt rbrkt
    tml-sym tokqt-sym arrow-sym sum-sym prod-sym null-sym
    cmntchr tokbearer toklbearer escape-sym mul-sym declnconstrs olinprec
    spec-toks anticnr-tok else-tok metaprec arrow-tok
    sum-tok prod-tok spec-syms rsvdwds eq-sym
    trap-syms trap-then-sym trap-loop-sym trapif-then-sym
    trapif-loop-sym trapbind-then-sym trapbind-loop-sym
    bastypes else-sym condl-sym endcnr-sym
    start-term-sym end-term-sym  ;-- PRL
    term-bearer
    ))



(defun parseml (pl)
       (prog (lang1 lang2 langlp atom-rtn juxtlevel juxt-rtn *read-base* parsedepth)
           (setq lang1 'ml1)
           (setq lang2 'ml2)
           (setq langlp 'mllp)
           (setq atom-rtn '(mlatomr))
           (setq juxtlevel 1010)
           (setq juxt-rtn '(mljuxt arg1))
           (setq *read-base* 10.)
           (setq parsedepth 0)
           (return (parse-pop pl))))  ;parseml

(defun istypedec (class)
 (member class '(mk-deftype mk-defrectype mk-abstype mk-absrectype)))  ;istypedec

(defun isabstypedec (class)
  (member class '(mk-abstype mk-absrectype)))  ;isabstypedec

(defun declnchk (x msg)
  (cond ((member (car x) declnconstrs) x) (t (fail msg))))  ;delnchk

(defun ultabstr (e)
       (or (eql (car e) 'mk-abstr)
         (and (eql (car e) 'mk-straint) (ultabstr (cadr e)))))  ;ultabstr

(defun idchk (id msg)
      (cond ((or (numberp id) (member id spec-syms) (member id rsvdwds)) (fail msg))
          (t id)))  ;idchk

(defun eqsetup ()
       (setf (get eq-sym 'ml2) '(appl-rtn 550 '=))
       (setf (get eq-sym 'mllp) 540))  ;eqsetup

(defun persetup () (binop period 650 '(appl-rtn 640 '|.|)))  ;persetup

(defun scolonsetup () (setf (get scolon 'mllp) 150))  ;scolonsetup

(defun sec-rtn (x)
   (let ((l '||))
      (ifn (eql parsedepth 1)
         (fail '|sections can only be opened or closed at top level|))
      (while (neq token tml-sym)
           (ifn (or (eql token period) (eql toktyp 1))
                (fail '|bad section name|))

           (setq l (concat l token))
           (gnt))
      (cons x (if (null l) nil (list l)))))  ;sec-rtn   ;GH

(defun mlinfix2 (x typ)
       (setf (get x 'mlinfix) typ)
       (binop x 450     (list (cond ((eql typ 'paired) 'mlinf-rtn) (t 'mlcinf-rtn))
                      (list 'quote x))))  ;mlinfix2

(defun mlinf-rtn (x)
   (list 'mk-appn (list 'mk-var x) (list 'mk-dupl arg1 (parse-pop 460))))  ;mlinf-rtn

(defun mlcinf-rtn (x)
   (list 'mk-appn (list 'mk-appn (list 'mk-var x) arg1) (parse-pop 460)))  ;mlcinf-rtn

(defun exfix-rtn ()
       (gnt)
       (list 'mk-var (cond ((eql ptoken tokbearer) (get tokbearer 'tokval))
                       (t ptoken))))  ;exfix-rtn

;-- Process PRL terms.  The value on the property list of of the term-bearer
;-- was returned by the function prl-parse-term

(defun process-prl-term ()
    (prog (raw-term result terms)
        (setq terms (get term-bearer 'term-val))
        (setq raw-term (car terms))  ;-- raw as returned
                                     ;-- by PRL.
        (setf (get term-bearer 'term-val) (cdr terms))   ;-- remove this term from list.

        (cond ((equal (car raw-term) 'TERM)
                  (setq result (list 'mk-termconst
                                   (ml-term
                                        (cdr raw-term))) ;-- tag as term
                  )
              )

              (t (breakout parse (cdr raw-term)))
        )
        (return result)
    )
)



(defun mlatomr ()
    (cond ((member ptoken spec-syms) (fail (concat ptoken '| cannot be a var|)))
        ((numberp ptoken) (list 'mk-intconst ptoken))
        ((eql ptoken tokbearer)
         (list 'mk-tokconst
               (let ((x (get tokbearer 'tokval)))
                  (setf (get tokbearer 'tokval) (cdr x)) (car x))))
        ((eql ptoken toklbearer)
         (cons 'mk-list
               (mapcar #'(lambda (x) (list 'mk-tokconst x))
		       (let ((x (get toklbearer 'toklval)))
                        (setf (get toklbearer 'toklval) (cdr x))(car x)))))
        ((eql ptoken term-bearer)
            (process-prl-term)
        )
        (t (list 'mk-var ptoken))))  ;mlatomr


(defun appl-rtn (pl rn)
 (let ((x arg1)) (parse-pop pl) (list 'mk-binop rn x arg1)))  ;appl-rtn

(defun lparen-rtn ()
       (cond ((eql token rparen) (gnt) '(mk-empty))
           (t (check rparen (parse-pop 15) '|bad paren balance|))))  ;lparen-rtn

(defun test-rtn  nil
       (prog (x1 x2 xl xt)
  loop (setq x1 (parse-pop 30))
       (setq xt token)
       (cond ((not (member xt '(|then| |loop|)))
            (fail '|missing then or loop after if|))
           (t (gnt)))
       (setq x2 (parse-pop 320))
       (setq xl (cons (cons (if (eql xt '|then|) 'once 'iter) (cons x1 x2)) xl))
       (cond ((member token '(|test| |if|)) (gnt) (go loop)))
       (setq xt token)
       (cond ((member xt '(|else| |loop|)) (gnt)
              (return (list 'mk-test
                        (reverse xl)
                        (cons (if (eql xt '|else|) 'once 'iter) (parse-pop 320)))))
           (t (return (list 'mk-test (reverse xl)))))))  ;test-rtn

(defun trap-rtn (trap)
   (prog        (x x1 x2 xl)
        (setq x arg1)
   loop (setq x1 (parse-pop 1020))
          (if (member token trap-syms) (fail '|missing trap body|))
        (setq x2 (parse-pop 270))
        (setq xl (cons (cons trap (cons x1 x2)) xl))
        (cond ((member token trap-syms)
               (setq trap (if (member token (list trap-then-sym trapif-then-sym trapbind-then-sym)) 'once
                          'iter))))
        (cond ((member token (list trapif-then-sym trapif-loop-sym)) (gnt) (go loop)))
        (cond ((member token (list trap-then-sym trap-loop-sym))
               (gnt)
               (return (list 'mk-trap x (reverse xl) (cons trap (parse-pop 240))))))
        (cond ((member token (list trapbind-then-sym trapbind-loop-sym))
               (gnt)
               (return
                 (list 'mk-trap x (reverse xl)
                     (cons (cons trap token) (prog2 (gnt) (parse-pop 270)))))))
        (return (list 'mk-trap x (reverse xl)))))  ;trap-rtn

(defun trapbind-rtn (trap)
  (list 'mk-trap arg1 nil
        (cons (cons trap (idchk token (concat token '| cannot be bound|)))
            (prog2 (gnt) (parse-pop 270)))))  ;trapbind-rtn

(defun list-rtn ()
    (prog       (l scolonlp)
        (setq scolonlp (get scolon 'mllp))
     loop       (cond ((eql token rbrkt) (gnt) (return (cons 'mk-list (reverse l)))))
          (setf (get scolon 'mllp) 20)
        (setq l (cons (parse-pop 30) l))
        (setf (get scolon 'mllp) scolonlp)
        (cond ((eql token rbrkt) (go loop))
              (t (check scolon arg1 '|funny list separator|)
                 (go loop)))))  ;list-rtn

(defun seq-rtn ()
    (prog       (xl)
        (setq xl (list arg1))
     loop       (setq xl (cons (parse-pop 160) xl))
          (cond ((eql token scolon) (gnt) (go loop)))
        (return (list 'mk-seq (reverse (cdr xl)) (car xl)))))  ;seq-rtn

(defun let-rtn (class)
       (setq arg1 (bind-rtn class))
       (cond ((eql token '|in|) (gnt) (in-rtn))
           ((< 1 parsedepth)
            (fail '|non top level decln must have in clause|))
           (t arg1)))  ;let-rtn

(defun bind-rtn (class)
    (prog       (dl x y)
        (cond ((isabstypedec class) (return (abstypbind-rtn class)))
              ((istypedec class) (return (typbind-rtn class))))
      l1        (binop eq-sym 30 '(fail '|= inside definiend|))
          (setq x (check eq-sym (parse-pop 50) '|lost = in decln|))
        (eqsetup)
        (setq y (parse-pop 120))
      l2        (cond ((eql (car x) 'mk-straint)
               (setq y (list 'mk-straint y (caddr x)))
               (setq x (cadr x))
               (go l2))
              ((eql (car x) 'mk-appn) (go l4))
              ((eql (car x) 'mk-var) (go ok))
              ((eql class 'mk-letrec) (fail '|illegal form of letrec|))
              (t nil))
          (chkvarstr x
               '|multiple binding occurence of var in decln|
               '|illegal form of declaration|)
        (go ok)
      l4        (setq y (list 'mk-abstr
                    (chkvarstr (caddr x)
                             '|multiply occurring fn param|
                             '|bad fn param structure|)
                    y))
          (setq x (cadr x))
      l5        (cond ((eql (car x) 'mk-straint)
               (setq y (list 'mk-straint y (caddr x)))
               (setq x (cadr x))
               (go l5))
              ((eql (car x) 'mk-appn) (go l4))
              ((eql (car x) 'mk-var) (go ok))
              (t (fail '|bad definiend of function|)))
      ok        (cond
          ((and (eql class 'mk-letrec) (not (ultabstr y)))
           (fail '|letrec of non-function|)))
          (setq dl (cons (cons x y) dl))
        (cond ((eql token '|and|) (prog2 (gnt) (go l1))))
        (setq x (caar dl))
        (setq y (cdar dl))
      l9        (setq dl (cdr dl))
        (cond
          ((null dl)
           (return (list class (chkvarstr x '|multiply occurring var in declaration| nil) y))))
        (setq x (list 'mk-dupl (caar dl) x))
        (setq y (list 'mk-dupl (cdar dl) y))
        (go l9)))  ;bind-rtn

(defun typbind-rtn (class)
    (prog       (dl)
     loop       (cond ((not (eql toktyp 1)) (fail (concat token '| not allowed as a type|)))
              ((member token bastypes) (fail (concat token '| musn't be redefined|)))

                              ((not (null (assoc token dl))) (fail (concat token '| defined more than once|)))
              ((not (eql (gnt) eq-sym)) (fail '|missing = in type declaration|)))
     (setq dl (cons (cons ptoken (prog2 (gnt) (mlt))) dl))
     (cond ((eql token '|and|) (gnt) (go loop)))
     (return (list class dl))))  ;typbind-rtn

(defun abstypbind-rtn (class)
   (prog        (tyargs dl)
    loop        (setq tyargs nil)
          (cond ((eql token mul-sym) (gnt) (setq tyargs (list (vartype-rtn))))
              ((eql token lparen) (if (eql (gnt) rparen) (gnt) (go l2))))
      l1        (cond ((not (eql toktyp 1)) (fail '|bad type constructor|))
              ((not (eql (gnt) eq-sym)) (fail '|bad type constructor|)))
          (setq dl (cons (cons ptoken (cons tyargs (prog2 (gnt) (mlt)))) dl))
        (cond ((eql token '|and|) (gnt) (go loop))
              ((eql token '|with|) (gnt))
              (t (fail '|missing with|)))
        (return (list class dl (bind-rtn 'mk-let)))
      l2        (cond ((not (eql token mul-sym)) (fail '|type constructor's args not variables|)))
          (gnt)
        (setq tyargs (append tyargs (list (vartype-rtn))))
        (cond ((eql token comma) (gnt) (go l2))
              ((eql token rparen) (gnt) (go l1))
              (t (fail '|bad args to type constructor|)))))  ;abstyp-rtn

(defun chkvarstr (x msg1 msg2)
       (chkvarstrx x nil msg1 msg2) x)  ;chkvarstr

(defun chkvarstrx (x idlst msg1 msg2)
    (cond       ((eql (car x) 'mk-straint) (chkvarstrx (cadr x) idlst msg1 msg2))
        ((eql (car x) 'mk-var)
         (if (member (cadr x) idlst) (fail msg1) (cons (cadr x) idlst)))
        ((eql (car x) 'mk-dupl)
         (chkvarstrx (caddr x) (chkvarstrx (cadr x) idlst msg1 msg2) msg1 msg2))
        ((eql (car x) 'mk-empty) idlst)
        ((eql (car x) 'mk-list)
         (itlist #'(lambda (x idlst) (chkvarstrx x idlst msg1 msg2))
		 (cdr x) idlst))
        ((and (eql (car x) 'mk-binop) (eql (cadr x) '|.|))
         (chkvarstrx (cadddr x) (chkvarstrx (caddr x) idlst msg1 msg2) msg1 msg2))
        (t (fail msg2))))  ;chkvarstrx

(defun in-rtn ()
    (list       (cond ((isabstypedec (car arg1)) 'mk-ina)
              ((istypedec (car arg1)) 'mk-ind)
              (t 'mk-in))
        (declnchk arg1 '|in must follow decln|)
        (parse-pop 100)))  ;in-rtn

(defun where-rtn (class)
    (let ((e arg1))
         (list (cond ((isabstypedec class) 'mk-ina)
                 ((istypedec class) 'mk-ind)
                 (t 'mk-in))
             (declnchk (bind-rtn class) '|bad decln in where|)
             e)))  ;where-rtn

(defun lamb-rtn ()
    (let ((iter nil))
         (binop period 220 '(appl-rtn 210 '|.|))
         (cond ((eql token period)     ;-- nullary lambda.
		(gnt)                 ;-- changed for PRL. 
		(persetup)
		`(mk-null-abstr ,(parse-pop 130))
	       )
	       (t                     ;-- normal case.
                  (setq iter (parse-pop 230))
                  (persetup)
                  (iter-rtn (check period iter '|lost period in abstrn|) (parse-pop 130))))
     )
)
     ;lamb-rtn

(defun iter-rtn (a b)
    (cond       ((eql (car a) 'mk-appn)
         (iter-rtn (cadr a)
                (list 'mk-abstr
                      (chkvarstr (caddr a)
                               '|multiple lambda binding for var|
                               '|bad var structure in iterated abstrn|)
                      b)))
        (t (list 'mk-abstr
                 (chkvarstr a
                        '|multiple lambda binding for var|
                        '|bad var structure in abstrn|)
                 b))))  ;iter-rtn

(defun assign-rtn ()
    (list       'mk-assign
        (chkvarstr arg1
                 '|var duplicated on left of assgt|
                 '|bad left hand side of assgt|)
        (parse-pop 350)))  ;assign-rtn

(defun dupl-rtn () (list 'mk-dupl arg1 (parse-pop 370)))  ;dupl-rtn

(defun cond-rtn ()
    (prog       (x1 x2 xl)
     loop       (setq x1 arg1)
          (setq x2 (parse-pop 30))
        (setq xl (cons (cons 'once (cons x1 x2)) xl))
        (cond ((not (eql token else-sym)) (fail (list 'missing else-sym))) (t (gnt)))
        (parse-pop 430)
        (cond ((eql token condl-sym) (gnt) (go loop)))
        (return (list 'mk-test (reverse xl) (cons 'once arg1)))))
    ;cond-rtn

(defun failwith-rtn () (list 'mk-failwith (parse-pop 340)))  ;failwith-rtn

(defun mltyp-rtn () (list 'mk-straint arg1 (mlt)))  ;mltyp-rtn

(defun mlt () (mlt1 (mlt2 (mlt3 (mlt4)))))  ;mlt

(defun mlt1 (x)
    (cond ((eql token arrow-sym) (gnt) (list 'mk-funtyp x (mlt))) (t x)))  ;mlt1

(defun mlt2 (x)
     (cond ((eql token sum-sym) (gnt) (list 'mk-sumtyp x (mlt2 (mlt3 (mlt4)))))
         (t x)))  ;mlt2

(defun mlt3 (x)
    (cond ((eql token prod-sym) (gnt) (list 'mk-prodtyp x (mlt3 (mlt4))))
        (t x)))  ;mlt3

(defun mlt4 ()
    (prog       (x)
        (gnt)
        (cond ((eql ptoken lparen) (setq x (cond ((eql token rparen) (gnt) nil)
                                        (t (mlt5)))) (go l)))
        (setq x
              (list
                (cond ((eql ptoken null-sym) '(mk-nulltyp))
                    ((eql ptoken mul-sym) (list 'mk-vartyp (vartype-rtn)))

                                    ((not (eql ptoktyp 1)) (fail (concat ptoken '| is not allowed in a type|)))
                    ((eql ptoken '|int|) '(mk-inttyp))
                    ((eql ptoken '|obj|) '(mk-objtyp))
                    ((eql ptoken '|bool|) '(mk-booltyp))
                    ((eql ptoken '|term|) '(mk-termtyp))  ;-- chaged for PRL
;--                 ((eql ptoken '|formula|) '(mk-formtyp))
                    ((eql ptoken '|proof|) '(mk-prooftyp))
                    ((eql ptoken '|declaration|) '(mk-declarationtyp))
                    ((eql ptoken '|rule|) '(mk-ruletyp))

;--                 ((eql ptoken 'thm) '(mk-thmtyp))
;--                 ((eql ptoken 'type) '(mk-typetyp))
                    ((member ptoken '(|token| |tok|)) '(mk-toktyp))
                    ((eql ptoken arrow-sym)
		     `(mk-null-funtyp ,(mlt))
		    )
                    (t (list 'mk-consttyp ptoken)))))
       l        (cond ((or (not (eql toktyp 1)) (member token rsvdwds))
               (return
                 (cond ((not (eql (length x) 1)) (fail '(missing type constructor)))
                     (t (return (car x))))))
              (t (gnt)))
       (setq x (cond ((eql ptoken '|list|) (list (cons 'mk-listyp x)))
                 (t (list (cons 'mk-consttyp (cons ptoken x))))))
       (go l)))  ;mlt4

(defun mlt5 ()
    (prog       (x)
        (setq x (list (mlt)))
     loop       (cond ((eql token rparen) (gnt) (return x))
              ((eql token comma) (gnt) (setq x (append x (list (mlt)))) (go loop))
              (t (fail '|missing separator or terminator in type|)))))  ;mlt5

(defun mljuxt (x) (list 'mk-appn x (parse-pop 1020)))  ;mljuxt
   
; quotations       REMOVED BY PRL
;-- (defun cnr-rtn ()
;--     (check endcnr-sym
;--      (selectq token
;--           (|:| (gnt) (list 'mk-tyquot (olt)))
;--           (t (list 'mk-quot (parse-ol)))) 
;--      '|cannot find end of quotation|))  ;cnr-rtn




(setq bastypes '(|int| |bool| |token| |tok| |.| |term| |proof| |declaration|
                    |rule|)) ;-- PRL
(setq lang1 'ml1)
(setq lang2 'ml2)
(setq langlp 'mllp)
(setq metaprec 20)
(unop '|begin| '(sec-rtn 'mk-begin))
(unop '|end| '(sec-rtn 'mk-end))
(unop tml-sym '(fail '(stuff missing)))
(unop '|true| ''(mk-boolconst t))
(unop '|false| ''(mk-boolconst nil))
(unop '|fail| ''(mk-fail))
(unop '|break| ''(mk-fail))
(unop exfix-sym '(exfix-rtn))
(unop lparen '(lparen-rtn))
(unop '|do| '(list 'mk-unop '|do| (parse-pop 410)))
(unop '|if| '(test-rtn))
(unop '|loop| '(list 'mk-test nil (cons 'iter (parse-pop 320))))
(unop '|else| '(list 'mk-test nil (cons 'once (parse-pop 320))))
(bnop trap-then-sym '(list 'mk-trap arg1 nil (cons 'once (parse-pop 240))))
(bnop trap-loop-sym '(list 'mk-trap arg1 nil (cons 'iter (parse-pop 240))))
(bnop trapif-then-sym '(trap-rtn 'once))
(bnop trapif-loop-sym '(trap-rtn 'iter))
(bnop trapbind-then-sym '(trapbind-rtn 'once))
(bnop trapbind-loop-sym '(trapbind-rtn 'iter))
(unop lbrkt '(list-rtn))
(bnop scolon '(seq-rtn))
(unop '|let| '(let-rtn 'mk-let))
(unop '|letrec| '(let-rtn 'mk-letrec))
(unop '|letref| '(let-rtn 'mk-letref))
(unop '|deftype| '(let-rtn 'mk-deftype))
(unop '|lettype| '(let-rtn 'mk-deftype))
(unop '|abstype| '(let-rtn 'mk-abstype))
(unop '|absrectype| '(let-rtn 'mk-absrectype))
(bnop '|in| '(in-rtn))
(bnop '|where| '(where-rtn 'mk-let))
(bnop '|whererec| '(where-rtn 'mk-letrec))
(bnop '|whereref| '(where-rtn 'mk-letref))
(bnop '|wheretype| '(where-rtn 'mk-deftype))
(bnop '|whereabstype| '(where-rtn 'mk-abstype))
(bnop '|whereabsrectype| '(where-rtn 'mk-absrectype))
(unop lam-sym '(lamb-rtn))
(bnop asgn-sym '(assign-rtn))
(bnop comma '(dupl-rtn))
(bnop condl-sym '(cond-rtn))
(bnop disj-sym '(appl-rtn 470 '|%or|))
(bnop conj-sym '(appl-rtn 510 '%&))
(unop '|failwith| '(failwith-rtn))
(unop '|breakwith| '(failwith-rtn))
(unop '|not| '(list 'mk-unop '|not| (parse-pop 530)))
(bnop eq-sym '(appl-rtn 550 eq-sym))
(bnop lt-sym '(appl-rtn 610 lt-sym))
(bnop gt-sym '(appl-rtn 570 gt-sym))
(bnop conc-sym '(appl-rtn 620 conc-sym))
(bnop period '(appl-rtn 640 period))
(bnop plus-sym '(appl-rtn 710 plus-sym))
(bnop mns-sym '(appl-rtn 710 mns-sym))    ;-- was 670.  caused bug 4-4+1=-1
(unop mns-sym '(list 'mk-unop '%- (parse-pop 760)))
(bnop mul-sym '(appl-rtn 750 mul-sym))
(bnop div-sym '(appl-rtn 730 div-sym))
(bnop colon '(mltyp-rtn))
;-- (unop cnr-sym '(cnr-rtn))      ;--  not used by prl.
(setf (get tml-sym langlp) 0)
(setf (get rparen langlp) 10)
(setf (get '|eqindec| langlp) 30)
(setf (get '|in| langlp) 60)
(setf (get '|and| langlp) 70)
(setf (get '|perinlam| langlp) 140)
(setf (get scolon langlp) 150)
(setf (get rbrkt langlp) 20)
(setf (get '|where| langlp) 150)
(setf (get '|whereref| langlp) 150)
(setf (get '|whererec| langlp) 150)
(setf (get '|wheretype| langlp) 150)
(setf (get '|whereabstype| langlp) 150)
(setf (get '|whereabsrectype| langlp) 150)
(setf (get '|perinvs| langlp) 220)
(setf (get trap-then-sym langlp) 250)
(setf (get trap-loop-sym langlp) 250)
(setf (get trapif-then-sym langlp) 260)
(setf (get trapif-loop-sym langlp) 260)
(setf (get trapbind-then-sym langlp) 260)
(setf (get trapbind-loop-sym langlp) 260)
(setf (get '|loop| langlp) 20)
(setf (get '|else| langlp) 20)
(setf (get '|then| langlp) 20)
(setf (get '|if| langlp) 310)
(setf (get asgn-sym langlp) 360)
(setf (get comma langlp) 400)
(setf (get else-sym langlp) 20)
(setf (get condl-sym langlp) 440)
(setf (get '|mlinfix| langlp) 450)
(setf (get '|or| langlp) 500)
(setf (get conj-sym langlp) 520)
(setf (get gt-sym langlp) 560)
(setf (get lt-sym langlp) 600)
(setf (get eq-sym langlp) 540)
(setf (get conc-sym langlp) 630)
(setf (get period langlp) 650)
(setf (get mns-sym langlp) 660)
(setf (get plus-sym langlp) 700)
(setf (get div-sym langlp) 720)
(setf (get mul-sym langlp) 740)
(setf (get colon langlp) 770)
(setf (get '|primary| langlp) 1010)

