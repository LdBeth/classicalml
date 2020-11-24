%-*- Tab-Width: 2 -*-%
%
********************************************************************************
********************************************************************************
********************************************************************************

   tactics-2

********************************************************************************
********************************************************************************
********************************************************************************
%







let ELastHyp p = E (number_of_hyps p) p ;;


  



letrec RepeatAndE i p =
  Try
  ( IfOnHyp (\x,A. x=`NIL` & is_and_term A) (E i) Fail i
    THEN
    Thinning [i]
    THEN
    RepeatAndE (number_of_hyps p + 1)
    THEN
    RepeatAndE (number_of_hyps p)
  )
  p
;;

let DeAnd =
  Repeat (OnEveryHyp (\i. IfThenOnHyp (\x,(). x=`NIL`) 
                            (Try (ComputeHyp i THEN Progress (RepeatAndE i)))
                            i))
;;

letrec RepeatOrE i p =
   Try
  ( IfOnHyp (is_union_term o snd) (E i) Fail i
    THEN
    Thinning [i]
    THEN
    OnLastHyp RepeatOrE
  )
  p
;;







let RepeatAndOrE i p =
  Repeat
    ( Progress
        ( ForEachHypFrom (\i. RepeatAndE i ORELSE RepeatOrE i) i))
    p
;;


let RepeatSetE i  =
  letrec Aux i =
    Try
    (ComputeHyp i 
     THEN IfOnHyp 
          (\x,H. is_set_term H)
          (\p. (E i THEN Aux (number_of_hyps p + 1)) p)
          (\p. fail)   
          i
    )   in
  Aux i
;;




let RepeatFunctionEFor n instantiation_list i =

  letrec Aux j n instantiation_list =
  
    if n < 1 then Idtac else

      Try

      (\ p .
        ( let (),A = destruct_hyp j p in
          let x,(),() = destruct_function A in
          if x=`NIL` then
            Refine (function_elim_independent j `NIL`)
            THEN
            (if i=j then Idtac else Thinning [j])
            THENL
            [Idtac
            ;(\p. Aux (number_of_hyps p) (n-1) instantiation_list p)
            ]
          else   
            let term . new_list = instantiation_list  in
            Refine (function_elim j term `NIL`)
            THEN
            (if i=j then Idtac else Thinning [j])
            THENL
            [Idtac
            ;\p. Aux (number_of_hyps p) (n-1) new_list p
            ]
        )
        p     
      )       in

   Aux i n instantiation_list

;;


let depending_hyp_nums p i =
  let possibly_depending_hyps = map destruct_declaration (nthcdr i (hyps p))  in
  letrec aux remaining_hyps next_hypno vars_so_far depending_hyp_nums_so_far =
    if null remaining_hyps then depending_hyp_nums_so_far
    else
      let (x,A).l = remaining_hyps in
      if null (intersection (free_vars A) vars_so_far) then 
        aux l (next_hypno+1) vars_so_far depending_hyp_nums_so_far
      else aux l (next_hypno + 1) (x=`NIL` => vars_so_far | (mvt x).vars_so_far) 
               (next_hypno . depending_hyp_nums_so_far) in
  aux possibly_depending_hyps (i+1) [mvt (id_of_hyp i p)] []
;;

let BringDependingHyps id p =
  BringHyps (depending_hyp_nums p (find_declaration id p)) p
;;



letrec BackchainWith Tactic =

  let AtomizeConcl =
    REPEAT (IfOnConcl (\c. is_function_term c or is_and_term c)
                      (I THENG OnLastHyp RepeatAndE)
                      Fail) in

  letrec Aux (history: (term#term) list) =
    let AuxAux = 
      ApplyToAHyp 
      (\i p. (let A = h i p and C = concl p in
              if member (C,A) history then Fail 
              else (BackThruHyp i ORELSE (SwapEquands THEN BackThruHyp i))
                   THENM Aux ((C,A) . history)
             ) p)  in
    Try Hypothesis THEN 
    (AuxAux ORELSE (Progress AtomizeConcl THENW AuxAux)
            ORELSE Tactic)  in

  OnEveryHyp RepeatAndE THEN Aux []
;;

let Backchain = BackchainWith Fail ;;

let Contradiction = 
  Assert make_void_term THENL
  [Try Backchain;OnLastHyp E]
;;




let Cases terms =

  Assert (make_disjunction terms)
  THENL [Idtac; OnLastHyp RepeatOrE]

;;




let ExposeArithableHyps p =

  letrec Aux i p =

    if i < 1 
    then Idtac p
    if is_and_term (type_of_hyp i p)
       & exists (\t. (is_int_term o snd o destruct_equal) t
                     or (is_int_term o snd o destruct_equal o destruct_not) t
                     or is_less_term t
                     or is_less_term (destruct_not t)
                     ?
                     false
                )
                (destruct_conjunction (type_of_hyp i p))
    then (RepeatAndE i THEN (Aux (i-1))) p
    else Aux (i-1) p      in

  Aux (number_of_hyps p) p

;;

% w.r.t.  %
let glb_of_var_in_ineq var ineq =
  ( % c < var %
    let c,y = destruct_less ineq in
    if not var = y then fail ;
    destruct_integer c + 1
  )
  ?
  ( % c < var + 1 %
    let c,d = destruct_less ineq in
    let y,one = destruct_addition d in
    if not var = y or not destruct_integer one = 1 then fail ;
    destruct_integer c
  )
  ?     
  ( % (var < c) -> void %
    let ineq' = destruct_not ineq  in
    let y,c = destruct_less ineq'  in
    if not var = y then fail ;
    destruct_integer c 
  )
;;

% Guess a greatest lower bound for a subtype of the integers.  (Wimpy) %
let glb_of_integer_subtype T =
  let x,A,B = destruct_set T  in
  glb_of_var_in_ineq (mvt x) (hd (destruct_conjunction B))
;;


%$%
let NonNegInd newid i =

  ComputeHypType i
  THEN
  (\ p .
    let n,H = destruct_hyp i p  in
    if n=`NIL` then failwith `hyp. to elim must have label` ;
    let n = mvt n and x,A,B = destruct_set H  in
    let P,no_P = snd (destruct_and B), false ? make_nil_term, true  in
    let lb = glb_of_integer_subtype H - 1 % strict lower bound for n % in
    if lb < -1 then failwith `smallest member must be non-neg.` ;

    let lemma = % all n:int. lb<n => [ ||P[n/x]|| ] => ,(concl p) %
      make_function_term (dv n)
        make_int_term
        ( make_implication
            ( [make_less_term (make_integer_term lb) n]
              @ (if no_P then [] else [make_ugly_squash_term (substitute P [mvt x, n])])
              @ [concl p]
            )
        )   in

    let SetE = E i  in

    let UseLemma p =
      let k = number_of_hyps p  in
      ( EOn n k
        THENS
        ( OnLastHyp E
          THENL
          [SetE THENW Arith
          ;if no_P then Hypothesis
          else OnLastHyp E
                THENL
                [ Refine (explicit_intro  make_axiom_term)
                  THEN SetE
                  THENW SetElementI
                ; Hypothesis
                ]
          ]
        )
      )
      p   in
    
    let ProveDownCase = I THENW Arith in
  
    let ProveZeroCase p = 
      if lb = -1 then 
        ( I 
          THENW ( Thinning [number_of_hyps p + 1]
                  THEN (if no_P then Idtac else I)
                )
        ) p
      else (I THENW Arith) p    in
  
    let ProveUpCase p =
      ( let base = make_integer_term (lb + 1)  in
        let k = number_of_hyps p in
        let n' = make_var_term (id_of_hyp (k-2) p) in
        if lb = -1 then
          I THENW (E k THENL [Arith; Thinning [k;k+1]])
        else 
          I
          THENW
          ( Cases [make_equal_term make_int_term [n';base]  
                  ;make_less_term base n']
            THENL
            [Arith
            ;Thinning [k-1;k;k+1] 
             THEN (if not no_P then I else Idtac)
            ;E k THENL [Arith; Thinning [k-1;k;k+1]
                                  THEN (if not no_P then I  else Idtac)]
            ]
          )
      ) p in
  
    ( Assert lemma
      THENL
      [I
      THENW ( OnLastHyp (\i. Refine (integer_elim i `NIL` newid))
              THEN Thinning [i; number_of_hyps p + 1]
              THENL [FastAp ProveDownCase; ProveZeroCase; ProveUpCase]
            )
      ;FastAp UseLemma
      ]
    ) p
    
  )
;;


   


   


%  Type of hyp i must be Int.
%
let NonNegIndUsing j newid i p =

( let T = concl p   in
  let n,H = destruct_hyp i p  in
  if n=`NIL` then failwith `hyp. to elim must have label` ;
  let n = mvt n and lb = j-1  % strict lower bound for n %  in
  if lb < -1 then failwith `smallest member must be non-neg.` ;

  let lemma = % all n:Int. lb<n => T  %
        make_function_term (dv n)
          make_int_term
          (make_implication [make_less_term (make_integer_term lb) n ; T ]) in

  let UseLemma p =
    let k = number_of_hyps p  in
    ( EOn n k THENS OnLastHyp E) p   in
  
  let ProveDownCase = I THENW Arith in

  let ProveZeroCase p = 
    if lb = -1 then (I THENW Thinning [number_of_hyps p + 1]) p
    else (I THENW Arith) p    in

  let ProveUpCase p =
    ( let base = make_integer_term (lb + 1)  in
      let k = number_of_hyps p in
      let n' = make_var_term (id_of_hyp (k-2) p) in
      if lb = -1 then E k THENL [Arith; Thinning [k]]
      else 
        I
        THENW
        ( Cases [make_equal_term make_int_term [n';base]  
                ;make_less_term base n']
          THENL
          [Arith
          ;Thinning [k-1;k;k+1] 
          ;E k THENL [Arith; Thinning [k-1;k;k+1]]
          ]
        )
    ) p in

  Assert lemma
  THENL
  [I THENW ( OnLastHyp (\i. Refine (integer_elim i `NIL` newid))
           THEN Thinning [i; number_of_hyps p + 1]
           THENL [FastAp ProveDownCase; ProveZeroCase; ProveUpCase]
         )
  ;FastAp UseLemma
  ]

) p

;;



   
%$%


   

