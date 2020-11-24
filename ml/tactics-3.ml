%-*- Tab-Width: 2 -*-%
%
********************************************************************************
********************************************************************************
********************************************************************************

   tactics-3

********************************************************************************
********************************************************************************
********************************************************************************
%

let SubstOver in_term ztok B p =
  let [b],A = destruct_equal in_term  in
  let a = lookup (match B (concl p) [ztok]) ztok  in
  Refine (substitution big_U (make_equal_term A [a;b]) ztok B) p
;;


let SubstFor equality_term p =
  let [a;()],() = destruct_equal equality_term  in
  let z = undeclared_id p `z`   in
  let B = replace_subterm a (mvt z) (concl p) in
  Refine (substitution big_U equality_term z B) p
;;


%$%
let UseHypEq term_modifier i p = 
  SubstFor (term_modifier (type_of_hyp i p)) p
;;
%$%


let ListUnrollNew h t i p =

( let type = type_of_hyp i p  in
  if not is_list_term (fast_ap compute type) then failwith
    `ListUnroll: hyp. must compute to a list type` ;
  let l = id_of_hyp i p and l' = undeclared_id p `l`  in
  let l_var, l'_var = mvt l, mvt l' in
  let seq_term = % all l':type. (l=l' in type) => T[l'/l] %
    make_function_term l' type
      (make_implies_term (make_equal_term type [l_var; l'_var])
                         (substitute (concl p) [l_var, l'_var]) ) in
  Assert seq_term
  THENL
  [ I
    THENL
    [ OnLastHyp ComputeHypType
      THEN OnLastHyp (\i. Refine (list_elim i `NIL` h t))
      THENL [I; OnLastHyp (\i. Thinning [i]) THEN I]
      THEN Thinning [number_of_hyps p + 1]
    ; Idtac
    ]
  ; FastAp ( OnLastHyp (RepeatFunctionEFor 2 [l_var]) THEN Trivial )
  ]
) p
;;


let ListUnroll i p =
  ListUnrollNew (undeclared_id p `h`) (undeclared_id p `t`) i p
;;

let UnrollNew ids i = 
  (\p. ListUnrollNew (first ids) (second ids) i p) 
  ORELSE RecUnrollNew ids i 
;;

let Unroll i = ListUnroll i ORELSE RecUnroll i ;;



let HypCharUsing characterization_lemma_name inst_list i p =
( let context,t =
    explode_function (main_goal_of_theorem characterization_lemma_name) in
  let a,b = destruct_iff t in
  let hyp = type_of_hyp i p in
  let new_hyp = 
    substitute_using_bindings b
      (match_in_context a hyp context p) 
    ? 
    substitute_using_bindings a
      (match_in_context b hyp context p) in
  Assert new_hyp THENL [Lemma characterization_lemma_name; Thin i]
) p
;; 

let HypChar name = HypCharUsing name [] ;; 

let match_and_replace pattern instance ids (actions: (tok#(term->term)) list) =
  substitute_using_bindings
    pattern
    (map (\id,t. id, (lookup actions id t ? t))
         (match pattern instance ids))
;; 
                                
let LemmaWithMatchHack name pattern ids actions =
  ReverseComputeConclUsing (\c. match_and_replace pattern c ids actions)
  THEN Lemma name
;; 





% Write the formula as:             
x1:A1 -> ... -> xn:An -> B                    
where B is not a function type, and some xi may be NIL.  Find, using
matching and extra_terms, a sequence of terms [a1;...;an], 
such that for each term t in terms there is some j, 1jn,
such that t  Aj[ai/xi,1i<j].  Return the subsequence corresponding 
to the non-NIL xi in [x1;...;xn].  The computation of the ai involves
first matching members of terms against Aj, then matching the types of
the resulting bindings against the appropriate Ak, then using extra_terms
to fill out the instantiation list.  Rather inefficient (somewhat exponential
in the number of terms).
%
let match_against_formula_hyps formula terms extra_terms typer =
  let context, B = explode_function formula in
  let context_with_leftward_ids = 
    accumulate_and_combine (\ids (x,A). x.ids) [] context  in
  let bindings_from_types match_bindings =
    iterate_fun append
      (map (\(x,A),ids.
              ( if exists (\v. member (dv v) ids & not is_bound (dv v) match_bindings)
                          (free_vars A)
                then match A (typer (lookup match_bindings x)) ids else fail
              ) ? []
           )
           context_with_leftward_ids
      )  in
  letrec bindings bindings_so_far remaining_patterns remaining_instances =
    if null remaining_instances then
      ( let l = union bindings_so_far
          (bindings_from_types bindings_so_far) in
        if not context_instantiated context l then fail else l
      )
    else 
      let u.itail = remaining_instances   in
      let ((x,A),ids).ptail = remaining_patterns  in
      ( bindings (combine_alists bindings_so_far (match A u ids))
                       context_with_leftward_ids itail
        ? bindings bindings_so_far ptail remaining_instances
      )   in
  let reorder_patterns %for efficiency% l =
    uncurry append (partition (\(x,A),ids. not is_var_term A) l) in
  let bindings = 
    bindings [] (reorder_patterns context_with_leftward_ids) terms in
  letref extra_terms = extra_terms  in
  let extra_term () = let x.y = extra_terms in (extra_terms:=y;x) in
  collect (\x,(). lookup bindings x ? extra_term ()) context
;;


% This tactic is intended to be only top level -- it is quite inefficient. %
let LemmaFromHyps name hypnos terms p =
( Refine (lemma name `nil`)
  THEN RepeatAtomicNotFunctionE 
        (match_against_formula_hyps 
            (main_goal_of_theorem name) 
            (map (\i. type_of_hyp i p) hypnos)
            terms
            (get_type p)
        )
        (number_of_hyps p + 1)
  THEN Thinning [(number_of_hyps p + 1)]
)  p
;;



let match_formula_hyps formula terms p =

  letrec aux ctxt_types ctxt_ids bindings fmla_tl terms_tl =
    if null terms_tl then
    ( let bindings' =
        extend_bindings_using_context 
          (rev (ctxt_ids com ctxt_types)) bindings p in
      map (lookup bindings') (rev ctxt_ids)
    )  
    if is_function_term fmla_tl & `NIL` = fst (destruct_function fmla_tl) then
    ( let (),A,B = destruct_function fmla_tl in
      aux ctxt_types ctxt_ids (match A (hd terms_tl) ctxt_ids @ bindings) 
          B (tl terms_tl)
      ? aux ctxt_types ctxt_ids bindings B terms_tl
    )
    if is_function_term fmla_tl then
    ( let x,A,B = destruct_function fmla_tl in
      let ctxt_types' = A . ctxt_types in
      let ctxt_ids' = x . ctxt_ids in
      aux ctxt_types' ctxt_ids'
          (match (assert (\t. not is_var_term t) A) (hd terms_tl) ctxt_ids 
           @ bindings) 
          B (tl terms_tl)
      ? aux ctxt_types' ctxt_ids' bindings B terms_tl
    )
    if is_and_term fmla_tl then
    ( let A,B = destruct_and fmla_tl in
      aux ctxt_types ctxt_ids bindings A terms_tl
      ? aux ctxt_types ctxt_ids bindings B terms_tl
    )
    else fail        in
  aux [] [] [] formula terms
;; 



% This tactic is intended to be only top level -- it is quite inefficient. %
let FLemmaUsing name assums p =
  let terms = 
    match_formula_hyps (main_goal_of_theorem name) assums p in
  let WithDischarge Aux terms assums fun_type =
    if null assums then Aux terms assums
    if hd assums = fst (snd (destruct_function fun_type)) then 
      Aux terms (tl assums) 
    else Aux terms assums in
  let Check assums = if null assums then Idtac else Fail in
  letrec Aux terms assums i p =
    Refine (hyp i) p
    ?
    let A = type_of_hyp i p in
    if is_not_term A then
    ( if null assums then Try (Complete (E i) THEN Thin i) p
      if null (tl assums) & hd assums = destruct_not A then 
        (E i THEN Thin i) p
      else fail
    )
    if is_function_term A & `NIL` = fst (destruct_function A) then
      Same 
      [E i THEN Thin i; 
       OnLastHyp (WithDischarge Aux terms assums A)
      ] p
    if is_function_term A & null terms then Check assums p
    if is_function_term A then
      Same 
      [EOn (hd terms) i THEN Thin i; 
       OnLastHyp (WithDischarge Aux (tl terms) assums A)
      ] p
    if is_and_term A  & null assums then RepeatAndE i p
    if is_and_term A then
    ( E i THEN Thin i 
      THEN ( OnLastHyp Thin THEN OnLastHyp (Aux terms assums)
             ORELSE (OnNthLastHyp 2 Thin THEN OnLastHyp (Aux terms assums))
           )
    ) p
    else Check assums p in
  ( Refine (lemma name `nil`)
    THEN OnLastHyp (Aux terms assums)
  ) p
;; 


let FLemma name hypnos p = 
  FLemmaUsing name (map (\i. type_of_hyp i p) hypnos) p
;; 




letrec UglyRepeatSetE i p =
  if is_set_term (fast_ap compute (type_of_hyp i p)) then
    (E i THENW UglyRepeatSetE (number_of_hyps p + 1)) p 
  else Idtac p 
;;




let ComputeSomeEquands nums p =
  let equands,T = destruct_equal (concl p)    in
  Refine
    (direct_computation
      (make_equal_term
        T
        (map (\t,n. if member n nums then make_tagged_term 0 t else t)
        (equands com (upto 1 (length equands))))))
  p
;;

let ComputeAnEquandFor n i p =
  let equands,T = destruct_equal (concl p)    in
  Refine
    (direct_computation
      (make_equal_term
        T
        (map (\t,j. if j=i then make_tagged_term n t else t)
        (equands com (upto 1 (length equands))))))
  p
;; 

let ReduceDecisionTerm equand_num case =

  ComputeSomeEquands [equand_num]
    THEN
    (\p.
      let t = select equand_num (fst (destruct_equal (concl p)))   in
      if is_int_eq_term t then Refine (int_eq_computation equand_num case) p
      if is_atom_eq_term t then Refine (atom_eq_computation equand_num case) p 
      if is_intless_term t then Refine (int_less_computation equand_num case) p
      else fail
    )
;;





% Will not always work, since try_to_replace_subterm doesn't. %
let AddDefInstancesToConcl instances p =
  ( letrec aux instances t =
      try_to_replace_subterm (aux (tl instances) t)
        (compute (hd instances))
        (hd instances)
      ? t     in
    Assert (aux instances (concl p))
    THENL [Idtac; OnLastHyp NormalizeHyp 
                  THEN NormalizeConcl 
                  THEN Hypothesis]
  ) p
;;


