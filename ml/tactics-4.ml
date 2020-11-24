%-*- Tab-Width: 2 -*-%
      
let InstantiateHyp term_list i p =
  
  if null term_list then Idtac p
  else
  ( letrec make_instance ids_so_far t =
      ( if is_not_term t then fail ;
        let x,A,B = destruct_function t in
        if x = `NIL` then make_instance ids_so_far B
        else make_instance (x.ids_so_far) B
      )
      ?
      substitute t 
        ((map (\x. make_var_term x)
        (rev ids_so_far)) com term_list)  in

    Assert (make_instance [] (compute (type_of_hyp i p)))
    THENL
    [ComputeHyp i THEN RepeatAtomicNotFunctionE term_list i
    ;Idtac
    ]
  ) p
;;


let ref t p = refine_using_prl_rule t p ;; 


let get_ids_equands_and_type t =
  letrec aux t ids_so_far =
    ( let x,(),B = destruct_function t  in
      aux B (if x=`NIL` then ids_so_far else x.ids_so_far)
    )
    ?
    rev ids_so_far, destruct_equal t  in
  aux t []
;;



let RewriteConclWithLemmaOver name over_id over_term p =
( let ids,[e;e'],T = get_ids_equands_and_type (main_goal_of_theorem name)  in
  let instance = lookup (match over_term  (concl p) [over_id]) over_id  in
  let instantiation_terms = 
    match_part_in_context first_equand (main_goal_of_theorem name) instance p []  in
  let subst_list = (map (\x. make_var_term x) ids com instantiation_terms)  in
  let replacement = substitute e' subst_list  in
  let type_inst = substitute T subst_list   in
  Refine (substitution big_U
            (make_equal_term type_inst [instance; replacement])
            over_id over_term 
         )
  THENL [Refine (lemma name `NIL`) 
         THEN (OnLastHyp (RepeatFunctionE instantiation_terms))
        ;Idtac
        ;Idtac
        ]
) p
;;


letrec get_contained_instance term pattern ids =
  substitute pattern (map (\x,t. make_var_term x, t) (match pattern term ids))
  ?
  letrec try_on_each_member l =
    get_contained_instance (hd l) pattern ids
    ?
    try_on_each_member (tl l)
    ?
    failwith `get_contained_instance`   in
  try_on_each_member (subterms term)
;;


let RewriteConclWithLemma name p =
  let ids,[e;e'],T = get_ids_equands_and_type (main_goal_of_theorem name)  in
  let over_id = undeclared_id p `z` in
  let over_term = replace_subterm
                    (get_contained_instance (concl p) e ids)
                    (make_var_term over_id)
                    (concl p)     in
  RewriteConclWithLemmaOver name over_id over_term p
;;

let second_equand t = let [u;u'],() = destruct_equal t in u' ;;


let RewriteConclWithRevLemmaOver name over_id over_term p =
( let ids,[e;e'],T = get_ids_equands_and_type (main_goal_of_theorem name)  in
  let instance = lookup (match over_term  (concl p) [over_id]) over_id  in
  let instantiation_terms = 
    match_part_in_context second_equand (main_goal_of_theorem name) instance p [] in
  let subst_list = (map (\x. make_var_term x) ids com instantiation_terms)  in
  let replacement = substitute e subst_list in
  let type_inst = substitute T subst_list   in
  Refine (substitution big_U
            (make_equal_term type_inst [instance; replacement])
            over_id over_term
         )
  THENL [Refine (lemma name `NIL`) 
         THEN (OnLastHyp (RepeatFunctionE instantiation_terms))
        ;Idtac
        ;Idtac
        ]
) p
;;

let RewriteConclWithRevLemma name p =
  let ids,[e;e'],T = get_ids_equands_and_type (main_goal_of_theorem name)  in
  let over_id = undeclared_id p `z` in
  let over_term = replace_subterm
                    (get_contained_instance (concl p) e' ids)
                    (make_var_term over_id)
                    (concl p)     in
  RewriteConclWithRevLemmaOver name over_id over_term p
;;













let RewriteHypWithLemmaOver name over_id over_term i p =
( let ids,[e;e'],T = get_ids_equands_and_type (main_goal_of_theorem name)  in
  let instance = lookup (match over_term  (type_of_hyp i p) [over_id]) over_id  in
  let instantiation_terms = map (lookup (match e instance ids)) ids   in
  let subst_list = (map (\x. make_var_term x) ids com instantiation_terms)  in
  let replacement = substitute e' subst_list  in
  let type_inst = substitute T subst_list   in
  Assert (substitute over_term [make_var_term over_id, replacement])
  THENL  [RewriteConclWithRevLemmaOver name over_id over_term
         ;Idtac
         ]
) p 

;;




let RewriteHypWithLemma name i p =
  let ids,[e;e'],T = get_ids_equands_and_type (main_goal_of_theorem name)  in
  let over_id = undeclared_id p `z` in
  let over_term = replace_subterm
                    (get_contained_instance (type_of_hyp i p) e ids)
                    (make_var_term over_id)
                    (type_of_hyp i p)     in
  RewriteHypWithLemmaOver name over_id over_term i p
;;




let big_U_term = make_universe_term big_U ;;

let tag_equands tags t =
  let equands,T = destruct_equal t  in
  make_equal_term T (map (\t,i. make_tagged_term i t) (equands com tags))
;;




% All argument lists must have the same length.
  >> B(a_bar)  BY MultiSubst z_bar B b_bar T_bar [z_bar means z1,...,zn]
    >> a1=b1 in T1
    ...
    >> an=bn in Tn
    >> B(b_bar)
    z1:T1,...,zn:Tn >> B in U17
%
let MultiSubst z_bar B b_bar T_bar p =

  let bindings = match B (concl p) z_bar  in
  let a_bar = map (lookup bindings) z_bar in
  let B_of_b_bar = substitute B (map mvt z_bar  com  b_bar) in

  ( SubstConcl B_of_b_bar
    THEN
    IfThenOnConcl (\c. not c = B_of_b_bar)
      ( % Prove B(a_bar) = B(b_bar) by asserting
          (\ z_bar. B(z_bar)) (a_bar) = (\ z_bar. B(z_bar)) (b_bar) %
        Assert 
          ( let f = make_lambdas z_bar B in
            make_equal_term big_U_term
             [iterate_fun make_apply_term (f.a_bar)
             ; iterate_fun make_apply_term (f.b_bar)
             ]
          )
        THENL
        [ % Prove assertion by introing using T_bar, leaving %
          %  the a_bar = b_bar equalities %
          RepeatApIUsing (implode_function (z_bar com T_bar) big_U_term)
        ; % Use assertion by computing it to B(a_bar) = B(b_bar) %
          OnLastHyp (ComputeHypUsing (let n = length z_bar in tag_equands [n;n]))
          THEN Refine equality
        ]
      )
  ) p
;;




let RewriteConclWithLemmasOver (name_and_over_id_list: (tok#tok) list) over_term p =
(  let over_ids = map snd name_and_over_id_list   in
   let over_vars = map mvt over_ids in
   let over_bindings = match over_term (concl p) over_ids   in
   let n=number_of_hyps p in
   let replacements_with_types, lemma_instantiators =
      split
         (map 
            (\name, over_id.
              let ids,[e;e'],T = 
                get_ids_equands_and_type (main_goal_of_theorem name)  in
              let instance = lookup over_bindings over_id  in
              let instantiation_terms = 
                map (lookup (match e instance ids)) ids      in
              let subst_list = 
                (map (\x. make_var_term x) ids) com instantiation_terms  in
              (substitute e' subst_list , substitute T subst_list)
              , InstantiateLemma name instantiation_terms
            )
            name_and_over_id_list
         )        in
   let replacements, types = split replacements_with_types  in
   Same lemma_instantiators
   THENS (MultiSubst over_ids over_term replacements types 
          THEN IfThenOnConcl (\c. can (match over_term c) over_ids) (ThinToEnd (n+1))
         )
)  p
;;



let RewriteConclWithLemmas names p =
   letrec aux remaining_names partial_over_term collected_names_and_ids =
      if null remaining_names then partial_over_term, collected_names_and_ids
      else 
      ( let over_id = undeclared_id p `z`   in
        let ids,[e;e'],T = 
          get_ids_equands_and_type (main_goal_of_theorem (hd names))  in
        let newer_over_term = 
          replace_subterm
            (get_contained_instance partial_over_term e ids)
            (make_var_term over_id)
            partial_over_term         in
        aux remaining_names newer_over_term 
          ((hd names, over_id).collected_names_and_ids)
      )
      ? aux (tl remaining_names) partial_over_term collected_names_and_ids     in
   let over_term, names_and_ids = aux names (concl p) []  in       
   RewriteConclWithLemmasOver names_and_ids over_term p
;;







let SubstForInHyp eq_term i p =
( let [e;e'],T = destruct_equal eq_term 
  and H = type_of_hyp i p   in
  let over_id = undeclared_id p `z`   in
  let over_term = replace_subterm e (make_var_term over_id) H in
  Assert (substitute over_term [make_var_term over_id, e'])
  THENL [Refine (substitution big_U (make_equal_term T [e';e])
                  over_id over_term
                )
        ;Idtac
        ]
) p
;;


let tag_member n t =
  let [t'],T = destruct_equal t in
  make_equal_term T [make_tagged_term n t']
;;


let ComputeConclMemberFor n =
  ComputeConclUsing (tag_member n)
;;

let ComputeHypMemberFor n =
  ComputeHypUsing (tag_member n)
;;

letrec NLambdaIsThen k T p =
  if k < 1 then T p
  else 
    let n = number_of_hyps p  in
    ( ComputeConclMemberFor 0
      THEN IfOnConcl (is_lambda_term o first_equand) EqI Fail
      THEN IfThen (\p. n + 1 = number_of_hyps p) (NLambdaIsThen (k-1) T)
    ) p
;;

let ReduceEquandicity p =
  let [t;t'],T = destruct_equal (concl p) in
  (Assert (make_equal_term T [t]) THENL [Idtac; Eq]) p
;; 


% Attempt to apply extensionality n times, proving that the function
in each case is in void->void via computation.  
%
letrec AddArgsThen n T p =     
  if n=0 then T p
  else
  ( ExtUsing (make_function_term `NIL` make_void_term make_void_term)
    THENL
    ( [AddArgsThen (n-1) T ; Idtac]
      @ replicate
          ( ComputeEquands 
            THEN IfThenOnConcl (\c. not (is_lambda_term (first_equand c))) Fail
          )
          ((length o equands o concl) p)
    )
  ) p
;;


% If the concl is of the form 'a in A' or 'a=b in A' where a,b are (the same) 
poly-defined terms, then use the named typing lemma to obtain subgoal 
equalities involving the def's arguments. 
%
let ApplyPolyMemberLemma lemma_name p =
( let [t],T = destruct_equal (concl p) in 
  let lemma_goal = main_goal_of_theorem lemma_name in
  let match_res = 
    match_part (get_type p) first_equand lemma_goal t []
    ? match_part (\t. fast_ap reduce (get_type p t))
        first_equand lemma_goal t [] in
  InstantiateLemma lemma_name match_res
  THENS (Refine equality ORELSE FastAp (OnLastHyp Inclusion))       
) p
;; 



let ApplyPolyMemberLemmaToEq lemma_name p =
( let [t;t'],T = destruct_equal (concl p) in 
  let lemma_goal = main_goal_of_theorem lemma_name in
  let match_res = 
    match_part (get_type p) first_equand lemma_goal t []
    ? match_part (\t. fast_ap reduce (get_type p t))
        first_equand lemma_goal t [] in
  let l, eq = explode_function lemma_goal in
  let ctxt,ants = 
    chop_list (find_position (find (\x,A. x=`NIL`) l) l - 1 ? length l) l in
  if exists ($= `NIL` o fst) ctxt or exists ($not o $= `NIL` o fst) ants then
    failwith `lemma must have form: All x1. ... All xn. B1=>...=>Bm=> a in A` ;
  let d.xs = decompose_ap (first_equand eq) in
  if not (is_term_of_theorem_term d & all is_var_term xs) then
    failwith `member in lemma must be a term_of applied to variables` ;
  if not null (intersection xs (free_vars (eq_type eq))) then
    failwith `lemma's equality type cannot depend on def args.` ;
  let implicit_vars_etc, explicit_vars_etc = 
    partition (\(x,A),t. not member (mvt x) xs) (ctxt com match_res) in
  let subs = map (\(x,A),t. mvt x,t) implicit_vars_etc in
  let inst t = substitute t subs in
  let explicit_ctxt = map (\(x,A),t. x, inst A) explicit_vars_etc in
  let set_part = 
    let x,A = last explicit_ctxt in 
    x, make_set_term x A (inst (make_conjunction (map snd ants)))
    ? x, A in
  let using = 
    implode_function (firstn (length explicit_ctxt -1)
                             explicit_ctxt @ [set_part]) 
                     T  in
  RepeatApIUsingThen using
    ( ReduceEquandicity THEN
      AddArgsThen (length explicit_ctxt)
        (OnLastHyp (\i. IfThenOnHyp (is_set_term o snd) (E i) i) 
         THEN ApplyPolyMemberLemma lemma_name)
    )
  THEN Try (IfThenOnConcl (is_set_term o eq_type) SetElementI)
) p 
;; 


% Most applications of this tactic will be to goals of the form
>> f(a1)...(an) in T, where f is an extraction with membership theorem
(whose name is f's with an extra underscore appended) of the form
>> all x1. ... all xn . f(x1)...(xn) in T'.  However, there are situations
where f will not have n arguments; in this case some obnoxious
backing up might have to be done in order to apply the membership theorem.
%
let PolyMember p =
  let n = number_of_hyps p  in
  let t = first_equand (concl p)  in
  let f.args = decompose_application t in
  let actual_arity = length args  in
  let lemma_name = (append_underscore o destruct_term_of_theorem) f  in
  let lemma_goal = main_goal_of_theorem lemma_name  in
  let def_arity = arity_of_poly_definition (destruct_term_of_theorem f) in
  let DoLemma = 
    ApplyPolyMemberLemma lemma_name 
    ORELSE ApplyPolyMemberLemmaToEq lemma_name in
  if actual_arity = def_arity then DoLemma p
  if actual_arity > def_arity then RepeatApIThen DoLemma p
  else AddArgsThen (def_arity-actual_arity) DoLemma p
;;




