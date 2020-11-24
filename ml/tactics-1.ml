%-*- Tab-Width: 2 -*-%
%
********************************************************************************
********************************************************************************
********************************************************************************

   tactics-1

********************************************************************************
********************************************************************************
********************************************************************************
%

let fst_ch tok = hd (explode tok) ;;

let WithoutDisplayMaintenance Tactic p =
  apply_without_display_maintenance Tactic p
;;

let Refine r p = refine r p ;;

let ReverseComputeConclUsing tagger p =
  Refine (reverse_direct_computation (tagger (concl p))) p
;;

let ReverseComputeHypUsing tagger i p =
  Refine (reverse_direct_computation_hyp i (tagger (type_of_hyp i p))) p
;;

let ApI t = Refine (function_equality_apply t) ;;

% replacement must head-normalize to t %
let ReplaceSubtermInConcl t replacement =
  ReverseComputeConclUsing
    (replace_subterm t (make_tagged_term 0 replacement))
;;

% replacement must head-normalize to t %
let ReplaceSubtermInHyp t replacement =
  ReverseComputeHypUsing
    (replace_subterm t (make_tagged_term 0 replacement))
;;

let FastAp = WithoutDisplayMaintenance ;;

let Arith = Refine (arith big_U) ;;

let Thinning l p = Refine (thinning l) p ;;

let ThinIf (P: int->tok->term->bool) p =
  let P' (x,y,z) = P x y z in
  Thinning 
    (map fst (filter P' (upto 1 (number_of_hyps p)
                          com map destruct_declaration (hyps p))))
    p
;;

let SavingOnlyDecls T p =
  let n = number_of_hyps p in
  (T THEN ThinIf (\i x A. i>n & x=`NIL`)) p
;;

let Frontier = frontier ;;

let Hypothesis p =  hypothesis p ;;

let Immediate p  = immediate p ;;

let Try p = TRY p ;;

let Seq term_list = 
    Refine (seq term_list (replicate `NIL` (length term_list)))
;;

let Assert t = Seq [t] ;;

let Idtac p = IDTAC p ;;

let Complete = COMPLETE ;; 

let Id = Idtac ;;

let Progress = PROGRESS ;;

let Fail: tactic = \p. fail ;;

let Trivial = Hypothesis ORELSE (Refine equality) ;;

% The objects referring to the eval rules and extensionality require
  doug's patches.
%

let Thin i = Thinning [i] ;;

let MoveToEnd i p = 
  (Assert (type_of_hyp i p) THENL [Trivial; Thin i]) p
;;


let ExplicitI t = Refine (explicit_intro t) ;;                             


% The last hyp. is the 1th last. %
let OnNthLastHyp n T p = T (number_of_hyps p - (n-1)) p ;;



lettype bogus_type = (void#void#void+void)->void ;;
lettype tactical = bogus_type;;

let First (TL: tactic list) :tactic = first_fun TL ;;





ml_curried_infix `THENTRYL` ;; 

let $THENTRYL (tac1:tactic) (tac2l:tactic list) (g:proof) =
   let gl,p = tac1 g  in
   (  let gll,pl = split(map (\(tac2,g). tac2 g) tac2gl)
                  where tac2gl = combine(tac2l,gl) in
      flat gll  ,  (p o mapshape(map length gll)pl)
   )
   ? gl, p
;;





ml_curried_infix `THENO` ;;   

let $THENO T T' p =
  let c = concl p in
  (T THEN (\p. if concl p = c then Idtac p else T' p)) p
;;  

letrec map_on_nth n f l =
  if n=1 then f (hd l) . tl l
  else hd l . map_on_nth (n-1) f (tl l)
;;


ml_curried_infix `THENS` ;;


let $THENS T T' p = 
  (T THEN (\p'. if concl p' = concl p then T' p' else Idtac p')) p
;;

%$%
ml_curried_infix `THENG` ;;

% Apply the second tactic to subgoals having a greater number
of hypotheses.
%
let $THENG T T' p = 
  (T THEN (\p'. if number_of_hyps p' > number_of_hyps p then T' p' else Idtac p')) p
;;
%$%
ml_curried_infix `THENM` ;;

let $THENM T T' = 
  T THEN (\p. if not is_membership_goal p then T' p else Idtac p)
;;


ml_curried_infix `THENW` ;;

let $THENW T T' =           
  T THEN (\p. if not is_wf_goal p then T' p else Idtac p)
;;


letrec Repeat T p = REPEAT T p ;;


letrec RepeatM T p = 
  Try (T THENM RepeatM T) p
;;

letrec RepeatO T p = 
  Try (T THENO RepeatO T) p
;;

letrec RepeatS T p = 
  Try (T THENS RepeatS T) p
;;


letrec RepeatW T p = 
  Try (T THENW RepeatW T) p
;;


let OnLastHyp (T: int->tactic) p = T (number_of_hyps p) p ;;


let ApplyToAHyp (T: int->tactic) p =
  letrec Aux i p = 
    if i=0 then failwith `ApplyToAHyp`
    else (T i ORELSE Aux (i-1)) p in
  Aux (length (hyps p)) p
;;



let If (predicate: proof -> bool) (T1: tactic) (T2: tactic) p =
  if predicate p then T1 p else T2 p
;;

let IfOnConcl (concl_predicate: term -> bool) (T1: tactic) (T2: tactic) p =
  if concl_predicate (concl p) then T1 p else T2 p
;;

let IfOnHyp (hyp_predicate: tok#term -> bool) (T1: tactic) (T2: tactic) i p =
  if hyp_predicate (destruct_declaration
            (select i (hyps p)))
        then T1 p
  else T2 p
;;


let IfThen predicate (T: tactic) =
  If predicate T Idtac
;;

let IfThenOnConcl concl_predicate (T: tactic) =
  IfOnConcl concl_predicate T Idtac
;;

let IfThenOnHyp hyp_predicate (T: tactic) i =
  IfOnHyp hyp_predicate T Idtac i 
;;


letrec RepeatUntil halting_predicate Tactic p =
   Repeat (IfThen (\p. not halting_predicate p) Tactic) p
;;



let ForEachHypInRange T i j p =

  letrec Aux j p = if j < i then Idtac p else (T j THEN Aux (j-1)) p  in
  Aux j p
;;



let ForEachHypFrom T i p = ForEachHypInRange T i (number_of_hyps p) p ;;

let ForEachHyp T = ForEachHypFrom T 1 ;;



let Same T_list p =

  let c = concl p   in

  letrec Aux T_list p =
    ( if not null T_list & concl p = c 
      then (hd T_list THEN Aux (tl T_list)) p
      else Idtac p
    )           in

  Aux T_list p
;;


let SameModP (P: proof->proof->bool) T_list =
  letrec Aux T_list p =
    ( if not null T_list
      then hd T_list THEN IfThen (P p) (Aux (tl T_list))
      else Idtac 
    ) p          in
  Aux T_list
;;

let SameModI (I:proof->*) T_list =
  SameModP (\p p'. I p = I p' ? false) T_list
;;

let RepeatHypTactic T hyps =
  Same (map T (rev hyps))
;;

let OnHyps = RepeatHypTactic ;; 

let Some Tactics p =
  letrec Aux Ts p = 
    (hd Ts ORELSE Aux (tl Ts)) p    in
  Aux Tactics p ? failwith `Some`
;;


let Every Tactics p =
  letrec Aux Ts p =
    if null Ts then Idtac p
    else (hd Ts THEN Aux (tl Ts)) p    in
  Aux Tactics p ?\id failwith `Every: `^id
;;

let OnEveryHyp T p =                                                           
  Same                                                              
    (map T (rev (upto 1 (number_of_hyps p))))                                  
    p                                                                          
;;                                                                             

let TryEverywhere Hyptac ConclTac =
  Try ConclTac THEN OnEveryHyp (\i. Try (Hyptac i))
;;

let EvalConclExcept thm_names = Refine (eval true thm_names) ;;

let EvalConclOnly thm_names = Refine (eval false thm_names);;

let EvalHypExcept thm_names i = Refine (eval_hyp i true thm_names) ;;

let EvalHypOnly thm_names i = Refine (eval_hyp i false thm_names);;

let EvalConcl = EvalConclExcept [] ;;

let EvalHyp = EvalHypExcept [] ;;

let Eval = TryEverywhere EvalHyp EvalConcl ;;

let EvalExcept thm_names = 
  TryEverywhere (EvalHypExcept thm_names) (EvalConclExcept thm_names)
;;

let EvalOnly thm_names = 
  TryEverywhere (EvalHypOnly thm_names) (EvalConclOnly thm_names)
;;


let SwapEquandsInConcl p =

( let [t;t'],T = destruct_equal (concl p)   in
  Assert (make_equal_term T [t';t])
  THENL [Idtac; Refine equality]
) p
?  failwith `SwapEquandsInConcl`
;;

let SwapEquands = SwapEquandsInConcl ;;

let SwapEquandsInHyp i p =
( let [t;t'],T = destruct_equal (type_of_hyp i p) in
  Assert (make_equal_term T [t';t])
  THENL [Refine equality; Thinning [i]]
) p
?  failwith `SwapEquandsInHyp`
;;


let ComputeConclUsing tagger p =
   Refine (direct_computation (tagger (concl p))) p
;;


let ComputeHypUsing tagger i p =
   Refine (direct_computation_hyp
      i
      (tagger (type_of_hyp i p)))
          p
;;

let RedefConcl = ComputeConclUsing add_defs ;;

let RedefHyp = ComputeHypUsing add_defs ;;

let Redef = OnEveryHyp RedefHyp THEN RedefConcl ;;


let tag_all_equands n equality_term =
  let l,T = destruct_equal equality_term in
  make_equal_term T (map (make_tagged_term n) l)            
;;


let ComputeEquandsFor n =
  ComputeConclUsing (tag_all_equands n)
;;                                                                             

let ComputeHypEquandsFor n = 
  ComputeHypUsing (tag_all_equands n)
;;

let ComputeEquands = ComputeEquandsFor 0 ;;

let ComputeHypEquands = ComputeHypEquandsFor 0 ;;


let unroll_rec_using rec_type another_version =
  let T,C = destruct_simple_rec rec_type in
  substitute C [mvt T, another_version]
;;

let UncomputeMember uncomputed_member p =
( Assert (make_equal_term (concl_type p) [uncomputed_member]) 
  THENL [Idtac; (FastAp o OnLastHyp) ComputeHypEquands THEN Trivial]
) p
;;



% Not too efficient.  Also, applications of the U function are not
tagged, as their normalization takes too much time.
%
let tag_all_legal_subterms t =
   letrec tag_everything t =
  if is_indexed_universe_term t then t
  if is_noncanonical_term t or is_term_of_theorem_term t then
    make_tagged_term 0 (map_on_subterms tag_everything t)  
  else  map_on_subterms tag_everything t  in
   remove_illegal_tags (tag_everything t)
;;





let ComputeConcl p =
  ( let t = concl p  in
    if is_canonical_type t or is_var_term t then
    Idtac 
    else
    ComputeConclUsing (make_tagged_term 0)
  )

  p

;;




let ComputeConclType p =

( let t = concl_type p  in
    if is_canonical_type t or is_var_term t then
    Idtac 
    else
      ComputeConclUsing (map_on_equality_type (make_tagged_term 0))
    ORELSE
    ComputeConclUsing (make_tagged_term 0)
)

p

;;



let ComputeConclTypeFor i p =

( let t = concl_type p  in
  if is_canonical_type t or is_var_term t then
    Idtac
  else
    ComputeConclUsing (map_on_equality_type (make_tagged_term i))
    ORELSE
    ComputeConclUsing (make_tagged_term i)
)

p 

;;


let ComputeHyp i p =
  let t = type_of_hyp i p   in
    if is_canonical_type t or is_var_term t then
    Idtac p
  else ComputeHypUsing (make_tagged_term 0)i p
;;



let ComputeHypType i p =
( let (),H = destruct_hyp i p in
  let hyp_type = hyp_type i p in
  if is_canonical_type hyp_type or is_var_term hyp_type then
    Idtac
  else
      ComputeHypUsing (map_on_equality_type (make_tagged_term 0)) i
    ORELSE
    ComputeHypUsing (make_tagged_term 0) i
)
p
;;

let CC = ComputeConcl ;;
let CH = ComputeHyp ;; 

let CCThen T = CC THEN T ;;
let CHThen T i = CH i THEN T i ;;


let ComputeHypTypeFor n i p =
( let (),H = destruct_hyp i p in
  let hyp_type = hyp_type i p in
  if is_canonical_type hyp_type or is_var_term hyp_type then
    Idtac
  else
      ComputeHypUsing (map_on_equality_type (make_tagged_term 0)) i
    ORELSE
    ComputeHypUsing (make_tagged_term n) i
)
p
;;




let ExpandDefsInConcl name_list =
  ComputeConclUsing (tag_named_defined_terms name_list)
;;

let ExpandDefsInHyp name_list  =
  ComputeHypUsing (tag_named_defined_terms name_list) 
;;

let ExpandDefsInHyps name_list hyp_list =
  iterate_fun 
    (\T T'. T THEN T') 
    (map (ExpandDefsInHyp name_list) hyp_list) 
;;


let ExpandDefs name_list =
  ExpandDefsInConcl name_list
  THEN
  ForEachHyp (ExpandDefsInHyp name_list)
;;


letrec NormalizeConcl p =
( let c = concl p   in
    ComputeConclUsing tag_all_legal_subterms 
  THEN
  Try (\p. if c = concl p then fail else NormalizeConcl p)
) p
;;


letrec NormalizeHyp i p =
( let h = type_of_hyp i p   in
    ComputeHypUsing tag_all_legal_subterms i
  THEN
  Try (\p. if h = type_of_hyp i p then fail else NormalizeHyp i p)
) p
;;



let NormalizeHyps hyp_list =
  iterate_fun 
    (\T T'. T THEN T') 
    (map NormalizeHyp hyp_list) 

;;

let Normalize =
  NormalizeConcl
  THEN
  ForEachHyp NormalizeHyp 
;;
  

let TopLevelComputeConcl =
  ComputeConclUsing tag_for_top_level_compute
;;

let TopLevelComputeHyp =
  ComputeHypUsing tag_for_top_level_compute
;;

let TopLevelComputeHyps hyp_list =
  iterate_fun 
    (\T T'. T THEN T') 
    (map TopLevelComputeHyp hyp_list) 

;;

let TopLevelCompute =
  TopLevelComputeConcl
  THEN
  ForEachHyp TopLevelComputeHyp 
;;



%  "Abs" as a prefix below indicates that the computations stop
   short of substituting extracted terms for term_of terms.
%



let AbsSweepReduceConcl =
  ComputeConclUsing tag_for_abs_sweep_reduce
;;

let AbsSweepReduceHyp =
  ComputeHypUsing tag_for_abs_sweep_reduce
;;

let AbsSweepReduceHyps hyp_list =
  iterate_fun 
    (\T T'. T THEN T') 
    (map AbsSweepReduceHyp hyp_list) 
;;

let AbsSweepReduce =
  AbsSweepReduceConcl
  THEN
  ForEachHyp AbsSweepReduceHyp 
;;




letrec NormalizeEquands p =
( let c = concl p   in
    ComputeConclUsing
      (\t. let eqs,T = destruct_equal t in
          make_equal_term T (map (\x. tag_all_legal_subterms x) eqs))
  THEN
  Try (\p. if c = concl p then fail else NormalizeConcl p)
) p
;;



let tag_redices t =
  letrec aux t =
    if is_redex t then make_tagged_term 1 (map_on_subterms aux t)
    else map_on_subterms aux t    in
  let t' = aux t  in
  if t=t' then failwith `tag_redices`
  else remove_illegal_tags t'
;;

let ComputeConclRedices =
  ComputeConclUsing tag_redices
;;



let ReduceConcl =
  Repeat (ComputeConclUsing tag_redices)
;;

let ReduceHyp i =
  Repeat (ComputeHypUsing tag_redices i)
;;

let ReduceHyps hyp_list =
  iterate_fun 
    (\T T'. T THEN T') 
    (map ReduceHyp hyp_list) 
;;

let Reduce =
  ReduceConcl
  THEN
  ForEachHyp ReduceHyp 
;;

let has_two_principal_arguments t =
  member_of_tok_list (term_kind t)
    [`ATOMEQ`; `INTEQ`; `INTLESS` ; `MINUS`; `ADDITION`;
     `SUBTRACTION`; `MULTIPLICATION`; `DIVISION`; `MODULO`]
;;


letrec is_head_redex t =
  if not is_noncanonical_term t then false
  if is_redex t then true
  if has_two_principal_arguments t then
    (let a.b.t = subterms t in is_head_redex a or is_head_redex b)
  else is_head_redex (hd (subterms t))
;;

let tag_head_redex t =
  if is_head_redex t then make_tagged_term 1 t
  else failwith `tag_head_redex`
;;

let HeadReduceConcl =
  Repeat (ComputeConclUsing tag_head_redex)
;;

let HeadReduceHyp i =
  Repeat (ComputeHypUsing tag_head_redex i)
;;

let HeadReduceHyps hyp_list =
  iterate_fun 
    (\T T'. T THEN T') 
    (map HeadReduceHyp hyp_list) 
;;

let HeadReduce =
  HeadReduceConcl
  THEN
  ForEachHyp HeadReduceHyp 
;;



let find2 (R: *->**->bool) (l: * list) (l': ** list) : *#** =
  letrec aux l =
    hd l, find (R (hd l)) l'  ?   aux (tl l)  in
  aux l
;;

let same_def t t' =
  let f.args = decompose_ap t and f'.args' = decompose_ap t'  in
  is_term_of_theorem_term f & f=f' & length args = length args'
;;

% 0 means 0 steps (not ) %
letrec topmost_tags_toward_equality t t' : int#int =
  let l,l' = def_stepped_comp_seq t, def_stepped_comp_seq t'  in
  let ((),n),((),n') = 
    find2 (\(t,()) (t',()). 
            same_def t t' 
            or not is_apply_term t & term_kind t = term_kind t'
          )
          l l'  in
  n,n'
;;


let head_normal_mod_defs t = 
  0 = snd (fast_ap no_extraction_compute t)
;;

let tag_if_pos n t = 
  if n>0 then make_tagged_term n t else t
;;

% fails if found to be not {provably equal by computation}, or
if nothing is tagged.  No subterm of a term with
a tag is itself tagged.
%
let tag_toward_equality t t' =
  letref something_tagged = false in
  letrec aux t t' =
    if t = t' then t,t'
    if same_def t t' then 
      map2_on_def_subterms aux t t' 
    if both head_normal_mod_defs t t' & term_kind t = term_kind t' then 
      map2_on_subterms aux t t' 
    else
      let n,n' = topmost_tags_toward_equality t t' in
      something_tagged := n>0 or n'>0 ;
      tag_if_pos n t, tag_if_pos n' t' in
  assert (\(). something_tagged) (aux t t') 
;;


% all occurrences of the subterm specified by a destructor are replaced %
let tag_subterms_toward_equality destructor t destructor' t'  =
  let u,u' = destructor t, destructor' t' in
  let v,v' = tag_toward_equality u u' in
  replace_subterm u v t, replace_subterm u' v' t'
;;


let HypModCompUsing hyp_destructor concl_destructor i =
  (Repeat o FastAp)
  (\p.
    let t,t' = tag_subterms_toward_equality 
                hyp_destructor (type_of_hyp i p) concl_destructor (concl p) in
    ( Refine (direct_computation_hyp i t)
      THEN Refine (direct_computation t')
      THEN Try Trivial
    ) p
  )
;;

let id = \x.x ;;

let HypModComp = HypModCompUsing id id ;;

let tag_using (f: term->int) t =
  letrec aux t = 
    let t' = map_on_subterms aux t in make_tagged_term (f t') t' ? t' in
  assert (\t'. not t=t') (aux t)
;;

% tag only if t is a universe term or an equality with type a universe term %
let tag_constant_indexed_universes t = 
  tag_using ((\t.0) o assert is_constant_indexed_universe_term) t
;;


let ComputeUniverses =
  FastAp
  ( OnEveryHyp (\i. Try (ComputeHypUsing tag_constant_indexed_universes i))
    THEN Try (ComputeConclUsing tag_constant_indexed_universes)
  )
;;

let ComputeHypUniverses i =
  (FastAp o Try) (ComputeHypUsing tag_constant_indexed_universes i)
;;

let ComputeConclUniverses =
  (FastAp o Try) (ComputeConclUsing tag_constant_indexed_universes)
;;



let ILeft =
  ComputeConcl
  THEN
  (Refine (union_intro_left big_U))

;;

let IRight =
  ComputeConcl
  THEN
  (Refine (union_intro_right big_U))
;;




let ITerm term =

   ComputeConcl

   THEN

   ( Refine (product_intro_dependent term big_U `nil`)
     ORELSE
     (\ p .  Refine 
              (product_intro_dependent
                term
                big_U
                (undeclared_id_using p (fst (destruct_product (concl p))))
              ) p
     )
     ORELSE
     Refine set_intro_independent 
     ORELSE
     (\ p .  Refine 
               (set_intro
                  big_U
                  term
                  (undeclared_id_using p (fst (destruct_set (concl p))))
               ) p
     )
   )
;;


letrec ITerms terms =
  ITerm (hd terms) 
   THEN 
    (\p.ITerms (tl terms) p
     ?
     Idtac p
    )
;;



let RecI p =
( let A = concl p in
  if is_simple_rec_term A then Refine (simple_rec_intro big_U)
  else 
    ComputeConcl THEN
    (\p. (Refine (simple_rec_intro big_U)
          THEN ReplaceSubtermInConcl (concl p) A
         )p   
    )
) p
;;



%$%

let ReclessI =

   ComputeConcl

   THEN

   (\ p .

        let T = concl p  in

        if is_atom_term T then
           Refine (atom_intro (make_token_term `foo`)) p
      
        if is_universe_term T then
           Refine universe_intro_void p
      
        if is_int_term T then
           Refine (integer_intro_integer 0) p
      
        if is_list_term T then
           Refine (list_intro_nil big_U) p
      
        if is_union_term T then
           fail

        if is_true_term T then Refine integer_equality_natural_number p
      
        if is_function_term T then
           (  Refine (function_intro big_U `nil`) 
              ORELSE
              Refine (function_intro
                         big_U
                         (undeclared_id_using p (fst (destruct_function T))))
           ) p
         
        if is_product_term T & (`NIL` = (fst (destruct_product T))) then
           (  Seq (let (),A,B = destruct_product T in [A;B])
              THENL [Idtac; Idtac; Refine product_intro THENL
                                   [OnNthLastHyp 2 (\i. Refine (hyp i));
																		OnLastHyp (\i. Refine (hyp i))]]
                                    
           )  p
           
        if is_quotient_term T then
           Refine (quotient_intro big_U) p
      
        if is_set_term T then
           Refine set_intro_independent p
      
        if is_simple_rec_term T then
           failwith `rec`
      
        else failwith `I: no intro rule applies.`
   )

;;


let I p = ReclessI p  ??  [`rec`] RecI p 

;;


let AndI p = 
  if `NIL` = (fst o destruct_product o concl) p then Refine product_intro p 
  else fail 
;;

%$%




let EOn term i =
    ComputeHypType i
    THEN
    (\ p .
      let x,() = destruct_hyp i p  in
      if x = `NIL` then Refine (function_elim i term `NIL`) p
      else Refine (function_elim i term (undeclared_id p `y`)) p
    )
;;


let ExtNew id p = 
( ComputeConclType THEN
  Refine (extensionality
            big_U
            (map
                (compute o get_type p)
                ( (fst o destruct_equal o concl) p ))
            id
         )
) p
;;

let Ext p = ExtNew (undeclared_id p `x`) p  ;;

let ExtUsing t p = 
( ComputeConclType 
  THEN Refine (extensionality
                big_U 
                (map (\x.t) ((fst o destruct_equal o concl) p))
                (undeclared_id p `x`)
              )
) p
;;


let RecUnrollNew ids i p =
( let x,A = destruct_hyp i p in
  if is_simple_rec_term A then Refine (simple_rec_unroll_elim i ids)
  if x=`NIL` then
    ComputeHyp i THEN 
    (\p.
    ( let rec = type_of_hyp i p in
      Refine (simple_rec_unroll_elim i [])
      THEN OnLastHyp (ReplaceSubtermInHyp rec A)
      THEN Thin i
    ) p
    )
  else 
    ComputeHyp i THEN 
    (\p.
    ( let rec = type_of_hyp i p in
      Refine (simple_rec_unroll_elim i ids)
      THEN OnLastHyp (ReplaceSubtermInHyp rec A)
      THEN OnNthLastHyp 2 (ReplaceSubtermInHyp rec A)
      THEN ReplaceSubtermInHyp rec A i
    ) p
    )
) p
;;


let undeclared_id_from_hyp p i = 
  undeclared_id_using p (id_of_hyp i p)
;;

let RecUnroll i p =
  RecUnrollNew [undeclared_id_from_hyp p i] i p
;;



let RepeatFunctionE instantiation_list i =

  letrec Aux j instantiation_list =
  
    Try Hypothesis

    THEN

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
            ;(\p. Aux (number_of_hyps p) instantiation_list p)
            ]
          else
            let term . new_list = instantiation_list  in
            Refine (function_elim j term `NIL`)
            THEN
            (if i=j then Idtac else Thinning [j])
            THENL
            [Idtac
            ;\p. Aux (number_of_hyps p) new_list p
            ]
        )
        p     
      )       in

   Aux i instantiation_list

;;


let RepeatAtomicNotFunctionE instantiation_list i =

  letrec Aux j instantiation_list =
  
    Try

      (\ p .
        ( let (),A = destruct_hyp j p in
          if is_not_term A then fail ; 
          let x,(),() = destruct_function A in
          if x=`NIL` then
            Refine (function_elim_independent j `NIL`)
            THEN
            (if i=j then Idtac else Thinning [j])
            THENL
            [Idtac
            ;(\p. Aux (number_of_hyps p) instantiation_list p)
            ]
          else
            let term . new_list = instantiation_list  in
            Refine (function_elim j term `NIL`)
            THEN
            (if i=j then Idtac else Thinning [j])
            THENL
            [Idtac
            ;\p. Aux (number_of_hyps p) new_list p
            ]
        )
        p     
      )       in

   Aux i instantiation_list

;;

let SetElementI p =
  ( ComputeConclType 
    THEN
    ( Refine (set_equality_element big_U `NIL`)
      ORELSE
      Refine (set_equality_element big_U (undeclared_id p `x`))
    )
  ) p
;;


let SquashI p =
( Refine (explicit_intro make_axiom_term)
  THEN
  SetElementI
  THEN (FastAp o Try o Complete) 
       (Refine axiom_equality_equal 
        THEN Refine integer_equality_natural_number)
) p
;;  




let is_hidden p hyp = member hyp (hidden p) ;;

let BringHyps hyp_nums p =
  let numbered_hyps =
    collect
      (\i,decl. if not member i hyp_nums then fail else i, destruct_declaration decl)
      (upto 1 (length (hyps p)) com (hyps p)) in
  let seq_term =
    implode_function
      (map
        (\i,x,A. x, (is_hidden p i => make_squash_term A | A))
        numbered_hyps
      )
      (concl p) in
  let Eliminator =
    OnLastHyp (RepeatFunctionE
                (collect (\(),x,(). if x=`NIL` then fail else mvt x)  numbered_hyps))
    THEN (Trivial ORELSE (SquashI THEN Trivial)) in
  (Assert seq_term THENL [Idtac; Eliminator]) p
;;

let BringHyp i = BringHyps [i] ;; 

let RecInductionNew ids i p =
( let A = type_of_hyp i p  and  n = number_of_hyps p in
  let ind_hyps = [n+1;n+2;n+3] in
  let ids = if `NIL`= id_of_hyp i p then firstn 2 ids else ids
            ? failwith `RecInductionNew: need at least 2 new ids` in
  if is_simple_rec_term A then Refine (simple_rec_elim i (guess_U A p) ids)
  else
    ComputeHyp i
    THEN Refine (simple_rec_elim i (guess_U A p) ids)
    THENL [\p. Every (map (ReplaceSubtermInHyp (type_of_hyp i p) A)
                         (i.ind_hyps))
                     p
          ;\p. ReplaceSubtermInConcl (type_of_hyp i p) A p
          ]
) p
;;


let RecInduction i p =
  RecInductionNew (map (undeclared_id p) [`P`;`x`;`h`;`z`]) i p
;;




let ReclessE i =

  (ComputeHypType i)  
  
  THEN

  (\ p .

      let x, T = destruct_hyp i p  in

      if is_void_term T then
         Refine (void_elim i) p

      if is_int_term T then
        (let new_a = undeclared_id p `a` in
         Refine (integer_elim i `NIL` `NIL`) 
         ORELSE
         Refine (integer_elim i `NIL` (undeclared_id p `n`)) 
        ) p

      if is_list_term T then
        (let new_a = undeclared_id p `a` and new_h = undeclared_id p `h` in
         Refine (list_elim i `NIL` new_h `NIL`)
         ORELSE
         Refine (list_elim i `NIL` new_h (undeclared_id p `t`)) 
        ) p

      if is_union_term T then
        if x=`NIL` then Refine (union_elim i `NIL` `NIL`) p
        else Refine (union_elim i (undeclared_id p `a`) (undeclared_id p `b`)) p

      if is_function_term T then
         Refine (function_elim_independent i
                    (if x=`NIL` then `NIL` else undeclared_id p `b`)) 
                p

      if is_product_term T then
         if x=`NIL` then
            ( (Refine (product_elim i `NIL` `NIL`))
              ORELSE
              (Refine (product_elim i (undeclared_id p `a`) `NIL`))
            ) p
        else Refine (product_elim i (undeclared_id p `a`) (undeclared_id p `a`)) p

      if is_quotient_term T then
         Refine (quotient_elim i big_U (undeclared_id p `u`) (undeclared_id p `u`)) p

      if is_set_term T then
        IfOnHyp (\x,H. if not is_set_term H then failwith `SetE`; x=`NIL`)
          (Refine (set_elim i 1 `NIL`) THEN Thinning [i])
          (Refine (set_elim i 1 `NIL`)
           ORELSE \p. Refine (set_elim i 1 (undeclared_id p `z`)) p)
          i p

      if is_simple_rec_term T then failwith `rec`

      else  fail

  )

;;

let E i p = ReclessE i p ?? [`rec`] RecInduction i p ;; 

%let RecInduction i =
  ComputeHyp i
  THEN
  (\p. 
    let P = undeclared_id p `P` in
    let level = destruct_universe (get_type p (type_of_hyp i p)) ? big_U - 1  in
    if id_of_hyp i p = `NIL` then
      Refine (simple_rec_elim i level [P; undeclared_id p `x`; `NIL`; `NIL`]) p
    else
      Refine (simple_rec_elim i level
              [P; undeclared_id p `x`; undeclared_id p `h`; undeclared_id p `z`])
              p
  )
;;%


let SetE i =
  ComputeHyp i
  THEN
    IfOnHyp (\x,H. if not is_set_term H then failwith `SetE`; x=`NIL`)
    (Refine (set_elim i 1 `NIL`) THEN Thinning [i])
    (Refine (set_elim i 1 `NIL`) ORELSE \p. Refine (set_elim i 1 (undeclared_id p `z`)) p)
    i
;;




let RecElementI = Refine (simple_rec_equality_element big_U) ;;

let eq_type t = snd (destruct_equal t) ;;

let RecMemberI p =
( let A = concl_type p  in
  if is_simple_rec_term A then RecElementI
  else 
    ComputeConclType THEN 
    (\p.( let A' = eq_type (concl p) in
          RecElementI
          THEN ReplaceSubtermInConcl A' A
        ) p
    )
) p
;;

let SquashIWith Tactic p =
( Refine (explicit_intro make_axiom_term)
  THEN (Tactic THENS SetElementI)
) p
;;

let SquashE i p =
  if not is_squash_term (type_of_hyp i p) then
    failwith `SquashE` ;
  ( E i
    THEN If (\p'. id_of_hyp i p = `NIL`) (OnNthLastHyp 2 Thin) (Thin i)
  ) p
;; 




letrec ExposeProperties i p =
  % Hyp i should be of the form x:T or t in T, where T computes to a set type %
  let x,H = destruct_hyp i p  in
  let [t],T = 
    destruct_equal H ?
    if not x = `NIL` then [mvt x], H else failwith `ExposeProperties: nothing to expose`  in
  If
    (\p. mvt x = t)
    (SetE i THEN Try (ExposeProperties i))
    ( let z',A,B' = destruct_set (compute T) and z = undeclared_id p `z`  in
      let B = substitute B' [mvt z', mvt z]   in
      let properties = 
        % z:T. (z in A) & (B(z)) %
        make_function_term
          z T (make_product_term `NIL` 
                (make_equal_term A [mvt z]) (make_ugly_squash_term B)) in
      let n = number_of_hyps p  in
      Assert properties
      THENL
      [ % prove properties %
        FastAp
        ( I 
          THENW (OnLastHyp SetE THEN I THENL [Idtac; SquashI])
        )
      ; % Use properties to get the desired new hyps, clean up, 
          and do a recursive application %
        Same
        [ OnLastHyp (EOn t)
        ; OnLastHyp E
        ; OnLastHyp SquashE
        ; Thinning [n+1; n+2]
        ; Try (ExposeProperties (n+1))
        ]
      ]
    ) 
    p
;;  




% Wimpy for now. %
let certainly_equal type1 type2 =
  simplify (fast_ap compute type1) = simplify (fast_ap compute type2)
;;






let TagHyp i id p =
  ( Refine (seq [type_of_hyp i p] [id])
    THENL
    [Refine (hyp i)
    ;Thinning [i]
    ]
  )
  p
;;


let ThinToEnd n p =
  Thinning (upto n (number_of_hyps p)) p
;;


%  A form of the sequence rule where only the last subgoal generated has
   extra hypotheses.
%
let ParallelSeq term_list p =
  (let n = number_of_hyps p   in
  Seq term_list 
  THENL 
  (replicate (ThinToEnd (n+1)) (length term_list)) @ [Idtac])
  p
;;




% Equality subgoal comes first %
let SubstConcl t' p =

( ParallelSeq 
    [make_equal_term (make_universe_term big_U) [t';concl p]
    ;t'
    ]
  THENL 
  [Idtac
  ;Idtac
  ;\p.  let x = undeclared_id p `x` in
        ( TagHyp (number_of_hyps p) x
          THEN Refine (explicit_intro (make_var_term x))
          THEN Refine equality
        ) p
  ]
) p

;;


% Equality subgoal comes first %
let SubstHyp H' i p =
( let x,H = destruct_hyp i p in
  let n = number_of_hyps p   in
  if not x=`NIL` then failwith `SubstHyp: not yet implemented for tagged hyps.` 
  else
    let y = undeclared_id p `y`   in
    Seq [make_equal_term (make_universe_term big_U) [H';H]
        ;H'
        ]
    THENL [Idtac
          ;TagHyp i y THEN Refine (explicit_intro (make_var_term y)) THEN Refine equality 
          ;Thinning [i; n+1]
          ]
)  p
;;


let SubstConclType t' p =

  let c = concl p   in
  if is_equal_term c then
    (  let eqs, t = destruct_equal c in
       ParallelSeq [make_equal_term (make_universe_term big_U) [t';t]
                   ;make_equal_term t' eqs
                   ]
       THENL [Idtac; Idtac; Refine equality]
    ) p
  else
    (  ParallelSeq [make_equal_term (make_universe_term big_U) [t';c]
                   ;t'
                   ]
       THENL [Idtac
             ;Idtac
             ;\p. let x = undeclared_id p `x` in
                  (TagHyp (number_of_hyps p) x
                   THEN Refine (explicit_intro (make_var_term x))
                   THEN Refine equality
                  ) p
             ]
    ) p

;;

%$%


%  Generalize E by eliminating a term (instead of just a variable).
The derived rule here is something like this:

>> G  BY ETerm 't'
H', t=s in T >> G[s/t]

where H' contains declarations of variables created by E, and s contains 
those variables plus appropriate canonical term constructors.
%
let ETermUsingNew t T x p =
  let x = mvt x in
  let new_goal =
    if is_var_term t then substitute (concl p) [t, x]
    else replace_subterm t x (concl p)  in
  let seq_term =
    % All x:T. x=t in T => G[x/t] % 
    make_function_term (dv x) T 
      (make_function_term `NIL` (make_equal_term T [x;t]) new_goal)   in
( Assert (seq_term)
  THENL
  [I THENW (OnLastHyp E THEN Try I)
  ;Same [OnLastHyp (EOn t); OnLastHyp E; Trivial]
  ]
) p
;;

let ETermUsing t T p = ETermUsingNew t T (undeclared_id p `x`) p ;;

let EPseudoDecl i p = 
  let [t],T = destruct_equal (type_of_hyp i p) in 
  ETermUsing t T p
;;

let ETermNew t x p = ETermUsingNew t (get_type p t) x p ;;

let ETerm t p = ETermUsing t (get_type p t) p ;; 

%$%


let has_id i p = not id_of_hyp i p = `NIL` ;;

let is_var_inclusion i p =
  ( let x = first_equand (concl p) and y = id_of_hyp i p in
    dv x = y
  ) ? false
;;


let subtype_of_inclusion i p =
  if is_var_inclusion i p then type_of_hyp i p
    else eq_type (type_of_hyp i p)
;;

%$%
% Reduce a inclusion where the outermost type constructors are the 
same to inclusions of the the components.  WARNING: Only implemented
for function types where the left-types are identical.
%
let DecomposeInclusionThen Tac i p =
( let T = subtype_of_inclusion i p and T' = eq_type (concl p) in
  if not term_kind T = term_kind T' then failwith `DecomposeInclusionThen` 
  if is_function_term T 
     & ( (fst o snd o destruct_function) T = (fst o snd o destruct_function) T' ) 
  then 
    let x,A,B = destruct_function T in
    ExtUsing T
    THENG ( (\p. Assert ( let t = (first_equand o concl) p in
                          let (),z = destruct_apply t in
                          make_equal_term (substitute B [mvt x, z]) [t]
                        ) p
            )
            THENL [Refine (function_equality_apply T); OnLastHyp Tac]
          )
  else failwith `DecomposeInclusionThen`
) p
;;
%$%
let DeclaredInSubset i =
  Repeat (SetE i THEN Try (Refine (hyp i)))    
;;

let Eq = Refine equality ;;



let TrivialInclusion i =

  Try (FastAp (ReduceHyp i))
  THEN Try Eq
  THEN Try (FastAp ReduceConcl)
  THEN Try Eq
  THEN Try (HypModCompUsing id eq_type i)
% THEN Try (FastAp (NormalizeHyp i))
  THEN Try Eq
  THEN Try (FastAp NormalizeConcl)
  THEN Try Eq %  % This was too costly. %
  THEN (\p. let A, A' = hyp_type i p, concl_type p in
            if simplify A = simplify A' & not A = A' then
              SubstConclType (hyp_type i p) p
            else Fail p
       )      
;;


let QuotientInclusion i p =
( ComputeConclType
  THEN
  (\ p' .
    if (subtype_of_inclusion i p = base_type 
      where (),(),base_type,()
                = destruct_quotient (concl_type p'))
    then Idtac p'
    else ComputeHypType i p'
  )
  THEN
  Refine (quotient_intro big_U)
  THEN
  (\ p . if is_wf_goal p then Idtac p 
         else Try Eq p)    
) p 
;;

letref hyp_type_at_inclusion_start = make_int_term ;; 

let SubsetInclusion i p =
( if not is_membership_goal p then failwith
    `Inclusion: need membership goal for SubsetInclusion` ;
  (\ p' .
    if (concl_type p' = base_type 
      where (),base_type,() = 
        destruct_set (subtype_of_inclusion i p))
    then Idtac p'
    else ComputeConclType p'
  )      
  THEN
  (\ p' .
    (if  is_var_inclusion i p then
                    DeclaredInSubset i 
     else
            let new_id = undeclared_id p' `v`  in
            let subset_assertion =
                make_function_term
                  new_id
                  (subtype_of_inclusion i p)
                  (make_equal_term 
                    (concl_type p')
                    [make_var_term new_id])  in
            let ProveWfGoal =
              ReverseComputeConclUsing 
                \t. make_equal_term (eq_type t) 
                      [make_tagged_term 0 hyp_type_at_inclusion_start]  in
            Assert subset_assertion
            THENL  
            [I THEN If is_wf_goal (Try ProveWfGoal) (OnLastHyp DeclaredInSubset)
            ;EOn (first_equand (concl p)) (number_of_hyps p' + 1) 
              THEN (Refine equality ORELSE (ComputeConclType THEN Refine equality))
            ]  
          ) p' 
  )
) p                 
;;




let is_subprop s t =
  letrec is_in t = 
    s=t or (  (let A,B = destruct_and t in is_in A or is_in B) ? false )
        or (  is_in (snd (destruct_implies t)) ? false )  in
  is_in t
;;


% Thins hyp i %
let RepeatFunAndEThen T terms i p =
  if not id_of_hyp i p = `NIL` then 
    failwith `RepeatFunAndEThen: hyp has declared var.` ;
  letrec Aux terms i p =
    Refine (hyp i) p
    ?
    let A = type_of_hyp i p in
    if is_function_term A & `NIL` = fst (destruct_function A) then
      Same [E i THEN Thin i; OnLastHyp (Aux terms)] p
    if is_function_term A & null terms then 
      T i p
    if is_function_term A then
      Same [EOn (hd terms) i THEN Thin i; OnLastHyp (Aux (tl terms))] p
    if is_and_term A then
      (E i THEN Thin i 
       THEN ( (OnLastHyp Thin THEN OnLastHyp (Aux terms))
              ORELSE (OnNthLastHyp 2 Thin THEN OnLastHyp (Aux terms)))
      ) p
    else
      T i p in
  Aux terms i p
;; 



% Match the conclusion against part of the conclusion of the implication in
hypothesis i, generating the antecedents of the implication as subgoals.
Use the term list for the terms required to elim the implication.  "not"
terms are treated specially.
%
let BackThruHypUsing inst_list i p =          
( let instantiating_terms = 
    match_part_in_context (\t. failwith `No match.`)
      (type_of_hyp i p) (concl p) p inst_list in
  Assert (type_of_hyp i p) THEN Try Hypothesis
  THEN OnLastHyp (RepeatFunAndEThen (\i. Refine (hyp i)) instantiating_terms)
) p
;;




let BackThruHyp i p = BackThruHypUsing [] i p ;;



let LemmaUsing name inst_list =

  Refine (lemma name `NIL`)
  THEN  ( OnLastHyp (BackThruHypUsing inst_list)
          ORELSE
          (SwapEquands THEN OnLastHyp (BackThruHypUsing inst_list)) 
        )
  THEN OnLastHyp Thin
;;

let Lemma name = LemmaUsing name [] ;;



let InstantiateLemma name term_list p =

   letrec make_instance subst_pairs_so_far remaining_terms t =
      ( if is_not_term t then fail ;
        let x,A,B = destruct_function t   in
        if x = `NIL` then make_instance subst_pairs_so_far remaining_terms B
        if null remaining_terms then fail
        else make_instance
              ((mvt x, hd remaining_terms) . subst_pairs_so_far)
              (tl remaining_terms) 
              B
      )
      ?
      substitute t subst_pairs_so_far in

(  Assert (make_instance [] term_list (main_goal_of_theorem name))
   THENL
   [FastAp 
    ( Refine (lemma name `NIL`) 
      THEN OnLastHyp (RepeatAtomicNotFunctionE term_list)
      THEN (\p'. let n = number_of_hyps p and n' = number_of_hyps p' in 
                 if n' > n+1 then Thinning [n+1] p' else Idtac p'  )
      THEN Try Trivial
    )
   ;Idtac
   ]
)  p

;;


let is_constant_gen_universe_term t = 
  is_universe_term t or is_constant_indexed_universe_term t
;;

let destruct_constant_gen_universe t =
  destruct_universe t 
  ? (destruct_integer o index_of_indexed_universe) t
;;

let same_level U U' =
  destruct_constant_gen_universe U = destruct_constant_gen_universe U'
;;

let ConstantCumulativity (U: term) p =
( let U' = concl_type p in
  ComputeConclUniverses
  THEN (  if not is_universe_term U & same_level U U' then Id 
          else Refine (cumulativity (destruct_constant_gen_universe U))
       )
  THEN Assert (make_equal_term U [first_equand (concl p)])
  THENL [Id; OnLastHyp ComputeHypUniverses THEN Trivial]
) p
;;
 

% >> t in U' 
    >> t in U   where U,U' are generalized universe terms and {U in U'}.

(Implemented so far only for the case where U' can be computed to a constant
at the level of Type or greater.)
%
let Cumulativity (U: term) p = 
( let U' = eq_type (concl p) in
  Try ComputeConclUniverses
  THEN
  (\p.
  ( let U'' = eq_type (concl p) in
    let eqs = equands (concl p) in
    if U'' = U & not U''=U' then Idtac
    if both is_universe_term U U'' then
      Refine (cumulativity (destruct_universe U)) 
    if both is_constant_gen_universe_term U U'' then
      ConstantCumulativity U
    if is_universe_term U'' & not destruct_universe U'' < level_of_Type () then 
      InstantiateLemma `U_members` 
        [index_of_indexed_universe U; first_equand (concl p)] 
      THEN IfThen is_wf_goal 
            (Try (Refine (cumulativity (level_of_Type ())) THEN Trivial))
    if U = make_universe_term 1 & is_indexed_universe_term U'' then
      Assert (make_equal_term U [(hd eqs)])
      THENL [Idtac; Lemma `U1_contained_in_Ui` THEN Try Trivial]
    else failwith `Cumulativity`
  ) p
  )
) p
;;
  
let UniverseInclusion i =
  (\p. Cumulativity (subtype_of_inclusion i p) p)
  THEN Try Eq
;;

let SameRecType i p =
( if not (term_kind (concl_type p) = `SIMPLE-REC` 
          or term_kind (subtype_of_inclusion i p) = `SIMPLE-REC`)
  then Fail
  else
    Try Eq
    THEN IfThen (\p. term_kind (concl_type p) = `SIMPLE-REC`)
                RecElementI
    THEN IfThen (\p. term_kind (subtype_of_inclusion i p) = `SIMPLE-REC`)
                ( if is_var_inclusion i p then E i
                  else (\p'. ETermUsing (first_equand (concl p))
                                        (subtype_of_inclusion i p') p'))
    THEN Refine equality    
) p 
;;

%$%

% A gross hack to allow Inclusion components access to the pre-computation
form of the hypothesis.  (Passing it as a parameter would change the type
of Inclusion, destroying parts of an existing library.) 
%

let WeaklyComputeHypType i =
  Try (ComputeHypType i THEN (\p. if not Inclusion_restricted_p
                                     or is_canonical_type (ht i p) 
                                  then Id p else fail))
;; 

let WeaklyComputeConclType =
  Try (ComputeConclType THEN (\p. if not Inclusion_restricted_p
                                     or is_canonical_type (concl_type p)
                                    then Id p else fail))
;; 

% Prove subgoals of the form 
     H, membership-hyp, H' >> t in T'
  where "membership-hyp" is the i-th hypothesis and is of the form
  t:T for t a var, or t in T.  
%
letrec Inclusion i p =
hyp_type_at_inclusion_start := hyp_type i p ; 
( Refine equality
  ORELSE (\p. First (map (\T. T i) (current_inclusion_additions ())) p)
  ORELSE UniverseInclusion i ORELSE
  ( WeaklyComputeHypType i THEN Try Eq
    THEN
    ( UniverseInclusion i 
      ORELSE SubsetInclusion i
      ORELSE
      ( WeaklyComputeConclType THEN Try Eq
        THEN
        ( UniverseInclusion i
          ORELSE SameRecType i
          ORELSE TrivialInclusion i  % Last because of the reduction bottleneck %
          ORELSE DecomposeInclusionThen Inclusion i
        )
      )
    )
  )
) p
;;




let may_have_over_term t =
  member_of_tok_list (term_kind t)
    [`INTEGER-INDUCTION`; `LIST-INDUCTION`; `DECIDE`; `SPREAD`;      
     `SIMPLE-REC-IND` ]
;;


let RecIndIOverUsingNew over_id over_term A ids p =
( let a,b = (destruct_simple_rec_ind o first_equand o concl) p in
  let n = number_of_hyps p in
  if is_simple_rec_term A then 
    Refine (simple_rec_equality_rec_ind (guess_U A p) over_id over_term A ids)
  else
    let A' = compute A in
    Refine (simple_rec_equality_rec_ind 
                (guess_U A p) over_id over_term A' ids)
    THENL [Every (map (ReplaceSubtermInHyp A' A) [n+1;n+2;n+3])
          ;ReplaceSubtermInConcl A' A
          ;ReplaceSubtermInConcl A' A 
          ]
) p
;;

let ListIndEqIUsing T p =
  Refine  (list_equality_induction
             `NIL` make_nil_term T
             (undeclared_id_using p `h`) 
             (undeclared_id_using p `t`) 
             (undeclared_id_using p `v`))
          p
;; 

let ListIndEqI p = 
  ListIndEqIUsing ( (get_type p o hd o subterms o first_equand o concl) p ) p
;; 

let get_over_pair t T p =
  ( if not may_have_over_term t then fail
    else
      let z = (undeclared_id p `z`) in
      let principal_arg = hd (subterms t)   in
      let T' =  if is_var_term principal_arg then substitute T [principal_arg, mvt z]
                else replace_subterm principal_arg (mvt z) T  in
      if T=T' then fail else z,T'
  )
  ? `NIL`, make_nil_term
    % Rules taking optional over terms take `NIL` to mean no over term. %
;;


% Do the intro appropriate to the first equand of the conclusion,
  guessing all required parameters.  Fails if parameters cannot be
  guessed.  No attempt is made yet to guess over terms. %

let EqI p =


  let (t.rest),T = destruct_equal (concl p)  in
  let over_id, over_term = get_over_pair t T p  in


  if is_object_term T & null rest then
    ( Complete (Refine (object_equality_member make_nil_term))
      ORELSE (\p'. Refine (object_equality_member (get_type p t)) p')
    ) p
  
  if is_object_term T then
    Refine (object_equality_member make_nil_term) p

  if is_token_term t then 
    Refine atom_equality_token p

  if is_any_term t then
    Refine void_equality_any p

  if is_natural_number_term t then 
    Refine integer_equality_natural_number p

  if is_minus_term t then 
    Refine integer_equality_minus p

  if is_addition_term t then 
    Refine integer_equality_addition p
          
  if is_subtraction_term t then 
    Refine integer_equality_subtraction p
        
  if is_multiplication_term t then 
    Refine integer_equality_multiplication p
        
  if is_division_term t then 
    Refine integer_equality_division p
        
  if is_modulo_term t then 
    Refine integer_equality_modulo p

  if is_axiom_term t then
    if is_equal_term T then Refine axiom_equality_equal p
    else Refine axiom_equality_less p
 
  if is_nil_term t then 
    Refine (list_equality_nil big_U) p

  if is_cons_term t then 
    Refine list_equality_cons p

  if is_inl_term t then 
    Refine (union_equality_inl big_U) p
  
  if is_inr_term t then 
    Refine (union_equality_inr big_U) p

  if is_lambda_term t then
    (Refine (function_equality_lambda big_U `nil`)
    ORELSE
    Refine (function_equality_lambda big_U
             (undeclared_id_using p (fst (destruct_lambda t))))
           ) p

  if is_pair_term t then 
    ( let v,(),() = destruct_product T  in
      if v=`nil` then (Refine product_equality_pair_independent) p
      else
      ( Refine (product_equality_pair big_U `nil`) 
        ORELSE
        Refine (product_equality_pair big_U 
        (undeclared_id_using p v))
      ) p
    )

  if is_integer_induction_term t then 
    (Refine (integer_equality_induction over_id over_term `nil` `nil`)
     ORELSE
     let (),(),(),u = destruct_integer_induction t  in
     let [n;y],() = destruct_bound_id u  in
     Refine (integer_equality_induction
              over_id over_term
              (undeclared_id_using p n) 
              (undeclared_id_using p y))
    ) p

  if is_list_induction_term t then
    ( let using = get_using_type p (fst (destruct_list_induction t))  in 
      Refine  (list_equality_induction 
                  over_id over_term using `nil` `nil` `nil`)
      ORELSE
      let (),(),u = destruct_list_induction t  in
      let [h;t;v],() = destruct_bound_id u in
      Refine  (list_equality_induction
                over_id over_term using
                (undeclared_id_using p h) 
                (undeclared_id_using p t) 
                (undeclared_id_using p v))
    ) p

  if is_decide_term t then 
    ( let using = get_using_type p (fst (destruct_decide t))  in 
      Refine  (union_equality_decide
                  over_id over_term using `nil` `nil`)
      ORELSE
      let (),u,v = destruct_decide t  in
      let [x],() = destruct_bound_id u in
      let [y],() = destruct_bound_id v  in
      Refine  (union_equality_decide
                over_id over_term using 
                (undeclared_id_using p x) 
                (undeclared_id_using p y))
    ) p


  if is_spread_term t then
    ( let using = get_using_type p (fst (destruct_spread t))  in 
      Refine  (product_equality_spread
                over_id over_term using `nil` `nil`)
      ORELSE
      let (),u = destruct_spread t  in
      let [x;y],() = destruct_bound_id u in
      Refine  (product_equality_spread
                over_id over_term using
                (undeclared_id_using p x) 
                (undeclared_id_using p y))
    ) p

  if is_apply_term t then
    (let b,a = destruct_apply t  in
      (\ p.
        ( let using = get_using_type p b in
          let x,A,B = destruct_function using in
          let T' = if x=`NIL` then B 
                   else substitute B [make_var_term x,a] in
          if T'=T then Refine (function_equality_apply using)
          if both is_gen_universe_term T' T & not T=T' then
            Cumulativity T'
            THEN
            Try (Refine  (function_equality_apply using))
          else  
            Try 
            ( Assert (make_equal_term T' (t.rest))
               THENL
               [Refine (function_equality_apply using)
               ;FastAp (OnLastHyp Inclusion)
               ]
               ORELSE If (\p. certainly_equal T T') (SubstConclType T') Fail
            )
        ) p
      ) p
      ?
      (\p. Refine (function_equality_apply
                    (make_function_term `nil` (get_type p a) T))
                  p
      ) p
     ) 

  if is_simple_rec_ind_term t then 
    ( let using = get_type p (fst (destruct_simple_rec_ind t))  in 
      let ids = map (undeclared_id p) [`P`; `x`; `h`; `z`] in
      RecIndIOverUsingNew over_id over_term using ids
    ) p

  if is_atom_eq_term t then Refine atom_eq_equality p
  
  if is_int_eq_term t then Refine int_eq_equality p

  if is_intless_term t then Refine int_less_equality p

  if is_atom_term t then Refine atom_equality p

  if is_void_term t then Refine void_equality p

  if is_int_term t then Refine integer_equality p

  if is_object_term t then Refine object_equality p

  if is_less_term t then Refine less_equality p

  if is_universe_term t then Refine universe_equality p

  if is_list_term t then Refine list_equality p
 
  if is_equal_term t then Refine equal_equality p

  if is_function_term t then
    ( Refine (function_equality `nil`) 
      ORELSE
      Refine (function_equality 
                (undeclared_id_using p (fst (destruct_function t))))
    ) p

  if is_product_term t then
    (Refine (product_equality `nil`)
     ORELSE
     Refine (product_equality 
              (undeclared_id_using p (fst (destruct_product t))))
    ) p

  if is_simple_rec_term t then
    ( Refine (simple_rec_equality `NIL`)
      ORELSE 
      Refine (simple_rec_equality (undeclared_id_using p (fst (destruct_simple_rec t))))
    ) p

  if is_set_term t then
    ( Refine (set_equality `nil`)
      ORELSE
      Refine (set_equality (undeclared_id_using p 
              (fst (destruct_set t))))
    ) p

  if is_union_term t then Refine union_equality p

  if is_quotient_term t then 
    ( let v= fst (destruct_quotient t) in
      Refine (quotient_equality 
                (undeclared_id_using p v) 
                (undeclared_id_using p v))
    ) p

  else failwith `EqI`

;;

let poly_typing =
  main_goal_of_theorem o append_underscore o destruct_term_of_theorem o head_of_application
;;



% topmost using type first %
let using_types_for_repeated_ap t p =
  let l = decompose_application t in
  let n = if almost_poly_defined_term t then 
            1 + (arity_of_poly_definition o destruct_term_of_theorem o hd) l  
          else 1 in
  let args = nthcdr n l in
  if null args then fail ;
  let fun = iterate_fun make_apply_term (firstn n l)  in
  % build using types inside out %
  letrec build_using_types remaining_args =
    if null (tl remaining_args) then 
      [get_using_type p fun]
    else let l = build_using_types (tl remaining_args)  in
         let x,A,B = destruct_function (compute (hd l)) in
         if x=`NIL` then B.l else (substitute B [mvt x, (second remaining_args)]) . l in
  build_using_types (rev args)
;;

% like using_types_for_repeated_ap except a function type is supplied for the 
  head of the application sequence which cannot be itself an application.
%
let extend_using_types_for_repeated_ap t function_type =
  let ().args = decompose_application t in
  if null args then fail ;
  % build using types inside out %
  letrec build_using_types remaining_args =
    if null (tl remaining_args) then [function_type]
    else let l = build_using_types (tl remaining_args)  in
         let x,A,B = destruct_function (compute (hd l)) in
         if x=`NIL` then B.l else (substitute B [mvt x, (second remaining_args)]) . l in
  build_using_types (rev args)
;;
  
let RepeatApIUsingsThen using_types T p = 
  letrec Aux using_types p =
    if null using_types then T p
    else 
      ( Refine (function_equality_apply (hd using_types))
        THENL [Aux (tl using_types); Idtac]
      ) p   in
  Aux using_types p
;;

let RepeatApIUsingThen function_type T p =
  RepeatApIUsingsThen
    (extend_using_types_for_repeated_ap (first_equand (concl p)) function_type) 
    T p
;;

let RepeatApIUsing t = RepeatApIUsingThen t Idtac ;;

let RepeatApIThen T p =
  RepeatApIUsingsThen (using_types_for_repeated_ap (first_equand (concl p)) p) T p
;;

let RepeatApI = RepeatApIThen Idtac ;;

define_DE `E` (\p. E (hyp_num_arg ()) p) ;;

define_DI `I` (\p. E (hyp_num_arg ()) p) ;;









