%-*-Tab-Width: 2 -*-%







let ids = words ;; 

let sum = accumulate (\x y. x+y) 0 ;;

letrec nodes p = 1 + (sum (map nodes (children p)) ? 0) ;;



letrec InductionOn k n p =                                                     
  (let x,A,() = destruct_function (concl p) in                                 
   if x = n then                                                               
     I THENW NonNegInd k (number_of_hyps p + 1)                            
   else                                                                        
     I THENW InductionOn n k                                               
  ) p                                                                          
  ?                                                                            
  Idtac p                                                                      
;;                                                                             
                                                                               

let OnVar v T =                                                                
  let TryHyps p = T (find_declaration v p) p in                                
  letrec BeatConcl p =                                                         
    ( I THENW ( \p. let n = number_of_hyps p in                                  
                    if v = id_of_hyp n p then T n p                              
                    else BeatConcl p 
              )                                           
    ) p in                                                                     
  TryHyps ORELSE BeatConcl                                                     
;;                                                                             
                                                                               

let CaseHyp i p =                                                              
  if is_union_term (type_of_hyp i p) then                                      
    (E i THEN Thinning [i]) p                                               
  else failwith `CaseHyp: hyp not and "or" term`                               
;;                                                                             
                                                                               

                                                                               


let AbstractConcl instance p =                                                 
( let x = undeclared_id p `x` in                                               
  Assert                                                                       
    (make_apply_term                                                           
      (make_lambda_term x                                                      
        (replace_subterm instance (mvt x) (concl p)))                          
      instance)                                                                
  THENL                                                                        
  [Idtac                                                                       
  ;OnLastHyp (ComputeHypUsing (make_tagged_term 1))                       
   THEN Hypothesis                                                             
  ]                                                                            
) p                                                                            
;;                                                                             



let InductionLemma lemma_name parameter base instance p =
  FastAp ( AbstractConcl instance
           THEN                                                                 
           LemmaUsing lemma_name [parameter; base]
         )
         p
;;








let unfold t =
  let f.args = decompose_application t in
  (no_extraction_compute o make_application) 
    ( (extracted_term_of_theorem o destruct_term_of_theorem) f . args )
;;

%
letrec unfold_until_rec t =
  let n,t' = unfold t in
  let f = head_of_application t' in
  if is_simple_rec_term f or is_list_induction_term f then n,t'
  else (let n',t'' = unfold_until_rec n,t' in n+n', t'')
;; 
%

let tag_for_unfold name t = 
  let name_ = name^`_`  in
  let k = arity_of_extraction (make_term_of_theorem_term name_) in
  letrec aux t =
    let t' = map_on_subterms aux t in
    let f.args = decompose_application t  in
    ( if destruct_term_of_theorem f = name_ & length args = k then
        let (),n = unfold t in make_tagged_term (n+1) t'
      else fail
    ) ? t'  in
  aux t
;;

let UnfoldInConcl name =
  ComputeConclUsing (tag_for_unfold name) 
;;

let UnfoldInHyp name =
  ComputeHypUsing (tag_for_unfold name) 
;;

let Unfold name =
  TryEverywhere (UnfoldInHyp name) (UnfoldInConcl name)
;;

let UnfoldsInConcl names =
  Every (map UnfoldInConcl names) 
;;

let UnfoldsInHyp names i =
  Every (map (\name . UnfoldInHyp name i) names)
;;


let Unfolds names =
  TryEverywhere (UnfoldsInHyp names) (UnfoldsInConcl names)
;;

letrec remove_tags t = 
  map_on_subterms remove_tags ((snd o destruct_tagged) t ? t)
;;


let fold_and_tag_poly name_ p t =
  let f = make_term_of_theorem_term name_ in 
  let fun_ids, fun_body = 
    destruct_lambdas (extracted_term_of_theorem name_) in
  let thm = (main_goal_of_theorem (name_^`_`)) ? make_nil_term in
  let context, () = explode_function thm ? [],thm in
  let match' t = 
    map (lookup (extend_bindings_using_context 
                  context (match fun_body t fun_ids) p))
        fun_ids in
  let n = length fun_ids in
  letref tagged_something = false in
  letrec aux t =
    ( let folded_term = make_application (f . match' t)   in
      tagged_something := true ; 
      (make_tagged_term (n+1) o map_on_subterms aux) folded_term
    )
    ?
    ( if not is_lambda_term t then fail else 
      let i = length fun_ids - length (fst (destruct_lambdas t)) in
      let match_ids = firstn i fun_ids in
      let bins = match (make_lambdas (nthcdr i fun_ids) fun_body) t match_ids in
      tagged_something := true ;
      (make_tagged_term (i+1) o map_on_subterms aux)
      (make_ap (f . map (lookup bins) match_ids))
    )
    ? map_on_subterms aux t   in
  assert (\x. tagged_something) (aux t)
;;


let fold_and_tag_extraction name_ p t =
  let f = make_term_of_theorem_term name_ in 
  let fun_ids, fun_body = 
    destruct_lambdas (extracted_term_of_theorem name_) in
  let thm = main_goal_of_theorem name_ in
  let context', () = explode_function thm ? [],thm in
  let context = 
    map (\x,A. if x=`NIL` then undeclared_id p `x`, A else x, A) context' in
  let ids = map fst context in
  let pattern, n = fast_ap (unfold o make_application) (f . map mvt ids) in
  let pattern_container = implode_function context pattern in
  let match' t = match_part_in_context (\x. fail) pattern_container t p [] in
  letref tagged_something = false in
  letrec aux t =
    ( let folded_term = make_application (f . match' t)   in
      tagged_something := true ; 
      (make_tagged_term (n+1) o map_on_subterms aux) folded_term
    )
    ?
    ( if not is_lambda_term t then fail else 
      let i = length fun_ids - length (fst (destruct_lambdas t)) in
      let match_ids = firstn i fun_ids in
      let bins = match (make_lambdas (nthcdr i fun_ids) fun_body) t match_ids in
      tagged_something := true ;
      (make_tagged_term (i+1) o map_on_subterms aux)
      (make_ap (f . map (lookup bins) match_ids))
    )
    ? map_on_subterms aux t in
  assert (\x. tagged_something) (aux t)
;;

let fold_and_tag name p t =
  let name_ = name ^ `_`  in
  if is_object_term (main_goal_of_theorem name_) then
    fold_and_tag_poly name_ p t
  else fold_and_tag_extraction name_ p t
;;


let FoldInConcl names p =
  let Aux name = Try (ReverseComputeConclUsing (fold_and_tag name p)) in
  Progress (Every (map Aux names)) p
;;

let FoldInHyp names i p =
  let Aux name = Try (ReverseComputeHypUsing (fold_and_tag name p) i) in
  Progress (Every (map Aux names)) p
;;

let Fold names = TryEverywhere (FoldInHyp names) (FoldInConcl names) ;;





let tag_for_unfold_rec name t = 
  let name_ = name^`_`  in
  let k = arity_of_extraction (make_term_of_theorem_term name_) in
  letrec aux t =
    let t' = map_on_subterms aux t in
    let f.args = decompose_application t  in
    ( if destruct_term_of_theorem f = name_ & length args = k then
        let (),n = unfold t in make_tagged_term (n+2) t'
      else fail
    ) ? t'  in
  aux t
;;

let UnfoldRecInConcl name =
  ComputeConclUsing (tag_for_unfold_rec name) 
  THEN ReduceConcl THEN FoldInConcl [name]
;;

let UnfoldRecInHyp name i =
  ComputeHypUsing (tag_for_unfold_rec name) i
  THEN ReduceHyp i THEN FoldInHyp [name] i
;;

let UnfoldRec name =
  TryEverywhere (UnfoldRecInHyp name) (UnfoldRecInConcl name)
;;


let UnfoldRecsInConcl names =
  Every (map UnfoldRecInConcl names) 
;;

let UnfoldRecsInHyp names i =
  Every (map (\name . UnfoldRecInHyp name i) names)
;;


let UnfoldRecs names =
  TryEverywhere (UnfoldRecsInHyp names) (UnfoldRecsInConcl names)
;;



let UnrollDefsInConcl names =
  UnfoldsInConcl names THEN ReduceConcl THEN Try (FoldInConcl names)
;; 


let UnrollDefsInHyp names i =
  UnfoldsInHyp names i THEN ReduceHyp i THEN Try (FoldInHyp names i)
;; 

let UnrollDefs names =
  TryEverywhere (UnrollDefsInHyp names) (UnrollDefsInConcl names)
;;

% For recursively (rec_ind) defined functions of the form
ˆx1. ˆ.... ˆxn. rec_ind(xn;...) where (n-1) args can be guessed from
ˆxn. rec_ind(xn;...')
%
let unroll_rec_taggers p name =
  let name_ = name^`_` in
  let ids, rec_ind = destruct_lambdas (extracted_term_of_theorem name_) in
  if not (is_simple_rec_ind_term rec_ind & hd (subterms rec_ind) = mvt (last ids))  
  then failwith `unroll_rec_taggers` ;
  letrec aux t =
    let f.args = decompose_application t in
    let ids', rec_ind' = destruct_lambdas f in
    if not (is_simple_rec_ind_term rec_ind' & length ids' = 1 
            & mvt (hd ids') = hd (subterms rec_ind')
            & can (match rec_ind rec_ind') ids
            ? false)
    then (if null args then map_on_subterms aux f 
          else make_ap (map aux (f.args)))
    else make_ap (fold_and_tag name p f . map (map_on_subterms aux) args)  in
  tag_for_unfold_rec name, aux
;; 

let UnrollRecInConcl name p =
  let f,g = unroll_rec_taggers p name in 
  (ComputeConclUsing f THEN ReverseComputeConclUsing g) p
;; 

let UnrollRecInHyp name i p =
  let f,g = unroll_rec_taggers p name in 
  (ComputeHypUsing f i THEN ReverseComputeHypUsing g i) p
;; 

let UnrollRec name = 
  TryEverywhere (UnrollRecInHyp name) (UnrollRecInConcl name)
;; 


let UnrollRecsInConcl names =
  Every (map UnrollRecInConcl names) 
;;

let UnrollRecsInHyp names i =
  Every (map (\name . UnrollRecInHyp name i) names)
;;


let UnrollRecs names =
  TryEverywhere (UnrollRecsInHyp names) (UnrollRecsInConcl names)
;;

letrec tag_for_unext names t =
  if is_term_of_theorem_term t & member (destruct_term_of_theorem t) names
  then make_tagged_term 1 t 
  else map_on_subterms (tag_for_unext names) t
;; 

let UnExtInConcl names = ComputeConclUsing (tag_for_unext names) ;; 
let UnExtInHyp names = ComputeHypUsing (tag_for_unext names) ;; 
let UnExt names = TryEverywhere (UnExtInHyp names) (UnExtInConcl names) ;; 

let find_in_term P t =
  letref found_term = make_nil_term in
  letrec aux t = 
    P t => (found_term := t; failwith `found`) | map_on_subterms aux t in
  (aux t; failwith `find_in_term`) ?? ``found`` found_term
;; 

% i=0 indicates concl %
let UnrollRecOccAux i P p = 
( let t = i=0 => concl p | h i p in
  let occ = find_in_term P t in
  let f = head_of_application occ in
  let name = destruct_term_of_theorem f in
  let ids, b = destruct_lambdas (extracted_term_of_theorem name) in
  if not is_simple_rec_ind_term b then
    failwith `Unroll1RecAux: not a rec def` ;
  let arity = length ids in
  if not length (decompose_ap occ) = arity + 1 then 
    failwith `Unroll1RecAux: wrong number of args in supplied term` ; 
  let tagged_t = 
    replace_subterm occ (make_tagged_term (arity+2) occ) t in
  let folded_rec_fun = make_ap (remove_last (decompose_ap occ)) in
  let unfolded_rec_fun = compute folded_rec_fun in 
  let tag_for_fold t =
    replace_subterm unfolded_rec_fun 
      (make_tagged_term arity folded_rec_fun) t in
  (i=0 => Refine (direct_computation tagged_t) 
       |   Refine (direct_computation_hyp i tagged_t))
  THEN
  (i=0 => ReverseComputeConclUsing tag_for_fold
       |  ReverseComputeHypUsing tag_for_fold i)
) p
;; 

let UnrollRecOccInConcl P = UnrollRecOccAux 0 P ;; 
let UnrollRecOccInHyp P i = UnrollRecOccAux i P ;; 




let MultiAbstractConcl instances p =
  let ids = map (\x. undeclared_id p `x`) instances   in
  let lambda_body = 
    accumulate  
      (\t (x,t'). replace_subterm t' (mvt x) t)
      (concl p)
      (ids com instances) in
  let t = make_application (make_lambdas ids lambda_body . instances) in
  ( Assert t
    THENL                                                                        
    [Idtac                                                                       
    ;OnLastHyp (ComputeHypUsing (make_tagged_term (length instances)))
     THEN Hypothesis                                                             
    ]                                                                            
  ) p                                                                            
;;                                                                             




let is_le_term t =
  (is_less_term o destruct_not) t
  ? false
;;

let make_le_term a b =
  make_not_term (make_less_term a b)
;;

let swap_pair (x,y) = y,x ;;

let destruct_le =
  swap_pair o destruct_less o destruct_not
;;

let first_relnand t = 
  if is_equal_term t then (first o fst o destruct_equal) t 
  if is_less_term t then  (fst o destruct_less) t
  if is_le_term t then (fst o destruct_le) t
  else (second o rev o decompose_application) t
;;

let second_relnand t = 
  if is_equal_term t then (second o fst o destruct_equal) t 
  if is_less_term t then  (snd o destruct_less) t
  if is_le_term t then (snd o destruct_le) t
  else (first o rev o decompose_application) t
;;

let swap_equands t = 
  let [t';t''],T = destruct_equal t in
  (make_equal_term T [t'';t'])
;;

% Only for equality and defined relations. %
let swap_relnands t =
  swap_equands t
  ?
  (make_application o rev o (\(a.b.l). b.a.l) o rev o decompose_application) t
;;

let replace_first_relnand t t' =
  if is_equal_term t then
    (let [a;b],T = destruct_equal t in make_equal_term T [t';b])
  if is_less_term t then make_less_term t' (second_relnand t)
  if is_le_term t then make_le_term t' (second_relnand t)
  else 
    (make_application o rev o (\(a.b.l). a.t'.l) o rev o decompose_application)
    t
;;

let replace_second_relnand t t' =
  if is_equal_term t then 
    (let [a;b],T = destruct_equal t in make_equal_term T [a;t'])
  if is_less_term t then make_less_term (first_relnand t) t'
  if is_le_term t then make_le_term (first_relnand t) t'
  else 
    (make_application o rev o (\(a.b.l). t'.b.l) o rev o decompose_application) 
    t
;;

let replace_both_relnands t t' t'' =
  if is_equal_term t then 
    (let [a;b],T = destruct_equal t in make_equal_term T [t';t''])
  if is_less_term t then make_less_term t' t''
  if is_le_term t then make_le_term t' t''
  else 
    (make_application o rev o (\(a.b.l). t''.t'.l) o rev o decompose_application) 
    t
;;

let SwapEquandsInConcl  =
  (\p. Assert (swap_equands (concl p)) p)
  THEN Try Trivial
;;

let SwapRelnandsInConcl =
  SwapEquandsInConcl
  ORELSE
  (\p.
    Lemma ( ((\x. x^`sym`) o destruct_term_of_theorem o head_of_application o concl) p ) p
  )
;;

% Only for equality and defined relations.  For defined relations, it is assumed
  that the instance of the relation is an application headed by a term_of, whose 
  name, when suffixed with `sym`, gives the name of a symmetry theorem. 
%
let SwapRelnandsInHyp i p =
  ( Assert (swap_relnands (type_of_hyp i p))
    THENL [SwapRelnandsInConcl; Idtac]
  )
  p
;;

let last_hyp_type = (type_of_declaration o last o hyps) ;;

lettype generic_arg = term + (int + int) + (tok + tok) ;; 

let in_term: term->generic_arg =  inl
and in_hyp: int->generic_arg =  inr o inl o inl
and in_rev_hyp: int->generic_arg =  inr o inl o inr
and in_lemma: tok->generic_arg =  inr o inr o inl
and in_rev_lemma: tok->generic_arg =  inr o inr o inr
and term_of_generic_arg (x:generic_arg) =
  outl x ? failwith `term_of_generic_arg`
and hyp_of_generic_arg (x:generic_arg) =
  (outl o outl o outr) x ? failwith `hyp_of_generic_arg`
and rev_hyp_of_generic_arg (x:generic_arg) =
  (outr o outl o outr) x ? failwith `hyp_of_generic_arg`
and lemma_of_generic_arg (x:generic_arg) =
  (outl o outr o outr) x ? failwith `lemma_of_generic_arg`
and rev_lemma_of_generic_arg (x:generic_arg) =
  (outr o outr o outr) x ? failwith `rev_lemma_of_generic_arg`
;;

% For goals of the form: >> x R' z, when left_to_right_p is true (false),
this tactic attempts to use the named lemma to step forward (backward)
from the left (right) relnand.  (Interpolator left_to_right_p) should do
the following (modulo Autotactic):

H, xRy >> xR'z --> >> yR''z  if left_to_right_p
H, yRz >> xR'z --> >> xR''y  otherwise

It should not leave any subgoals whose proof requires the above indicated
hypotheses and does not follow by Trivial.
%
let RelnStep (Interpolator: bool->tactic) left_to_right_p (arg: generic_arg) =

  let ApplyLemma p =
    let lemma_name, revp = 
      lemma_of_generic_arg arg, false ? rev_lemma_of_generic_arg arg, true  in
    let pattern_container = main_goal_of_theorem lemma_name in
    let relnand_to_match = 
      if left_to_right_p then first_relnand (concl p) 
      else second_relnand (concl p) in
    let instantiators =
      if revp & left_to_right_p or not revp & not left_to_right_p then 
        match_part_in_context second_relnand pattern_container 
          relnand_to_match p [] 
      else match_part_in_context first_relnand pattern_container 
            relnand_to_match p []  in
    ( InstantiateLemma lemma_name instantiators 
      THENS (if revp then OnLastHyp (\i. SwapRelnandsInHyp i THEN Thinning [i]) 
             else Idtac)
    ) p      in

  let ApplyHyp p =
    let i, revp = 
      hyp_of_generic_arg arg, false ? rev_hyp_of_generic_arg arg, true  in
    let pattern_container = type_of_hyp i p in
    let relnand_to_match = 
      if left_to_right_p then first_relnand (concl p) 
      else second_relnand (concl p) in
    let instantiators =
      if revp & left_to_right_p or not revp & not left_to_right_p then 
        match_part_in_context second_relnand pattern_container 
          relnand_to_match p [] 
      else match_part_in_context first_relnand pattern_container 
            relnand_to_match p []  in
    ( InstantiateHyp instantiators i 
      THENS  (if revp then OnLastHyp (\i. SwapRelnandsInHyp i THEN Thinning [i]) 
              else Idtac)
    ) p      in

  let ExplicitlyInterpolate p =
    let t = term_of_generic_arg arg in
    let step =
      if left_to_right_p then replace_second_relnand (concl p) t
      else replace_first_relnand (concl p) t    in
    Assert step p in

  (\p. ApplyLemma p ? ApplyHyp p ? ExplicitlyInterpolate p 
        % ORELSE has a PROGRESS in it % 
  )
  THENS
  ( Interpolator left_to_right_p 
    THEN (Trivial ORELSE OnLastHyp Thin)
  )

;;



let BasicInterpolator left_to_right_p p =
  let t = last_hyp_type p  and  t' = concl p  in
  if is_equal_term t & (is_less_term t' or is_le_term t' or is_equal_term t') 
     or (is_le_term t or is_less_term t) & (is_le_term t' or is_less_term t')
    then
      ( if left_to_right_p then 
          Assert (replace_first_relnand t' (second_relnand t)) p
        else Assert (replace_second_relnand t' (first_relnand t)) p
      )
  if is_equal_term t then 
    (if left_to_right_p then SubstFor t p else SubstFor (swap_equands t) p)
  else LemmaUsing 
        ( ( (\x. x^`trans`) o destruct_term_of_theorem 
              o head_of_application o concl
          ) p 
        )
        [if left_to_right_p then second_relnand t else first_relnand t]
      p
;;

let RelnStepR = RelnStep BasicInterpolator true ;;

let RelnStepL = RelnStep BasicInterpolator false ;;

let remove_last_char = implode o rev o tl o rev o explode ;; 




let SomeDTactic Tactics p =
  letrec Aux Ts p = 
    hd Ts p 
    ?? [`no`] Aux (tl Ts) p    in
  Aux Tactics p ?? [`HD`] failwith `none applicable`
;;



let CtdDE i p =
  d_tactic_hyp_num_arg := i ;
  (HeadReduceHyp i THEN
   SomeDTactic (current_DE_definitions ())) p
;; 

let DE i terms choices ids p =
  set_d_tactic_args i terms choices ids ;
  CtdDE i p
;;



let CtdDI p =
  (HeadReduceConcl THEN
   SomeDTactic (current_DI_definitions ())) p
;; 


let DI terms choices ids p =
  set_d_tactic_args 0 terms choices ids ;
  CtdDI p
;;


ml_curried_infix `TRYTHENL` ;; 

let $TRYTHENL (tac1:tactic) (tac2l:tactic list) (g:proof) =
   let gl,p = tac1 g  in
   (  let gll,pl = split(map (\(tac2,g). tac2 g) tac2gl)
                  where tac2gl = combine(tac2l,gl) in
      flat gll  ,  (p o mapshape(map length gll)pl)
   )
   ?? [`combine`] gl, p
;;


% A DI or DE may be applications of patterns.  To
  create a pattern, set the args to be arbitrary, (do this
  in a library object right before the pattern), and develop
  a proof of a statement of a theorem that uses atoms for 
  syntactic variables.  Get parameters using only the get functions,
  and only refer to hypothesis numbers via nth_last_hyp.
%
let ApplyPattern pattern_pf =
  letrec Aux pattern_pf =
    if is_refined pattern_pf then
      Refine (refinement pattern_pf) 
      TRYTHENL map Aux (children pattern_pf)
    else Idtac  in
  Aux pattern_pf
;;

let nth_last_hyp j p =
  number_of_hyps p - (j-1)
;;

let make_macro_recognizer name =
  \t. name = top_def_of_term t ? false
;;

let make_def_recognizer name arity =
  let name = name ^ `_` in
  \t. (name = destruct_term_of_theorem (head_of_application t)
       & arity = arity_of_application t) ? false
;;


let define_patterned_DI pattern_name recognizer =
  define_DI
  pattern_name
  (\p.
    if recognizer (concl p)
    then ApplyPattern (proof_of_theorem pattern_name) p
    else failwith `no`
  )
;;

let define_patterned_DE pattern_name recognizer =
  define_DE
  pattern_name
  (\p.
    if recognizer (type_of_hyp (hyp_num_arg ()) p)
    then ApplyPattern (hd (children (proof_of_theorem pattern_name))) p
    else failwith `no`
  )
;;






let PatternAllI p =
  if `NIL` = fst (destruct_function (concl p)) then fail ;
  ( (\p. Refine (function_intro big_U (get_id_arg ())) p)
    ORELSE I
  ) p
;;


let RepeatDEFor n i terms choices ids =
  set_d_tactic_args i terms choices ids ;
  letrec Aux n i =
    if n=0 then Idtac
    else CtdDE i 
         THENS (Hypothesis ORELSE (\p. Try (Aux (n-1) (number_of_hyps p)) p))
  in
  Aux n i
;;

let RepeatCtdDEFor n i =
  letrec Aux n i =
    if n=0 then Idtac
    else CtdDE i 
         THENS (Hypothesis ORELSE (\p. Try (Aux (n-1) (number_of_hyps p)) p))   
  in
  Aux n i
;;



let ReplaceHyp i t = 
  Assert t THEN Try Hypothesis THEN Thinning [i]
;;


let define_lemmad_DI lemma_name recognizer =
  let T = Lemma lemma_name  in
  define_DI
    lemma_name
    (\p. if recognizer (concl p) 
          then T p
          else failwith `no`
    )
;;



let define_lemmad_DE lemma_names (remove_p: bool) recognizer =
  let T p = 
    let i = hyp_num_arg ()  in
    ( Same (map (\name. LemmaFromHyps name [i] []) lemma_names)
      THENS (if remove_p then Thinning [i] else Idtac)  
    ) p     in
  define_DE
    (concat_using_commas lemma_names)
    (\p. if recognizer (type_of_hyp (hyp_num_arg ()) p)
          then T p
          else failwith `no`
    )
;;



let ids = words ;; 

let sum = accumulate (\x y. x+y) 0 ;;

letrec nodes p = 1 + (sum (map nodes (children p)) ? 0) ;;


% Following are some renames for compatability with old
libraries. %

let Elim = E ;;
let Intro = I ;;
let EqualityIntro = EqI ;;
let RepeatAndElim = RepeatAndE ;;
let RepeatFunctionElim = RepeatFunctionE ;;
let SetElementIntro = SetElementI ;;



let OrByHyp p =
  if not is_union_term (concl p) then failwith `OrByHyp` ;
  let disjuncts = destruct_disjunction (concl p) in
  let target =
    find (\hyp. member hyp disjuncts) (map (snd o destruct_declaration) (hyps p)) in
  let Choose =
    IfOnConcl (member target o destruct_disjunction o fst o destruct_union)
      ILeft IRight  in
( Repeat (IfThenOnConcl is_union_term Choose)
  THENW Trivial
) p
;;

let abstract term subterm newid =
  make_apply_term 
    (make_lambda_term newid (replace_subterm subterm (mvt newid) term))
    subterm
;;

let TypeSubtermNew subterm type newid p =
  let l,T = destruct_equal (concl p) in
  let l' = map (\a. abstract a subterm newid) l in
  let using = make_function_term `NIL` type T in
( Assert (make_equal_term T l')
  THENL 
  [Refine (function_equality_apply using) THENL [EqI;Id]
  ;OnLastHyp (ComputeHypEquandsFor 1) THEN Hypothesis
  ]
) p
;; 


letrec TypeSubterms subterms_and_types p =
  let (subterm,type).rest = subterms_and_types in
  let l,T = destruct_equal (concl p) in
  let l' = map (\a. abstract a subterm (undeclared_id p `x`)) l in
  let using = make_function_term `NIL` type T in
( Assert (make_equal_term T l')
  THENL 
  [Refine (function_equality_apply using) 
   THENL [EqI THENL [Try (TypeSubterms rest); Id] ;Id] 
  ;OnLastHyp (ComputeHypEquandsFor 1) THEN Hypothesis
  ]
) p
;; 


let TypeSubterm subterm type p = 
  TypeSubtermNew subterm type (undeclared_id p `x`) p
;;

let TypeSubtermUsingHyp i p =
  let (t.()),T = destruct_equal (h i p) in
  TypeSubterm t T p
;; 

let TypeSubtermsUsingHyps hyps p =
  TypeSubterms (map (\i. let (t.()),T = destruct_equal (h i p) in t,T) hyps) p
;; 
 

let Dupl i p =
  let x,A = destruct_hyp i p in 
  let duplicated_hyp = 
    if x=`NIL` then A
    else make_equal_term A [mvt x] in
  (Assert duplicated_hyp THEN Try Trivial) p
;; 

let DuplThen T i = Dupl i THEN OnLastHyp T ;; 

let typing_from_hyp i p =
  let x,A = destruct_hyp i p in
  if is_equal_term A then (let [t],T = destruct_equal A in t,T)
  if x=`NIL` then fail
  else mvt x, A
;; 

let ContainmentLemma name i =
  BringHyps [i] THEN Lemma name
;; 

let abstract_and_tag_subterm subterm subsubterm newid term =
  replace_subterm 
    subterm
    (make_tagged_term 1 (abstract subterm subsubterm newid)) 
    term
;; 

let AbstractInConcl subterm subsubterm p =
  ReverseComputeConclUsing
    (abstract_and_tag_subterm subterm subsubterm (undeclared_id p `x`))
    p
;; 


let AbstractInHyp subterm subsubterm i p =
  ReverseComputeHypUsing
    (abstract_and_tag_subterm subterm subsubterm (undeclared_id p `x`))
    i
    p
;; 




let GenThenUsingNew t T x Tac p =
  let x = mvt x in
  let new_goal =
    if is_var_term t then substitute (concl p) [t, x]
    else replace_subterm t x (concl p)  in
  let seq_term =
    % All x:T. x=t in T => G[x/t] % 
    make_function_term (dv x) T 
      (make_function_term `NIL` (make_equal_term T [x;t]) new_goal)   in
  let membership_term = make_equal_term T [t] in
( Seq [membership_term; seq_term]
  THENL
  [Id
  ;I THENW (OnLastHyp Tac THEN Try (I THENW Thin (number_of_hyps p + 1)))
  ;Same [OnLastHyp (EOn t); OnLastHyp E] THEN Try Trivial
  ]
) p
;;


let LetBeThen id term type T p =
  GenThenUsingNew term type id (\i. T) p
;; 

let LetBe id term type = LetBeThen id term type Id ;; 

let GenThenUsing t T Tac p = 
  GenThenUsingNew t T (undeclared_id p `x`) Tac p ;;

let GenPseudoDeclThen i Tac p = 
  let [t],T = destruct_equal (type_of_hyp i p) in 
  GenThenUsing t T Tac p
;;

let GenThenNew t x Tac p = 
  GenThenUsingNew t (get_type p t) x Tac p ;;

let GenThen t Tac p = GenThenUsing t (get_type p t) Tac p ;; 

% The pattern starts with the first subgoal of the root of the proof of
the pattern theorem.
%
let Pattern pattern_thm_name terms choices ids i p =
  set_d_tactic_args i terms choices ids ;
  ApplyPattern (hd (children (proof_of_theorem pattern_thm_name))) p
;; 

let add_decl x A p =
  make_sequent (hyps p @ [make_declaration x A]) [] (concl p)
;; 

let DestructEq destructor i p =
( let z,b = destruct_lambda destructor ? failwith `DestructEq: not a lambda` in
  let equands, T = destruct_equal (h i p) in
  let x = undeclared_id p `x` in
  let T' = get_using_type (add_decl x T p) (substitute b [mvt z, mvt x]) in
  Assert (make_equal_term T' (map (make_apply_term destructor) equands))
  THENL [ApI (make_function_term x T T') THENL [EqI; Id]; Id]
) p
;; 

let DestructEqUsing destructor T i p =
( let z,b = destruct_lambda destructor ? failwith `DestructEq: not a lambda` in
  let equands, T'' = destruct_equal (h i p) in
  let x = undeclared_id p `x` in
  let T' = get_using_type (add_decl x T'' p) (substitute b [mvt z, mvt x]) in
  Assert (make_equal_term T' (map (make_apply_term destructor) equands))
  THENL [ApI (make_function_term x T T') THENL [EqI; Id]; Id]
) p
;; 

let ApplyToOcc (Tac: term->tactic) over_id over_term p =
( let a = snd (hd (match over_term (concl p) [over_id])) in
  let lemma = make_function_term over_id (get_type p a) over_term in
  Assert lemma 
  THENL [I THENW (\p. Tac (mvt (id_of_hyp (number_of_hyps p) p)) p)
        ;OnLastHyp (EOn a) THENS Trivial
        ]
) p
;; 

let SplitEq t p =
( let [t';t''],T = destruct_equal (concl p) in
  ParallelSeq [make_equal_term T [t';t]; make_equal_term T [t;t'']]
  THENL [Id; Id; Trivial]
) p
;; 


let SimpleETermUsingNew t T x p =
  let x = mvt x in
  let new_goal =
    if is_var_term t then substitute (concl p) [t, x]
    else replace_subterm t x (concl p)  in
  let seq_term =
    % All x:T. G[x/t] % 
		make_function_term (dv x) T new_goal in
( Assert seq_term
  THENL
  [I THENW OnLastHyp (\i. E i THEN Thin i)
  ;OnLastHyp (\i. EOn t i THENS Trivial THEN Thin i)
  ]
) p
;;

let SimpleETermUsing t T p = SimpleETermUsingNew t T (undeclared_id p `x`) p ;;

let SimpleETermNew t x p = SimpleETermUsingNew t (get_using_type p t) x p ;;

let SimpleETerm t p = SimpleETermUsing t (get_using_type p t) p ;; 
