%-*- Tab-Width: 2 -*-%

% Denote rec_ind by r in the following.  A "letrec" has the form
    letrec h(z) = b in t
and has definiens
    (\h. t) (\z. r(z;h,z.b))
%

let destruct_letrec u : tok#tok#term#term =
( let a,c = destruct_apply u in
  let h,t = destruct_lambda a in
  let z,d = destruct_lambda c in
  let z',e = destruct_simple_rec_ind d in
  if not dv z' = z then fail ;
  let [h';z''],b = destruct_bound_id e in
  if not (h'=h & z=z'') then fail
  else h,z,b,t  % SML patterns are for wimps.  %
) ? failwith `destruct_letrec`
;;

let make_letrec h z b t =
  instantiate_def `letrec` [mvt h; mvt z; b; t]
  ?
  make_apply_term
    (make_lambda_term h t)
    (make_lambda_term z
      (make_simple_rec_ind_term (mvt z) (make_bound_id_term [h;z] b)))
;;

let new_id_wrt_term t =
  let ids = map dv (free_vars t) in
  letrec new n =
    let x = `v`^(tok_of_int n) in
    if member x ids then new (n+1) else x in
  new 0
;;

let replace_all_instances t pattern pattern_ids (replace: term->term) =
  letrec aux t =
    if can (match pattern t) pattern_ids then replace t
    else map_on_subterms aux t in
  aux t
;;

% Denote the result by u,v,w.  u,v,w are tagged terms; u with tags erased is
t; v with tags erased is the result of computing (wrt tags) u; v and w compute
to the same term; and w with tags erased is the folded letrec.  u,v,w are intended
to be the "using" terms for 2 forward computation steps and one reverse.
The result will in any case be ugly, so all computations are fast_ap'd. 
%
let tagged_terms_for_letrec_unfold t : term#term#term =
  let h,(),(),() = 
    destruct_letrec t 
    ? failwith `tagged_terms_for_letrec_fold: not a letrec`  in
  let u = make_tagged_term 1 t in
  let h' = snd (destruct_apply t) in
  let v' = fast_ap do_computations u in
  let newid = new_id_wrt_term h' in
  let ap_pattern = make_apply_term h' (mvt newid) in
  let v = replace_all_instances v' ap_pattern [newid] (make_tagged_term 2) in
  let w' = fast_ap do_computations v in
  let w = 
    make_tagged_term 1 
      (make_apply_term (make_lambda_term h (replace_subterm h' (mvt h) w'))
                       h'
      ) in 
  if not fast_ap do_computations w = w' then
    failwith `tagged_terms_for_letrec_fold: capture problem?`
  else u,v,w 
;;


let add_letrec_def u =
  let h,z,b,t = destruct_letrec u in
  `letrec`, [mvt h; mvt z; b; t]
;;

%add_def_adder `letrec` add_letrec_def ;;%

let BringTyping i p =
( let x,A = destruct_hyp i p in
  if member i (hidden p) then failwith `BringTyping: hyp is hidden.` 
  if is_equal_term A then
  ( let x = undeclared_id p `x` in
    let c = replace_subterm (first_equand A) (mvt x) (concl p) in
    Assert (make_function_term x (eq_type A) c)
    THENL [Id; OnLastHyp (EOn (first_equand A)) THEN Trivial]
  )
  if x=`NIL` then failwith `BringTyping: hyp not a typing.`
  else BringHyps [i]
) p
;; 

let AssertTypingThen t T p =
( Assert (make_equal_term (get_type p t) [t])
  THENL [Id; T]
) p
;; 

let SameTypeMod ConclBeater HypBeater p =
( let [t],T = destruct_equal (concl p) in
  AssertTypingThen t (OnLastHyp HypBeater THENS (ConclBeater THEN Trivial))
) p
;; 

let SameTypeModEval = SameTypeMod EvalConcl EvalHyp ;; 

let ShrinkEqType T' p =
  if is_membership_goal p then failwith `ShrinkEqType: only applies to equalities`
  else let [t;t'],T = destruct_equal (concl p) in
       SubstFor (make_equal_term T' [t;t']) p
;; 


% t ---> (ˆx.t)(x) %
let trivially_abstract x t =
  make_apply_term (make_lambda_term x t) (mvt x)
;;

% x:A#B ---> x:A#[[1;(ˆx.B)(x)]]  and similarly for x:A->B. %
let abstract_and_tag_top_type t =
  let abs x t = make_tagged_term 1 (trivially_abstract x t) in
  ( let x,A,B = destruct_product t in
    if x = `NIL` then t
    else make_product_term x A (abs x B)
  )
  ?
  ( let x,A,B = destruct_set t in
    if x = `NIL` then t
    else make_set_term x A (abs x B)
  )
  ?
  ( let x,A,B = destruct_function t in
    if x = `NIL` then t
    else make_function_term x A (abs x B)
  )
  ? failwith `abstract_and_tag_top_type`
;;

let map_on_member f t = 
  let [a],T = destruct_equal t in
  make_equal_term T [f a]
;;

let check_all_objects kind =
  map (\x. if object_kind x = kind then
              execute_command `check` [x])
      (library ())
;;

let check_all_objects_in_range first last kind =
  let m = first = `first` => 1 | find_position first (library()) in
  let n = last = `last` => length (library()) 
                        |  find_position last (library()) in
  map (\x. if object_kind x = kind then
              execute_command `check` [x])
      (firstn (n-m) (nthcdr (m-1) (library())))
;; 

let number_of_occurrences_in_proofs lib_start lib_end (P: proof -> bool) =
  let a = if lib_start=`first` then hd (library()) else lib_start in
  let b = if lib_end=`last` then last (library()) else lib_end in
  let lib_tail = nthcdr (find_position a (library()) - 1) (library()) in
  let lib_hunk = 
    filter ($= `THM` o object_kind)
           (firstn (find_position b lib_tail) lib_tail) in
  letrec aux p = 
    (if P p then 1 else 0) + accumulate $+ 0 (map aux (children p) ? []) in
  map (\x. x, aux (proof_of_theorem x)) lib_hunk
;; 


let CanonicalI = IfThenOnConcl is_canonical_type I ;;

% No thinning. %
letrec FastRepeatAndE i p =
  if is_and_term (h i p) then 
    (E i THEN OnLastHyp FastRepeatAndE THEN OnNthLastHyp 2 FastRepeatAndE) p
  else Id p
;; 

let Unhide p =
( CC THEN (IfOnConcl is_squash_term Id Fail) THEN
  ExplicitI make_axiom_term THEN UnSquash THEN 
  Assert (concl p) THENL 
  [Id; OnLastHyp E THEN SetElementI THEN Try Trivial THEN Repeat EqI]
) p
;; 

let CanonicalEqI =
  IfOnConcl (is_canonical_term o first_equand) EqI Fail
;; 

let ApplyMembershipThm namer p =
  Lemma (namer (destruct_term_of_theorem 
                  (head_of_application (first_equand (concl p)))))
        p
;; 

let TryMembershipThm namer p =
  let name = namer (destruct_term_of_theorem 
                     (head_of_application (first_equand (concl p)))) in
  if member name (library()) then Try (Lemma name) p else fail
;; 

let is_true_type = 
  $= (make_equal_term make_int_term [make_integer_term 0]) 
;; 

let is_failure_type t = 
  is_true_type (snd (destruct_union t)) ? false
;; 

  
let AssumeUsing T extra_terms p =
  let name, terms = 
    first_value 
      (\name. name, match_part_in_context (fst o destruct_union)
                      (main_goal_of_theorem name) T p extra_terms)
      (current_Assume_additions()) in
( InstantiateLemma name terms THENS
  OnLastHyp (\i. IfOnHyp (is_union_term o snd)
                    (E i THEN Thin i 
                         THEN OnLastHyp (\i. IfThenOnHyp (is_true_type o snd) (Thin i) i)) 
                    (\p. failwith `Assume`)
                    i
            )
) p
;; 

let Assume T p = AssumeUsing T [] p ;; 


let ChainSeqWithEq equands eq_type p =

  (	if length equands < 2 then failwith `ChainSeqWithEq` ;
	let chain = 
		map
		  (\s,t. make_equal_term eq_type [s;t])
		  ( (remove_last equands) 
		    com 
	 	    (tl equands)
		  )	in
	let m = length equands 	in
	let n = number_of_hyps p	in
	let final_relate = 
		make_equal_term eq_type [hd equands; last equands] 	in

	Seq (chain @ [final_relate])
	THENL
	build_list [m-1, ThinToEnd (n+1)
		   ;1,   Refine equality
		   ;1,   \p. Thinning (upto (n+1) (number_of_hyps p - 1)) p
		   ]

  ) p

;;



let LemmaEUsing name term_to_elim inst_terms =
  AbstractConcl term_to_elim THEN
  LemmaUsing name inst_terms THENM
  ReduceConcl
;; 

let LemmaE name term_to_elim = 
  LemmaEUsing name term_to_elim []
;; 

let SimpleI = IfOnConcl is_squash_term Fail I ;; 


let InstLemma = InstantiateLemma ;;
let InstHyp = InstantiateHyp ;; 