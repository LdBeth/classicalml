%-*- Tab-Width: 2 -*-%
let is_arith_eq t = 
  (exists is_arith_exp (fst (destruct_equal t)))
  ? false
;;

let is_arith_eq_goal p = is_arith_eq (concl p) ;;

letrec is_arith_literal t =
  is_less_term t
  or ( (let ().().(),T = destruct_equal t in T = make_int_term) ? false) 
  or ( is_arith_literal (destruct_not t) ? false )
;;


let is_arith_concl c =
  all (\t. is_arith_literal t or is_void_term t) (destruct_disjunction c)
;;

let can_beat_to_arith_goal p =
  let c = concl p in
  all is_arith_concl (destruct_conjunction c)
  or (  let ().().(),T = destruct_equal c in is_set_term (fake_compute_ap T)
     ) ? false
;;

%$%

let member_i_may_introduce_squash p =
( let t = first_equand (concl p) in
  is_function_term t or is_product_term t 
  or is_lambda_term t or is_pair_term t
) ? false
;; 


let tag_eq_type n t =
  let l,T = destruct_equal t in
  make_equal_term (make_tagged_term n T) l
;;

let ComputeConclUniverse  =
  FastAp 
  (ComputeConclUsing
    (\t. if is_constant_indexed_universe_term (eq_type t) 
         then tag_eq_type 0 t else fail))
;; 

let TryCumulativity p =
  let (t.tl),T = destruct_equal (concl p) in
  if not is_gen_universe_term T then failwith `TryCumulativity`
  else Cumulativity (get_type p t) p
;;

let totalify (f:*->bool) (x:*) =  f x ? false ;;


let ReclessMemberI =

  Eq ORELSE ReduceEquandicity ORELSE TryCumulativity ORELSE

  (\p. First (current_member_i_additions ()) p) ORELSE

  ( %ReduceConcl
  
    THEN %  

    (\ p .
      ( let (t.tl),T = destruct_equal (concl p)  in
        if exists (\x. not term_kind x = term_kind t) tl then fail ;
        let type = fast_ap compute T  in  

%       if is_gen_universe_term T 
           & totalify (\t. get_type p t = make_universe_term 1) t
           & can (Cumulativity (make_universe_term 1)) p
        then Cumulativity (make_universe_term 1)
% 
        if is_apply_term t 
            & (is_set_term T 
                or (is_set_term type & (not T = get_type p t ? false))) then
          ComputeConclType THEN SetElementI
  
        if almost_poly_defined_term t then PolyMember
  
        if is_apply_term t & is_simple_rec_term T then RecElementI

        if is_apply_term t & is_quotient_term type then
          Refine (quotient_equality_element big_U)

        if is_any_term t then EqI 
  
        if is_canonical_term t then
          ComputeConclType
          THEN
          ( if is_set_term type then SetElementI
            if is_quotient_term type then Refine (quotient_equality_element big_U)
            if is_simple_rec_term type then failwith `rec`
            else EqI 
          )
  
        if is_int_exp t & not is_int_term T then
          ComputeConclType
          THEN SetElementI
          THENM Try (Refine (arith big_U))
  
        if is_noncanonical_term t then EqI
  
        if is_term_of_theorem_term t then
          ( Refine (def (destruct_term_of_theorem t) `nil`)
            THEN
            ( Refine equality
              ORELSE
              FastAp (Inclusion (number_of_hyps p + 1))
            )
          )
  
        if is_var_term t then
          SetElementI
          ORELSE
          FastAp (Inclusion (find_declaration (destruct_var t) p))
  
        else failwith `MemberI: missing case`
  
      ) p 
    )
  )
;;


let MemberI = 
  If member_i_may_introduce_squash
  ((\p. ReclessMemberI p ?? [`rec`] RecMemberI p) 
   THEN Try (OnLastHyp SquashE)
  )
  (\p. ReclessMemberI p ?? [`rec`] RecMemberI p)
;; 

let MemberIntro = MemberI ;;

let Member =
  Try Eq 
  THEN ReduceConcl THEN Try Eq THEN
  IfThenOnConcl
    (\c. length (equands c) = 1 
         or ( let t.t'.() = equands c  in 
              fast_ap (fst o no_extraction_compute) t 
              = fast_ap (fst o no_extraction_compute) t'
            )
    )
    (RepeatUntil
      (\p.
        ( let t = 
            (fst o (fast_ap no_extraction_compute) o first_equand o concl) p in
          is_list_induction_term t 
          or is_integer_induction_term t
          or is_rec_ind_term t
        ) ? false
      )
      MemberI
    )
;; 


let StrongMember = Repeat MemberI ;;

let BashArithGoal =
  let Aux =
    IfThenOnConcl is_equal_term 
                  (SameModI (equands o concl) [SetElementI; Arith])
    ORELSE (Repeat I THENW Arith) in
  If can_beat_to_arith_goal (Aux ORELSE (Unsetify THENS Aux)) Fail
;; 


let ApplyPolyMemberLemma =
 (\p. let [t],T = destruct_equal (concl p) in
      assert almost_poly_defined_term t ;
      (Lemma o append_underscore o destruct_term_of_theorem 
         o hd o decompose_ap) 
      t p)
;;

let Autotactic =
    (Repeat
      ( Trivial
        ORELSE (Progress (OnEveryHyp RepeatAndE) THEN Try Trivial)
        ORELSE (UnSquash THEN Try Trivial)
        ORELSE Member
        ORELSE BashArithGoal
        ORELSE (I THEN Try Trivial)
        ORELSE (\p. 
                let [t;t'],T = destruct_equal (concl p) in
                if is_universe_term T & simplify t = simplify t' then
                  (RepeatUntil is_arith_eq_goal MemberI THEN Try Trivial) p
                else fail
               )
        ORELSE ApplyPolyMemberLemma
        ORELSE (\p. First (current_autotactic_additions ()) p)
      )
    )
;;



% The previous ORELSE has a PROGRESS check.  This was a very bad idea. %
ml_curried_infix `REAL_ORELSE` ;; 
let $REAL_ORELSE (f1:tactic) (f2:tactic) (g:proof) = f1 g ? f2 g ;; 

let ReclessWeakMemberI =

  Eq ORELSE ReduceEquandicity ORELSE TryCumulativity ORELSE

  (\p. First (current_member_i_additions ()) p) REAL_ORELSE

  ( %ReduceConcl
  
    THEN %  

    (\ p .
      ( let (t.tl),T = destruct_equal (concl p)  in
        if exists (\x. not term_kind x = term_kind t) tl then fail ;
        let type = fast_ap compute T  in  

%       if is_gen_universe_term T 
           & totalify (\t. get_type p t = make_universe_term 1) t
           & can (Cumulativity (make_universe_term 1)) p
        then Cumulativity (make_universe_term 1)
% 
        if is_apply_term t & is_set_term T then SetElementI

        if is_apply_term t & is_set_term type & (can (get_type p) t)
        then (if almost_poly_defined_term t then PolyMember else EqI)
             ORELSE (ComputeConclType THEN SetElementI)
  
        if almost_poly_defined_term t then PolyMember
  
        if is_apply_term t & is_simple_rec_term T then RecElementI

        if is_apply_term t & is_quotient_term type then
          Refine (quotient_equality_element big_U)

        if is_any_term t then EqI 
  
        if is_canonical_term t then
          ComputeConclType
          THEN
          ( if is_set_term type then SetElementI
            if is_quotient_term type then Refine (quotient_equality_element big_U)
            if is_simple_rec_term type then failwith `rec`
            else EqI 
          )
  
        if is_int_exp t & not is_int_term T then
          ComputeConclType
          THEN SetElementI
          THENM Try (Refine (arith big_U))
  
        if is_noncanonical_term t then EqI
  
        if is_term_of_theorem_term t then
          ( Refine (def (destruct_term_of_theorem t) `nil`)
            THEN
            ( Refine equality
              ORELSE
              FastAp (Inclusion (number_of_hyps p + 1))
            )
          )
  
        if is_var_term t then
          IfOnConcl (is_set_term o eq_type) SetElementI
            (FastAp (Inclusion (find_declaration (destruct_var t) p)))
  
        else failwith `WeakMemberI: missing case`
  
      ) p 
    )
  )
;;

let WeakMemberI = 
  If member_i_may_introduce_squash
  ((\p. ReclessWeakMemberI p ?? [`rec`] RecMemberI p) 
   THEN Try (OnLastHyp SquashE)
  )
  (\p. ReclessWeakMemberI p ?? [`rec`] RecMemberI p)
;; 


let WeakMemberIntro = WeakMemberI ;;

let WeakMember p =
( Try Eq 
  THEN ReduceConcl THEN Try Eq THEN
  IfThenOnConcl
    (\c. length (equands c) = 1 
         or ( let t.t'.() = equands c  in 
              fast_ap (fst o no_extraction_compute) t 
              = fast_ap (fst o no_extraction_compute) t'
            )
    )
    (RepeatUntil
       (\p.
         ( let t = 
             (fst o (fast_ap no_extraction_compute) o first_equand o concl) p in
           is_list_induction_term t 
           or is_integer_induction_term t
           or is_rec_ind_term t
           or almost_poly_defined_term t
           or is_set_term (eq_type (concl p))
         ) ? false
       )
       WeakMemberI
     THEN Try (\p. if (almost_poly_defined_term o first_equand o concl) p 
                      or (is_set_term o eq_type o concl) p
                   then WeakMemberI p else fail)
    )
) p
;; 



let WeakAutotactic =
    (Repeat
      ( Trivial
        ORELSE (Progress (OnEveryHyp RepeatAndE) THEN Try Trivial)
        ORELSE (UnSquash THEN Try Trivial)
        ORELSE WeakMember
        ORELSE BashArithGoal
        ORELSE (IfOnConcl is_canonical_type (I THEN Try Trivial) Fail)
        ORELSE (\p. 
                let [t;t'],T = destruct_equal (concl p) in
                if is_universe_term T & simplify t = simplify t' then
                  (RepeatUntil is_arith_eq_goal WeakMemberI THEN Try Trivial) p
                else fail
               )
        ORELSE ApplyPolyMemberLemma
        ORELSE (\p. First (current_autotactic_additions ()) p)
      )
    )
;;



let StrongAutotactic =

  Repeat
  ( Autotactic THEN MemberI )
;;

%$%
let lib_dump name =
  execute_command_line
    (`dump `^`BEGIN_`^name^`-`^`END_`^name^` to dougprl:lib;`^name)
;;

let lib_load_bot fname =
  execute_command_line (`load bot from dougprl:lib;`^fname) 
;;

%$%

let WfLemma name p = 
  if not is_gen_universe_term (concl_type p) then failwith `WfLemma`
  else Lemma name p
;;

let Graft p p' = Idtac p ;; 


let Mark name p = 
 add_saved_proof name (copy_proof p); Id p
;; 

let Copy name p =
  saved_proof := get_saved_proof name ;
  copy p
;; 


let CompleteAutotactic =
  IfThen ($not o is_membership_goal) (Complete Autotactic)
  THEN Complete Autotactic
;; 


let CompleteWeakAutotactic =
  IfThen ($not o is_membership_goal) (Complete WeakAutotactic)
  THEN Complete WeakAutotactic
;; 


let add_membership_mono_lemma_to_inclusion lemma_name eq_type_ext_name =
  add_to_inclusion lemma_name
    (\i. IfOnConcl ($= eq_type_ext_name o ext_name o eq_type)
          (BringTyping i THEN Lemma lemma_name THEN CompleteWeakAutotactic)
          Fail
    )
;; 

let set_strong () = set_auto_tactic `refine (tactic \`StrongAutotactic\`)` ;;

letref autotactic_string = `WeakAutotactic` ;; 

let set () = set_auto_tactic (`refine (tactic \`` ^ autotactic_string ^ `\`)`) ;;

let unset () = set_auto_tactic `Idtac` ;;

set () ;;

