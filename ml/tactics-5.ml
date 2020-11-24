%-*- Tab-Width: 2 -*-%




let RepeatProductE newids i p =
  let x,A = destruct_hyp i p  in
  let prod_ids = map fst (explode_product (fast_ap compute A))  in
  if length prod_ids < 2 then failwith `RepeatProductE: hyp not a product` ;
  letref newids = newids in
  let SetE newid i p =
    let x,A = destruct_hyp i p  in
    let z,(),() = destruct_set A in
    ( Refine (set_elim i big_U (newid z)) 
      THEN (if x=`NIL` then Thin i else Idtac) ) p in
  letref junk_hyps = [] in
  let ProdE id1 id2 i p = 
    junk_hyps := ( if (id_of_hyp i p)=`NIL` then i . junk_hyps 
                   else i . (number_of_hyps p + 3) . junk_hyps )
    ; Refine (product_elim i id1 id2) p  in
  
( if x=`NIL` then
    let newid id =
      if id = `NIL` then `NIL`
      else (let h.t=newids in newids := t ; h) ? undeclared_id p (fst_ch id)  in
    let Tacs = 
      map (\id. OnLastHyp (ProdE (newid id) `NIL`))
          (remove_last prod_ids)  in
    ComputeHyp i THEN MoveToEnd i THEN Every Tacs 
    THEN (Try o OnLastHyp) (SetE newid) THEN (\p. Thinning junk_hyps p)

  else
    let newid id = 
      (let h.t=newids in newids := t ; h) 
      ? undeclared_id p (if id=`NIL` then `x` else fst_ch id)  in
    let idn.idnm1.l = rev prod_ids  in
    let ids = rev l in  % prod_ids = ids@[idnm1;idn] %
    let LastProdE i p = ProdE (newid idnm1) (newid idn) i p in
    let Tac id i = ProdE (newid id) (undeclared_id p `p`) i  in 
    ComputeHyp i 
    THEN
    ( if length prod_ids = 2 then LastProdE i
      else Tac (hd ids) i THEN Every (map (OnNthLastHyp 2 o Tac) (tl ids))
           THEN OnNthLastHyp 2 LastProdE
    )
    THEN (\p. Thinning junk_hyps p) THEN (Try o OnLastHyp) (SetE newid) 
) p
;;


let make_projection tuple_length component_number t =
  let p1 t = 
    make_spread_term t (make_bound_id_term [`x`;`y`] (make_var_term `x`))
  and p2 t = 
    make_spread_term t (make_bound_id_term [`x`;`y`] (make_var_term `y`)) in
  letrec aux tl cn t =
    if cn = 1 then p1 t
    if tl = 2 & cn = 2 then p2 t
    else aux (tl-1) (cn-1) (p2 t)    in
  if component_number < 1 or component_number > tuple_length or tuple_length <2 
  then failwith `make_projection`
  else aux tuple_length component_number t
;;



letrec RepeatExtThen Tactic p =
  if is_function_term (fast_ap compute (concl_type p)) then
    ( ComputeConclType 
      THEN Refine (extensionality big_U [] (undeclared_id p `x`))
      THENM RepeatExtThen Tactic) p
  else Tactic p
;;





let is_arith_exp t =
  member_of_tok_list (term_kind t)
    [`ADDITION`; `MULTIPLICATION`; `SUBTRACTION`; `DIVISION`; 
          `MODULO`; `MINUS`; `NATURAL-NUMBER`]
;;

letrec is_arith_fmla t =
  if is_equal_term t then
    (let eqs,() = destruct_equal t in null (filter (\x. not is_arith_exp x) eqs))
  if is_less_term t then true
  if is_not_term t then is_arith_fmla (destruct_not t)
  else false
;;




let SetEForArith p =
  if not is_arith_fmla (concl p) then failwith `SetEForArith` 
  else
    reverse_iterate_fun
      (\T T'. T THENM T')
      (map (\i. IfThenOnHyp (\x,A. is_set_term (fast_ap compute A)) (E i) i)
           (filter (\x. not x=0)
                   (map (\x. find_declaration (destruct_var x) p)
                        (free_vars (concl p)))))
      p
;;






letrec do_analogy pattern goal =
  if is_refined pattern then
    TRY ( Refine (adjust_assum_number pattern goal)
          THENTRYL (map do_analogy (children pattern))
        ) goal
   else IDTAC goal
;;



letref saved_proof = void_goal_proof;;

let mark goal_proof = (saved_proof := copy_proof goal_proof; IDTAC goal_proof);;

let copy goal_proof =
  do_analogy saved_proof goal_proof;;



