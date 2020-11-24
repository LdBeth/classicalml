
let list_subterms term =
  if member (term_kind term)
        ``UNIVERSE VOID ATOM TOKEN INT NATURAL-NUMBER NIL VAR AXIOM TERM-OF-THEOREM`` then
    []
  if is_any_term term then
    [destruct_any term]
  if is_minus_term term then
    [destruct_minus term]
  if is_addition_term term then
    pair_to_list (destruct_addition term)
  if is_subtraction_term term then
    pair_to_list (destruct_subtraction term)
  if is_multiplication_term term then
    pair_to_list (destruct_multiplication term)
  if is_division_term term then
    pair_to_list (destruct_division term)
  if is_modulo_term term then
    pair_to_list (destruct_modulo term)
  if is_integer_induction_term term then
    quad_to_list (destruct_integer_induction term)
  if is_list_term term then
    [destruct_list term]
  if is_cons_term term then
    pair_to_list (destruct_cons term)
  if is_list_induction_term term then
    triple_to_list (destruct_list_induction term)
  if is_union_term term then
    pair_to_list (destruct_union term)
  if is_inl_term term then
    [destruct_inl term]
  if is_inr_term term then
    [destruct_inr term]
  if is_decide_term term then
    triple_to_list (destruct_decide term)
  if is_product_term term then
    (make_var_term (fst (destruct_product term))) .
         (pair_to_list (snd (destruct_product term)))
  if is_pair_term term then
    pair_to_list (destruct_pair term)
  if is_spread_term term then
    pair_to_list (destruct_spread term)
  if is_function_term term then
    (make_var_term (fst (destruct_function term))) .
        (pair_to_list (snd (destruct_function term)))
  if is_lambda_term term then
    [(make_var_term (fst (destruct_lambda term))); (snd (destruct_lambda term))]
  if is_apply_term term then
    pair_to_list (destruct_apply term)
  if is_partial_function_term term then
   (let id,left,right = destruct_partial_function term in
      [(make_var_term id); left; right])
  if is_apply_partial_term term then
     pair_to_list (destruct_apply_partial term)
  if is_fix_term term then
     (let ids,terms,fix_id = destruct_fix term in
	(map make_var_term ids) @ terms)
  if is_dom_term term then
     [destruct_dom term]
  if is_quotient_term term then
    (let id1,id2,terms = destruct_quotient term in
      (make_var_term id1) .
        ((make_var_term id2) . (pair_to_list terms)))
  if is_set_term term then
    (let id , terms = destruct_set term in
      (make_var_term id) . (pair_to_list terms))
  if is_equal_term term then
    (let terms,type = (destruct_equal term) in
      terms @ [type]  )
  if is_less_term term then
    pair_to_list (destruct_less term)
  if is_bound_id_term term then
    (let bound_ids,type = (destruct_bound_id term) in
        (map make_var_term bound_ids) @ [type])
  if is_bound_id_list_term term then
    (let bound_ids, terms = (destruct_bound_id_list term) in
	(map make_var_term bound_ids) @ terms )
  if is_atom_eq_term  term then
    quad_to_list (destruct_atomeq term)
  if is_int_eq_term term then
    quad_to_list (destruct_inteq term)
  if is_intless_term term then
    quad_to_list (destruct_intless term)
  if is_rec_term term then
    (( let ids,terms,fix_term,id,value = destruct_rec term in
	(map make_var_term ids) @ terms @ [fix_term; value]
    ) ?
    ( let ids,terms,id,value = destruct_rec_without_fix term in
	 (map make_var_term ids) @ terms @ [value]
    ))
  if is_rec_ind_term term then
    (let arg,ids,terms,id = destruct_rec_ind term in
       arg . (map make_var_term ids) @ terms)
  if is_simple_rec_term term then
    (let id,term = destruct_simple_rec term in
       [(make_var_term id); term])
  if is_simple_rec_ind_term term then
    pair_to_list (destruct_simple_rec_ind term)
  else 
    failwith `list_subterms:  No case for this term-kind`;;



% takes a triple, token, term, term and collects up all the tokens in a list.%

letrec  tok_term_term_to_toks arg =
      fst arg .( (list_identifiers (fst (snd arg))) @
                 (list_identifiers (snd (snd arg)))
               )


and identifiers_of_subterms subterms = 
  if subterms = [] then
    []
  else 
    list_identifiers (hd subterms) @ (identifiers_of_subterms (tl subterms))

and list_identifiers term =
  if is_var_term term then
    [destruct_var term]
  if is_product_term term then
    tok_term_term_to_toks (destruct_product term) 
  if is_function_term term then
    tok_term_term_to_toks (destruct_function term)
  if is_partial_function_term term then
    tok_term_term_to_toks (destruct_partial_function term)
  if is_fix_term term then
    (let ids,terms,id = destruct_fix term in
       ids @ (identifiers_of_subterms terms))
  if is_rec_term term then
    ((let ids,terms,fix_term,id,value = destruct_rec term in
	ids @ (identifiers_of_subterms terms) @
	   (list_identifiers fix_term) @ (list_identifiers value)	
    ) ?
    (let ids,terms,id,value = destruct_rec_without_fix term in
	ids @ (identifiers_of_subterms terms) @ (list_identifiers value)
    ))
  if is_rec_ind_term term then
    (let arg,ids,terms,id = destruct_rec_ind term in
	(list_identifiers arg) @ ids @ (identifiers_of_subterms terms))
  if is_simple_rec_term term then
    (let id,subterm = destruct_simple_rec term in
	id . (list_identifiers subterm))
  if is_quotient_term term then
    (fst (destruct_quotient term)) . (tok_term_term_to_toks 
                                        (snd (destruct_quotient term)))
  if is_set_term term then
    tok_term_term_to_toks (destruct_set term)
  if is_bound_id_term term then
    (fst (destruct_bound_id term)) @ (list_identifiers (snd (destruct_bound_id term)))
  if is_bound_id_list_term term then
    (let ids,terms = destruct_bound_id_list term in
	ids @ (identifiers_of_subterms terms))
  else
    identifiers_of_subterms (list_subterms term);;



%%
% UNIFICATION %
%%


let is_meta_variable var =
  if is_var_term var &
     hd (explode (destruct_var var)) = `_`  then        % first char is underscore %
    true
  else
    false;;

let occurs_check term1 term2 =
  if not member (destruct_var term1) (list_identifiers term2) then
    false
  else 
    failwith `occurs_check`;;


let resolve_atoms term1 term2 =
  if term1=term2 then
    nil
  if is_meta_variable term1 then
    (occurs_check term1 term2; [term1, term2])
  if is_meta_variable term2 then                
    (occurs_check term2 term1; [term2, term1])
  else failwith `unify: different atoms`;;


letrec sub_in_list terms sub =
  if null terms then
    nil
  else 
    substitute (hd terms) sub . (sub_in_list (tl terms) sub);;

letrec map_unify subterms1 subterms2 =
  (if (null subterms1) or (null subterms2) then
    if (null subterms1) & (null subterms2) then
      nil      
    else
      failwith `unify: different length sub-term lists.`
  else 
    let sub = unify (hd subterms1) (hd subterms2) in
      let rest1 = sub_in_list (tl subterms1) sub and
          rest2 = sub_in_list (tl subterms2) sub in
      sub @
        (map_unify rest1 rest2)
  )
and unify term1 term2  =
  let subterms1, subterms2 = list_subterms term1, list_subterms term2 in
    if (null subterms1) or (null subterms2) then
      (resolve_atoms term1 term2)
    if term_kind term1 = term_kind term2 then
      map_unify  subterms1 subterms2
    else
      failwith `unify: different term kinds`;;
