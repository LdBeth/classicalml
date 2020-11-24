let max x y =
  if x>y then x else y;;
      
%Returns the max of a list.  Will fail if applies to empty list.%
letrec list_max list =
    let first = hd list and
        rest  = tl list in
      if rest = [] then
        first
      else
        max first (list_max rest);;

let pair_to_list pair =
  [fst pair; (snd pair)];;

let triple_to_list triple =
  fst triple . (pair_to_list (snd triple));;

let quad_to_list quad =
  fst quad . (triple_to_list (snd quad));;


let list_subterms term =
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
    pair_to_list (snd (destruct_product term))
  if is_pair_term term then
    pair_to_list (destruct_pair term)
  if is_spread_term term then
    pair_to_list (destruct_spread term)
  if is_function_term term then
    pair_to_list (snd (destruct_function term))
  if is_lambda_term term then
    [snd (destruct_lambda term)]
  if is_apply_term term then
    pair_to_list (destruct_apply term)
  if is_quotient_term term then
    pair_to_list (snd (snd (destruct_quotient term)))
  if is_set_term term then
    pair_to_list (snd (destruct_set term))
  if is_equal_term term then
    (let pair = (destruct_equal term) in
      snd pair . (fst pair))           %hd is a list%	
  if is_less_term term then
    pair_to_list (destruct_less term)
  if is_bound_id_term term then
    [snd (destruct_bound_id term)]
  if is_atomeq_term  term then
    quad_to_list (destruct_atomeq term)
  if is_inteq_term term then
    quad_to_list (destruct_inteq term)
  if is_intless_term term then
    quad_to_list (destruct_intless term)
  else 
    [];;

letrec max_universe term =
  if is_universe_term term then
    destruct_universe term
  else
    list_max (-1.(map max_universe (list_subterms term)));;
