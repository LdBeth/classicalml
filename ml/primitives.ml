


% The following package gives back-trace information upon failure %

letref trace_failure = false;;
letref fail_list = []:bool list;;

%let fail = 
  if trace_failure then
    (fail_list := (`FAIL` . fail_list);
     break
    )
  else 
    break;;   NOT YET

let failwith tok =
  if trace_failure then
    (fail_list := (tok . fail_list);
     breakwith tok
    )
  else 
    breakwith tok;;
%

%Interface to Prl Rule Parser%
  %This is a tactic that applies the rule described by the  %
  %token provided, in the context of the goal being refined.%

let refine_using_prl_rule rule_token proof =
    (refine (parse_rule_in_context rule_token proof)) proof;;


%Predicates on terms.%

let is_axiom_term term =
  ((term_kind term) = `AXIOM`);;

let is_universe_term (term) = 
  ((term_kind term) = `UNIVERSE`);;

let is_void_term (term) =
  ((term_kind term) = `VOID`);;

let is_any_term (term) = 
  ((term_kind term) = `ANY`);;

let is_atom_term (term) =
  ((term_kind term) = `ATOM`);;

let is_token_term (term) =
  ((term_kind term) = `TOKEN`);;

let is_int_term (term) =
  ((term_kind term) = `INT`);;

let is_natural_number_term (term) =
  ((term_kind term) = `NATURAL-NUMBER`);;

let is_minus_term (term) =
  ((term_kind term) = `MINUS`);;

let is_addition_term (term) = 
  ((term_kind term) = `ADDITION`);;

let is_subtraction_term (term) =
  ((term_kind term) = `SUBTRACTION`);;

let is_multiplication_term (term) =
  ((term_kind term) = `MULTIPLICATION`);;

let is_division_term (term) =
  ((term_kind term) = `DIVISION`);;

let is_modulo_term (term) =
  ((term_kind term) = `MODULO`);;

let is_integer_induction_term (term) =
  ((term_kind term) = `INTEGER-INDUCTION`);;

let is_list_term (term) =
  ((term_kind term) = `LIST`);;

let is_nil_term (term) =
  ((term_kind term) = `NIL`);;

let is_cons_term (term) =
  ((term_kind term) = `CONS`);;

let is_list_induction_term (term) =
  ((term_kind term) = `LIST-INDUCTION`);;

let is_union_term (term) =
  ((term_kind term) = `UNION`);;

let is_inl_term (term) =
  ((term_kind term) = `INL`);;

let is_inr_term (term) =
  ((term_kind term) = `INR`);;

let is_decide_term (term) =
  ((term_kind term) = `DECIDE`);;

let is_product_term (term) =
  ((term_kind term) = `PRODUCT`);;

let is_pair_term (term) =
  ((term_kind term) = `PAIR`);;

let is_spread_term (term) =
  ((term_kind term) = `SPREAD`);;

let is_function_term (term) =
  ((term_kind term) = `FUNCTION`);;

let is_lambda_term (term) =
  ((term_kind term) = `LAMBDA`);;

let is_apply_term (term) =
  ((term_kind term) = `APPLY`);;

let is_partial_function_term term = ((term_kind term) = `PARFUNCTION`);;

let is_apply_partial_term term = ((term_kind term) = `APPLY-PARTIAL`);;

let is_fix_term term = ((term_kind term) = `FIX`);;

let is_dom_term term = ((term_kind term) = `DOM`);;

let is_quotient_term (term) =
  ((term_kind term) = `QUOTIENT`);;

let is_set_term (term) =
  ((term_kind term) = `SET`);;

let is_equal_term (term) =   %poor name choice%
  ((term_kind term) = `EQUAL`);;

let is_less_term (term) =
  ((term_kind term) = `LESS`);;

let is_var_term (term) =
  ((term_kind term) = `VAR`);;

let is_variable_term (term) =
  ((term_kind term) = `VAR`);;

let is_bound_id_term (term) =
  ((term_kind term) = `BOUND-ID-TERM`);;

let is_bound_id_list_term (term) =
  ((term_kind term) = `BOUND-ID-LIST`);;

let is_term_of_theorem_term (term) =
  ((term_kind term) = `TERM-OF-THEOREM`);;

let is_atom_eq_term (term) =
  ((term_kind term) = `ATOMEQ`);;

let is_int_eq_term (term) =
  ((term_kind term) = `INTEQ`);;

let is_intless_term (term) = 
  ((term_kind term) = `INTLESS`);;

let is_rec_term (term) =
  ((term_kind term) = `RECURSIVE`);;

let is_rec_ind_term (term) =
  ((term_kind term) = `REC-IND`);;

let is_simple_rec_ind_term (term) =
  ((term_kind term) = `SIMPLE-REC-IND`);;

let is_simple_rec_term (term) =
  ((term_kind term) = `SIMPLE-REC`);;

let is_tagged_term (term) =
  ((term_kind term) = `TAGGED`);;



let type_of_declaration decl = snd (destruct_declaration decl);;


let id_of_declaration decl = fst (destruct_declaration decl);;
 


let make_addition_term = make_binary_term `ADD`;;

let make_subtraction_term = make_binary_term `SUB`;;

let make_multiplication_term = make_binary_term `MUL`;;

let make_division_term = make_binary_term `DIV`;;

let make_modulo_term = make_binary_term `MOD`;;


% return the term of a declaration %

let term_of_declaration decl =
  snd (destruct_declaration decl);;


let is_refined goal =
  ((refinement goal);true)?false;;
