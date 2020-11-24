
% Find the maximum universe used so far %

letrec max_universe term =
  if is_universe_term term then
    destruct_universe term
  else
    list_max (0 . (map max_universe (list_subterms term)));;

let max_universe_for_hyp decl =
  let type = type_of_declaration decl in
    if is_equal_term type then
      0                       % skip equalities %
    else
      max_universe type;;

%return a guess at what the next universe should be.  This is the current%
%maximum universe that occurs in the conclusion or any non-equality      %
%hypothesis plus 1 %

let next_universe proof_tree =
  list_max 
   (max_universe (conclusion proof_tree).
    (map max_universe_for_hyp (hypotheses proof_tree))
   )  + 1;;
 


%The next three functions are used to generate new variable names. %
% The greates current variable of the form v### is found, and a new%
% variable, one greater.                                           %

let number_of_new_identifier tok =
  if hd (explode tok) = `v` then
    (int_of_tok (implode (tl (explode tok))) ? -1)  %will fail if not integer%
  else 
    -1;;

% Returns the max number of "v###" variable in use in the term.  If none, then%
% returns -1%

let max_new_identifier_in_term term =
  (list_max (-1. (map number_of_new_identifier (list_identifiers term))));;



let max_new_identifier proof =
  letref max_num = max_new_identifier_in_term (conclusion proof) and
    hyplist = hypotheses proof in
      if (null hyplist) then max_num
      loop
        (let possible_max = max (number_of_new_identifier (id_of_declaration (hd hyplist)))
                           (max_new_identifier_in_term (term_of_declaration (hd hyplist))) in
         if possible_max > max_num then (max_num := possible_max;());
         hyplist := tl hyplist
        );;



let new_id proof = 
  if not new_id_initialized then
    (new_id_initialized := true;
     new_id_count := max_new_identifier proof;
     ());
  new_id_count := new_id_count + 1;
  implode (`v` . explode (tok_of_int new_id_count));;



%    Map-hypothesis  %

letrec try_each_hyp failure_message tac hyp_list hyp_num ptree =
  if null hyp_list then
    failwith failure_message
  else
    ((tac (hd hyp_list) hyp_num ptree) 
        ?(try_each_hyp failure_message tac (tl hyp_list) (hyp_num+1) ptree));;

let map_hyp failure_message hyp_tactic ptree =
  try_each_hyp failure_message hyp_tactic (hypotheses ptree) 1 ptree;;

%%
% Hypothesis tactic %
%%

% This searches for identical hypotheses or void. %

let try_hyp current_hyp hyp_number ptree =
  let type = type_of_declaration current_hyp in
    if is_void_term type then
      refine (void_elim hyp_number) ptree
    if type = (conclusion ptree) then
      refine (hyp hyp_number) ptree
    else
      failwith `try_hyp`;;

let hypothesis = map_hyp `hypothesis` try_hyp;;








let get_term_in_type proof =
  let goal = conclusion proof in
    let terms = fst (destruct_equal goal)
    and type = snd (destruct_equal goal) in
        ((hd terms),type);;

let try_set_elim left right current_hyp hyp_number proof =
  let id,type = destruct_declaration current_hyp in
    if right = fst (snd (destruct_set type)) &     % is the type the base type? %
      (left=(make_var_term id) or (member left (fst (destruct_equal type)))) then
        refine (set_elim  hyp_number (next_universe proof) (new_id proof)) proof
    else
      failwith `try_set_elim`;;


let set_elim_for_base proof =
  let left,right = get_term_in_type proof in
    map_hyp `set_elim_for_base` (try_set_elim left right) proof;;

% This function looks for a situation like x:U7 where the goal is >>x in U10. %

let try_id_cum id universe current_hyp hyp_number =
  let left,right = destruct_declaration current_hyp in
    if (make_var_term left) = id & 
       (destruct_universe right)<(destruct_universe universe) then
          refine (cumulativity (destruct_universe right)) THEN
          refine equal_equality_variable
     else fail;;

let try_id_cumulativity id universe =
  map_hyp `try_id_cumulativity` (try_id_cum id universe);;

let try_intro_equal_variable_in_type left_term right_term proof =
  (try_id_cumulativity left_term right_term  ORELSE
  refine equal_equality_variable) proof;;
              


% This looks for a hypothesis like >> x=y in U3 where the goal is >>x=y in U7.%

let try_cum_on_hyp equality_part universe current_hyp hyp_number proof =
  let left,right = destruct_equal (type_of_declaration current_hyp) in
  if left = equality_part &
     destruct_universe right < (destruct_universe universe)
    then (refine (cumulativity (destruct_universe right)) THEN
          refine (hyp hyp_number)) proof
  else failwith `try_cum_on_hyp`;;    

let try_cumulativity equality_part universe proof =
  map_hyp `try_cumulativity` (try_cum_on_hyp equality_part universe) proof;;

 
let try_apply_equality left_term right_term proof =
  let function, argument =  destruct_apply left_term in
    letrec explicit_typed_function hyp_list = % case where function is given an %
                                              % explicit typing in the hypotheses %
      (let id,type = destruct_declaration (hd hyp_list) in
        if function = (make_var_term id) then
          type
        if is_equal_term type &
           (member function (fst (destruct_equal type))) then 
          (snd (destruct_equal type)) 
        else (explicit_typed_function (tl hyp_list))) in
    
    letrec explicit_typed_argument hyp_list = % case where argument is given an %
                                              % explicit type.                  %
      (let id,type = destruct_declaration (hd  hyp_list) in
        if argument = (make_var_term id) then
          (make_function_term `nil` type right_term)
        if is_equal_term type &
           member argument (fst (destruct_equal type)) then
          (make_function_term `nil`
                              (snd (destruct_equal type))
                              right_term
          )
        else (explicit_typed_argument (tl hyp_list))) in
  let using_type =( explicit_typed_function (hypotheses proof) 
                   ?explicit_typed_argument (hypotheses proof)) in


    refine (function_equality_apply using_type)
            proof;;
       

let find_using_term expression proof =
  letrec explicitly_typed hyp_list =
    let id,type = destruct_declaration (hd hyp_list) in
      if expression= (make_var_term id) then
        type
      if is_equal_term type &
         member expression (fst (destruct_equal type)) then
        (snd (destruct_equal type))
      else explicitly_typed (tl hyp_list) in
  explicitly_typed (hypotheses proof);;



% The arguments are the the first part term of the equality part of%
% a the term, the type part of the term, and a term (which is an   %
% equality term), and the proof from which the term was derived.   %
  
let try_intro_equal_in_universe left_term right_term  proof =
   ((try_cumulativity (fst (destruct_equal (conclusion proof)))  % the equalities %
                     right_term
    )
   ORELSE

   (
    if is_universe_term left_term then      % universe %
      refine universe_equality
    if is_void_term left_term then          % void %
      refine void_equality
    if is_atom_term left_term then          % atom %
      refine atom_equality
    if is_int_term left_term then       % integer %
      refine integer_equality
    if is_list_term left_term then          % list %
      refine list_equality
    if is_union_term left_term then         % union %
      refine union_equality
    if is_product_term left_term then             % product % 
      refine (product_equality (new_id proof))
    if is_function_term left_term then            % function %
      refine (function_equality (new_id proof))
    if is_set_term left_term then                 % set %
      refine (set_equality (new_id proof))        
    if is_quotient_term left_term then            % quotient %
      refine (quotient_equality  `nil` `nil`)
    if is_equal_term left_term then        % equality %
      refine equal_equality
    if is_less_term left_term then         % less %
      refine less_equality
    else failwith `try_intro_equal_in_universe`
   )) proof;;
      
let try_intro_equal_in_int left_term right_term = 
  if is_natural_number_term left_term then
    refine integer_equality_natural_number
  if is_addition_term left_term then
    refine integer_equality_addition
  if is_subtraction_term left_term then
    refine integer_equality_subtraction
  if is_multiplication_term left_term then
    refine integer_equality_multiplication
  if is_division_term left_term then
    refine integer_equality_division
  if is_modulo_term left_term then 
    refine integer_equality_modulo
  if is_minus_term left_term then
    refine integer_equality_minus 
  if is_integer_induction_term left_term then
    refine (integer_equality_induction `nil` make_void_term `nil` `nil`)
  else
    failwith `try_intro_equal_in_int: not an expression in int term.`;;

let try_intro_equal_in_list left_term right_term proof =
  if is_nil_term left_term then
    refine (list_equality_nil (next_universe proof)) proof
  if is_cons_term left_term then
    refine list_equality_cons proof
  if is_list_induction_term left_term then
    let using_type = find_using_term
                       (fst (destruct_list_induction left_term))
                       proof  in
      refine (list_equality_induction `nil` make_void_term using_type `nil` `nil` `nil`) proof
  else
   failwith
    `try_intro_equal_in_list: not an expression in list term.`;;

let try_intro_equal_in_union left_term right_term proof =
  if is_inl_term left_term then
    refine (union_equality_inl (next_universe proof)) proof
  if is_inr_term left_term then
    refine (union_equality_inr (next_universe proof)) proof
  if is_decide_term left_term then
    refine (union_equality_decide `nil` make_void_term
              (find_using_term (fst (destruct_decide left_term)) proof)
              `nil` `nil`
           ) proof
  else 
    failwith `try_intro_equal_in_union`;;

let try_intro_equal_in_product left_term right_term proof =
  if is_pair_term left_term then
    refine (product_equality_pair (next_universe proof) `NIL`) proof    
  if is_spread_term left_term then
    refine (product_equality_spread `nil` make_void_term
              (find_using_term (fst (destruct_spread left_term)) proof)
              `nil` `nil`
           ) proof
  else 
    failwith `try_intro_equal_in_product`;;


let try_intro_equal_in_function left_term right_term proof =
  if is_lambda_term left_term then
    refine (function_equality_lambda (next_universe proof) `NIL`) proof
  else failwith `try_equal_intro_in_function`;;

let try_intro_equal_in_set left_term right_term proof =
  refine (set_equality_element (next_universe proof) (new_id proof)) proof;;

let try_intro_equal_in_quotient left_term right_term proof =
  refine (quotient_equality_element (next_universe proof)) proof;;


% Check to see of left-type is in a set whose base is the right-type %
% if so, do a set-elim.  Otherwise, do a case split on left/right    %

let try_intro_equal_in_type proof =
  let left_term, right_term = get_term_in_type proof in
    (if is_var_term left_term then                       % is left var? %
      try_intro_equal_variable_in_type left_term right_term 
    if is_apply_term left_term then                     % is left apply? %
      try_apply_equality left_term right_term 
    if is_universe_term right_term then                   % Universe %
      try_intro_equal_in_universe left_term right_term 
    if is_atom_term right_term then                      % Atom %
      refine atom_equality 
    if is_int_term right_term then                       % Integer %
      try_intro_equal_in_int left_term right_term   
    if is_list_term right_term then                      % List %
      try_intro_equal_in_list left_term right_term 
    if is_union_term right_term then                     % Union %
      try_intro_equal_in_union left_term right_term 
    if is_product_term right_term then                   % Product %
      try_intro_equal_in_product left_term right_term 
    if is_function_term right_term then                  % Function %
      try_intro_equal_in_function left_term right_term 
    if is_set_term right_term then                       % Set %
      try_intro_equal_in_set left_term right_term 
    if is_quotient_term right_term then                  % Quotient %
      try_intro_equal_in_quotient left_term right_term 
    if is_equal_term right_term then
      refine (axiom_equality_equal) 
    if is_less_term right_term then
      refine (less_equality) 
    else 
      failwith `try_intro_equal_in_type`
   ) proof;;



let union_intro_tac sub_tactic proof =
  ((refine (union_intro_left (next_universe proof)) THEN COMPLETE sub_tactic)
  ORELSE
  (refine (union_intro_right (next_universe proof)) THEN COMPLETE sub_tactic))
    proof;;




let intro_tac sub_tactic proof =
  let goal = conclusion proof in
    if is_universe_term goal then
      refine (universe_intro_void) proof


%    if is_atom_term goal then     (need to construct a token term.)%
%      refine (intro_atom (...))  %

    if is_int_term goal then 
      refine (integer_intro_integer 0) proof

    if is_list_term goal then
      refine (list_intro_nil (next_universe proof)) proof

    if is_union_term goal then
      union_intro_tac sub_tactic proof

    if is_product_term goal then
      refine product_intro proof

    if is_function_term goal then
      refine (function_intro (next_universe proof) `NIL`) proof

    else failwith `intro_tac`;;


letrec immediate proof =
     REPEAT (       hypothesis
             ORELSE COMPLETE (refine (arith (next_universe proof)) THEN immediate)
             ORELSE (refine equality)
             ORELSE set_elim_for_base 
             ORELSE try_intro_equal_in_type
             ORELSE (intro_tac immediate)
            ) proof;;





%%
% Transformation Tactics. %
%%

%%
% Frontier Tactic %  % It's a primitive now.  (see ml-refine.lisp) %
%%




%
letrec build_frontier goal_proof =
  if not (is_refined goal_proof)
    then IDTAC
  else refine (refinement goal_proof) THENL 
           (map build_frontier (children goal_proof));;

let frontier goal_proof = build_frontier goal_proof goal_proof;;
%

%%
% Mark and Copy tactics %
%%


letrec select position list =
  if position = 1 then hd list
  else select (position-1) (tl list);;
  
letrec find_position atom list =
  if atom = hd list then 1
  else find_position atom (tl list) + 1;;


let calculate_position pattern_position pattern goal =
  find_position
    (select pattern_position (hypotheses pattern))
    (hypotheses goal);;

let adjust_assum_number pattern goal =
  let original_rule = (refinement pattern) in
    if member (rule_kind original_rule)
              [ `VOID-ELIM`; `INT-ELIM`; `UNION-ELIM`; `LIST-ELIM`;
                `PRODUCT-ELIM`; `FUNCTION-ELIM`; `SET-ELIM`; `QUOTIENT-ELIM`;
                `HYP`
              ]
      then
          set_assum_number
              original_rule
              (calculate_position (get_assum_number original_rule)
                                    pattern
                                    goal
              )
              
    else original_rule;;        
   


%letrec do_analogy pattern goal =
  if (is_refined pattern) then
    ((
      (refine (adjust_assum_number pattern goal))
        THENL (map do_analogy (children pattern)) 
     ) 
      ORELSE immediate
    )  goal
  else
    immediate goal;;%


letrec do_analogy pattern goal =
	if is_refined pattern then
		TRY (refine (adjust_assum_number pattern goal)
			THENL (map do_analogy (children pattern))
		    ) goal
	else IDTAC goal
;;



letref saved_proof = void_goal_proof;;

let mark goal_proof = (saved_proof := copy_proof goal_proof;
                       IDTAC goal_proof);;

let copy goal_proof =
  do_analogy saved_proof goal_proof;;


%%
% Set auto-tactic to refinement tactic immediate %
%%

set_auto_tactic `COMPLETE (refine (tactic \`immediate\`))`;;
