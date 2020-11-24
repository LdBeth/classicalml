%-*- Tab-Width: 2  -*-%


%$%
let min x y = if x<y then x else y ;;

% (\x.a)(b) --> a  etc. %
letrec fake_compute_ap t = 
  if is_apply_term t or is_term_of_theorem_term t then
    ( let f.args = decompose_ap t in
      let f = 
        fake_compute_ap (extracted_term_of_theorem (destruct_term_of_theorem f))
        ? f in
      let ids,b = destruct_lambdas f in
      let n = min (length ids) (length args) in
      if n=0 then make_ap (f.args)
      else fake_compute_ap
            (make_ap (make_lambdas (nthcdr n ids) b . nthcdr n args))
    )
  else t
;; 

let ElimSetEq i p =
( let equands, T = destruct_equal (h i p) in
  if not is_set_term (fake_compute_ap T) then fail ; 
  let x,A,B = destruct_set (fast_ap compute T) in
  Assert (make_equal_term A equands)
  THENL 
  [SubstFor (h i p) THEN Try Trivial
  ;Id
  ]
) p
;; 

let ElimIntSubsetEq i =
  ElimSetEq i THENM 
  OnLastHyp (\i' p. if is_int_term (eq_type (h i' p)) then Thin i p else fail)
;; 



let Unsetify p =
  Same
    (map
      (\i. IfOnHyp (\x,A. is_set_term (fake_compute_ap A))
                   (Try (SetE i))
                   (Try (ElimIntSubsetEq i))
                   i)
      (rev (upto 1 (number_of_hyps p)))
    )
    p
;;


let UnSquash p =
  Same
    (map
      (\i. IfThenOnHyp (\x,A. is_set_term (fake_compute_ap A)) (Try (SquashE i)) i)
      (rev (upto 1 (number_of_hyps p)))
    )
    p
;;





let Properties terms =
  let Aux t p =
    let n = number_of_hyps p   in
    let type = get_type p t in
    Same
    [Assert (make_equal_term type [t]) 
    ;ExposeProperties (n+1)
    ;Thin (n+1)
    ]
    p     in
  Same (map Aux terms)
;;

let Decidable p = Repeat (First (current_Decidable_additions ())) p ;;

let Decide t = 
  Cases [t; make_not_term t] THENO Try Decidable 

;; 

% atom_eq not handled yet %
let DecisionTermCases terms_and_types =
  let Aux (t,T) =               
    let [a;b;t1;t2] = subterms t  in
    let true_case, false_case =
      if is_int_eq_term t then 
       (let u = make_equal_term make_int_term [a;b]  in
        u, make_not_term u)
      if is_atom_eq_term t then 
       (let u = make_equal_term make_atom_term [a;b]  in
        u, make_not_term u)
      else % assume int_less %
       (let u = make_less_term a b in
        u, make_not_term u)      in
    Same
      [Cases [true_case; false_case] THEN Try Decidable
      ;OnLastHyp 
        (IfOnHyp 
          (\x,H. H=true_case)
          ( Assert (make_equal_term T [t; t1])
            THENL [ReduceDecisionTerm 1 true; Idtac] 
          )
          ( Assert (make_equal_term T [t; t2])
            THENL [ReduceDecisionTerm 1 false; Idtac] 
          )
        )
      ]     in
  Same (map Aux terms_and_types)
;;



let CaseLemma name terms =
  Same
    [InstantiateLemma name terms
    ;OnLastHyp (\i. Refine (union_elim i `NIL` `NIL`))
    ;OnNthLastHyp 2 Thin
    ]
;;





let make_term_of_application thm_name args =
  iterate_fun make_apply_term (make_term_of_theorem_term thm_name . args)
;;


let n_ids n = map (\i. `x`^(tok_of_int i)) (upto 1 n)
;;

let add_prl_escapes tok =
  iterate_fun
    concat
    (map (\ch. if ch = `<` then `\\<`
               if ch = `>` then `\\>`
               if ch = `\\` then `\\\\`
               else ch )
         (explode tok))
;;



let types_to_formal_descriptors l =
  map (\x,A. add_prl_escapes
              (if x=`NIL` then term_to_tok A else x^`: `^(term_to_tok A)))
      l
;;



% x1:A1->...->xarity:Aarity->B  |--->  [x1,A1;...;xarity,Aarity].
  If the arity argument is negative then it is taken instead to be maximal.
%
let function_type_to_arg_types type arity =
  let domains = fst (explode_function type) ? []  in
  let max_arity = length domains   in
  if arity < 0 then domains
  if arity > max_arity then 
    failwith `function_types_to_arg_types: arity too large.`
  else firstn arity domains
;;


let concat_using_commas (l: tok list) =
  let l = iterate_fun append (map (\x. (explode x)@[`,`]) l)  in
  implode (firstn (length l - 1) l) 
;;


let make_formal_arg_string formals descriptors =
  concat_using_commas (map (\x,d. `<`^x^`:`^d^`>`) (formals com descriptors))
;;


let create_ext_application_def def_name lib_position display_name thm_name arity =
  if arity=0 then create_def def_name lib_position display_name
                    (make_term_of_theorem_term thm_name)
  else
    let arg_types = 
      function_type_to_arg_types (main_goal_of_theorem thm_name) arity in
    let n = length arg_types   in
    let formals = n_ids n   in
    let arg_string = 
      make_formal_arg_string formals (types_to_formal_descriptors arg_types)   in
    create_def def_name lib_position (display_name^`(`^arg_string^`)`)
      (make_term_of_application thm_name (map make_var_term formals))
;;



let types_to_universalizer types =
  letrec aux types t =
    if null types then t
    else let (x,A).rest = types in
         make_all_term x A (aux rest t)      in
  aux types
;;


let types_and_where_to_product types where_term =
  if null types then failwith `types_and_where_to_product: need types` ;
  letrec aux types =
    if length types = 1 then
      let [x,A] = types in 
      if is_true_term where_term then A
      else make_some_where_term x A where_term
    else
      let (x,A).rest = types in make_some_term x A (aux rest)     in
  aux types
;;


letref projector_separator = `.` ;;

let create_module_projector_def def_name lib_position projector_name projector_ext_thm_name module_type =
  create_def 
    def_name 
    lib_position
    ( (make_formal_arg_string [`z`] 
        (types_to_formal_descriptors [`NIL`, module_type])
      )
      ^ projector_separator ^ projector_name
    )
    (make_term_of_application projector_ext_thm_name [make_var_term `z`])
;;

let Tactic tok p = Refine (tactic tok) p ;;

let create_and_prove_thm name lib_position goal Tactic =
  create_theorem name lib_position 
    (let pl,v = Tactic (make_sequent [] [] goal) in v pl)
;;


let define_projector_redex names =
  define_redex
    (concat_using_commas names)
    (\t. ( let f,a = destruct_apply t  in
           member (destruct_term_of_theorem f) names  &  is_pair_term a
         ) ? false
    )
;;


let make_sequence lbracket rbracket separator members =
  let exploded_separator = explode separator  in
  letrec build_char_list members = 
    if null members then explode rbracket
    if length members = 1 then explode (hd members) @ explode rbracket
    else let h.t = 
            members in explode h @ exploded_separator @ build_char_list t    in
  implode (explode lbracket @ build_char_list members)
;;



let make_ml_tok x = `\``^x^`\`` ;;

let make_ml_tok_list l =
  make_sequence `[` `]` `;` (map make_ml_tok l)
;;



let make_ml_function_application (f: tok) (args: tok list) = 
  accumulate (\acc arg. acc ^ ` (` ^ arg ^ `)`)
             f
             args
;;

let make_ml_top_level_let lhs rhs =
  `let ` ^ lhs ^ ` = ` ^ rhs ^ ` ;; `
;;



let create_module_arg_names =
`(name: tok)
 (lib_position: tok)
 (parameter_types: (tok#term) list)
 (component_types: (tok#term) list)
 (projector_names: tok list)
 (typical_element_name: tok)
 (level: int)
 (where_term: term)`
;;


let concat_tok_list l =
  implode (accumulate append [] (map explode l))
;;


letrec RepeatFor n T p =
  Try (If (\p. n<1) Fail (Progress T) THEN RepeatFor (n-1) T)
  p
;;

let create_module 
    (name: tok)
    (lib_position: tok)
    (parameter_types: (tok#term) list)
    (component_types: (tok#term) list)
    (projector_names: tok list)
    (typical_element_name: tok)
    (level: int)
    (where_term: term)   =
  let parameter_names = 
    map fst parameter_types and component_names = map fst component_types in
  let universalizer = types_to_universalizer parameter_types  in
  let m = length parameter_types  and  n = length component_types   in
  let name_ = name^`_`    in
  let projector_def_names = map (\x. name^`_`^x) projector_names in
  let projector_ext_thm_names = map (\x. x^`_`) projector_def_names  in
  let projector_type_thm_names = map (\x. x^`__`) projector_def_names  in
  if exists (\x. x=`NIL`) parameter_names then
    failwith `create_module: parameter names must be non-NIL.` ;
  if not n = length projector_names then
    failwith `create_module: wrong number of projector names.` ;      
  letref lib_position = lib_position  in
  let update_lib_position ob_name = lib_position := `after `^ob_name   in
  let subst_into_ith_component i terms =
    substitute  (snd (select i component_types))
                (map make_var_term (firstn (i-1) component_names)  com terms)  in
  let p = make_var_term typical_element_name   in

  % Create the thm and def pair that form the definition of the module type-term. %  
  let thm_goal = universalizer (make_universe_term level)  in
  let T =
    Refine (explicit_intro 
              (make_lambdas parameter_names
              (types_and_where_to_product component_types where_term)))
    THEN Tactic `Autotactic`   in
  create_and_prove_thm name_ lib_position thm_goal T ;
  update_lib_position name_ ;
  create_ext_application_def name lib_position name name_ m ;
  update_lib_position name ;

  % Create the thm and def pairs that form the definitions of the projector terms %
  let type = instantiate_def name (map make_var_term parameter_names)  in
  let extended_universalizer = 
    types_to_universalizer (parameter_types @ [typical_element_name, type])  in
  let new_ids p = map (\(). undeclared_id p `p`) (upto 1 n)   in
  letrec create_remaining_projectors i =
    if n<i then ()
    else
      let ext_thm_name = (select i projector_ext_thm_names) in
      create_and_prove_thm ext_thm_name lib_position make_object_term
        (Refine 
          (explicit_intro 
            (make_lambda_term typical_element_name (make_projection n i p)))
        THEN Refine (object_equality_member make_nil_term)) ;
      update_lib_position ext_thm_name ;
      create_module_projector_def (select i projector_def_names) 
        lib_position (select i projector_names)
        ext_thm_name type ;
      update_lib_position (select i projector_def_names) ;
      let p_projections_so_far =
        map (\def. instantiate_def def [p])
            (firstn (i-1) projector_def_names) in
      let projection_type = subst_into_ith_component i p_projections_so_far in
      let type_thm_goal =
        extended_universalizer
          (make_equal_term projection_type 
            [instantiate_def (select i projector_def_names) [p]])  in
      let ProveTypeThm =
        ExpandDefsInConcl [select i projector_ext_thm_names] 
        THEN Tactic `Autotactic`    in
      create_and_prove_thm (select i projector_type_thm_names) 
        lib_position type_thm_goal ProveTypeThm ;
      update_lib_position (select i projector_type_thm_names) ;
      create_remaining_projectors (i+1)   in
  create_remaining_projectors 1 ;

  % Create a theorem which gives the hidden properties of the module, if any. %
  (if not is_true_term where_term then
    let properties_thm_name = name_^`properties` in
    let p_projections =
      map (\def. instantiate_def def [p])
         projector_def_names in 
    let properties_thm_goal =
      extended_universalizer
        (make_squash_term 
          (substitute where_term
            (map (make_var_term o fst) component_types  com  p_projections)))  in
    let PropertiesTheoremTactic =
      RepeatFor (m+1) I
      THENW (OnLastHyp (\i p. RepeatProductE (new_ids p) i p)
             %THEN OnLastHyp SetE%
             THEN ExpandDefsInConcl projector_ext_thm_names
             THEN ReduceConcl
             THEN SquashI)
      THEN Tactic `Autotactic`            in
    create_and_prove_thm properties_thm_name lib_position 
      properties_thm_goal PropertiesTheoremTactic ;
    update_lib_position properties_thm_name
    ; 
    ()
  ) ;

  % Create an ML object which will: add to the redex %
  %  environment recognizers for projector/tuple pairs; %

  create_ml_object (`add_`^name_^`tactics`) lib_position 
    (concat_tok_list
      [make_ml_function_application
        `define_projector_redex` [make_ml_tok_list projector_ext_thm_names]
      ;` ;; `
      ;make_ml_function_application
        `define_ModE`
        [make_ml_tok name
        ;make_ml_function_application
          `ExplodeModule` [make_ml_tok name_; make_ml_tok_list projector_names]
        ]
      ;` ;;`
      ]
    )
  ;
  ()
;;

% The argument should be a term which is a module instance. 
(e.g. a member of Group). 
%
let ModuleProperties t p =
  let T = 
    get_type p t 
    ? failwith `ModuleProperties: could not guess type of ` ^ term_to_tok t  in
  let l = decompose_application T in
  ( let module_name_ = destruct_term_of_theorem (hd l)  in
    InstantiateLemma (module_name_^`properties`) (tl l @ [t]) p
  )
  ? failwith `ModuleProperties: type not a module type`
;;



let name_of_defined_term t =
  destruct_term_of_theorem (head_of_application t)
;;

%
let ExplodeModule module_name_ projector_def_names i p =
  if not module_name_ = name_of_defined_term (type_of_hyp i p) then fail ;
  let x = id_of_hyp i p in
  if `NIL` = x then failwith `ExplodeModule: type must have tag.` ;
  let projections = map (\def. instantiate_def def [mvt x]) projector_def_names in
  let projection_typings = 
    map (\proj. make_equal_term (get_type p proj) [proj]) projections  in
  ( Seq projection_typings
    THENS Try ( InstantiateLemma 
                  (module_name_ ^ `properties`) 
                  (tl (decompose_application (type_of_hyp i p)))
                THENS OnLastHyp 
                        (IfThenOnHyp (\x,H. is_set_term H) (OnLastHyp SetE))
              )
  ) p
;;
%

let max_number_suffixing_ proof =
   list_max
        (0 . (map (number_suffixing_letter o id_of_declaration)
                   (hyps proof)))
;;

let none_declared ids p = 
  let declared_ids = map id_of_declaration (hyps p) in
  not exists (\id. member id declared_ids) ids
;; 

let append_number n id =
  implode (explode id @ explode (tok_of_int (max n 0)))
;;

let new_ids_from_ids ids p =
  if none_declared ids p then ids
  else  
    letrec aux n =
      let new_ids = map (append_number n) ids in
      if none_declared new_ids p then new_ids else aux (n+1)  in
    aux 1
;;

let OnLastDecl T p =
  T (fst (find (\i,d. not id_of_declaration d = `NIL`)
               (rev (upto 1 (number_of_hyps p) com (hyps p)))))
    p
;;

let OnNthLastDecl n T p =
  T ((fst o select n)
     (filter (\i,d. not id_of_declaration d = `NIL`)
             (rev (upto 1 (number_of_hyps p) com (hyps p)))))
    p
;;

let decl_captures_hyp i p =
  let x = mvt (id_of_hyp i p) in
  exists (member x o free_vars o type_of_declaration)
         (nthcdr i (hyps p))
;;

let replace_eq_type T t =
  let l,T' = destruct_equal t in
  make_equal_term T l
;;

%$% 
let GenProductE newids i p =
  if id_of_hyp i p = `NIL` then failwith `GenProductE` ;  
  let A = type_of_hyp i p in
  letref newids = newids in
  let good_newid id = 
    (let h.t=newids in newids := t ; h) 
    ? undeclared_id p (if id=`NIL` then `x` else fst_ch id)  in
  letref junk_ids_so_far = [] in
  let junk_newid () = 
    hd (junk_ids_so_far := undeclared_id p `x` . junk_ids_so_far) in  
  let is_last_prod t = 
    is_product_term t 
    & not is_product_term ((snd o snd o destruct_product) t)  in
  let EJunkProd j p =
    if is_last_prod (type_of_hyp j p) then failwith `EJunkProd`
    else Refine (product_elim j (good_newid (id_of_hyp j p)) 
                                (junk_newid())) 
                p  in
  let ELastProd j p = 
    if is_last_prod (type_of_hyp j p) then
      ( Refine (product_elim j (good_newid (id_of_hyp j p)) 
                               (good_newid (id_of_hyp j p)))
        THEN Try (OnLastDecl \i. (Refine (set_elim i big_U `NIL`)))
      ) p
    else failwith `ELastProd`  in
  let PrettyUp =
    OnLastHyp (ReverseComputeHypUsing 
                  (replace_eq_type (make_tagged_term 0 A)))
    THEN ReverseComputeHypUsing (\t. make_tagged_term 0 A) i in

  If (decl_captures_hyp i)
  
  ( CH i
    THEN EJunkProd i
    THEN OnLastHyp (\i. BringHyps [i])
    THEN Repeat (OnLastDecl EJunkProd)
    THEN OnLastDecl ELastProd 
    THEN (\p. Thinning (map (\id. find_declaration id p) 
                            junk_ids_so_far) 
                       p)
    THEN I
    THEN
      If is_wf_goal 
        ( EqI 
          THEN Repeat (IfThenOnConcl (is_pair_term o first_equand) EqI)
          THEN Try Eq
          THENW (SetElementI THEN Try Trivial)
        )
        PrettyUp
    ORELSE % failure must be from "EJunkProd i" % 
    (CHThen ELastProd i THEN PrettyUp)
  ) 

  (RepeatProductE newids i)

  p

;;  
%$%   

let UglilyExplodeModule module_name_ desired_newids i p =
  if not module_name_ = name_of_defined_term (type_of_hyp i p) then fail ;
  ( GenProductE (new_ids_from_ids desired_newids p) i 
    THEN ReduceConcl 
  ) p
;;

let ExplodeModule module_name_ desired_newids i =
  UglilyExplodeModule module_name_ desired_newids i
  THEN RedefConcl
;;

let ModE i p =
  Some (map (\T. T i) (current_ModE_definitions ())) p
;; 



% ˆx1. ˆx2. ... ˆxn. t   ---> [x1; x2; ... xn], t
  If the arity argument is negative then it is taken instead to be maximal.
%
letrec destruct_multi_lambda t n =
  if n=0 or not is_lambda_term t then
    [],t
  else
    let x,t' = destruct_lambda t in
    let vars,t'' = destruct_multi_lambda t' (n - 1)   in
    (x.vars),t''
;;


% Gross hack. %
let get_type_assuming assums pf t =
  let p = 
    last (fst (Refine (let vars,types = split assums in seq types vars) pf))  in
  get_type p t
;;


let get_lambda_type t lambda_var_types p =
  let vars,body = destruct_multi_lambda t (length lambda_var_types) in
  implode_function
    (vars com lambda_var_types)
    (get_type_assuming (vars com lambda_var_types) p body)
;;

let make_in_term t T = 
  make_equal_term T [t]
;;



let pretty_up_mono_result_term t =
  let fix_not t =
    ( let t' = destruct_not t in
      if is_less_term t' then
        (let a,b = destruct_less t' in instantiate_def `le` [b;a])
      else make_not_term t'
    ) 
    ? t     in
  if is_and_term t then 
    let a,b = destruct_and t in make_and_term (fix_not a) (fix_not b)
  else fix_not t
;;


let Mono i op j p =
  let n = number_of_hyps p in
  ( Refine (monotonicity op i j)
    THEN
    \p.
      let n' = number_of_hyps p   in
      ( Seq (map (pretty_up_mono_result_term  o (\i. type_of_hyp i p)) 
                 (upto (n+1) n')
            )
        THEN (Hypothesis ORELSE Thinning (upto (n+1) n'))
  
      ) p
    
  ) p
;;




let MonoWithL t op i p =
  let n = number_of_hyps p  in
  ( Assert t
    THENL [Idtac; Mono (n+1) op i THEN Thinning [n+1]]
  ) p
;;

let MonoWithR i op t p =
  let n = number_of_hyps p  in
  ( Assert t
    THENL [Idtac; Mono i op (n+1) THEN Thinning [n+1]]
  ) p
;;



