%-*- Tab-Width: 2 -*-%


letrec remove_if (P: * -> bool) (l: * list) =
  if null l then [] 
  else let h.t = l in P(h) => remove_if P t | h . remove_if P t 
;;

let update_named_list name val list =
  (name,val) . remove_if (\x,(). x=name) list
;;

letref def_adders = []: (tok # (term -> (tok # term list))) list ;;

let current_def_adders () = map snd def_adders ;;

let add_def_adder name adder =
  def_adders := update_named_list name adder def_adders ;
  ()
;;

letref defined_redices = [] : (tok # (term->bool)) list ;;

let define_redex name pred = 
  defined_redices := update_named_list name pred defined_redices;
  ()
;;

let current_defined_redices () = map snd defined_redices ;;

let undo_redex_definitions (():void) = defined_redices := [] ; () ;;



% The "defined" elims and intros use global lists of arguments.
  The lists are accessed by the "get_..." functions, which are
  destructive.  Defined rules should fail with `no` if they
  find themselves to be inapplicable, in which case other rules
  will be tried, or with some other token, in which case no 
  other rules will be tried.
%

letref d_tactic_term_args = []: term list ;;

letref d_tactic_choice_args = []: tok list ;;

letref d_tactic_id_args = []: tok list ;;

letref d_tactic_hyp_num_arg = 0 ;;

let get_term_arg () =
  ( let res = hd d_tactic_term_args in
    (d_tactic_term_args := tl d_tactic_term_args ; res)
  ) ? failwith `need a term.`
;;

let get_choice_arg () =
  ( let res = hd d_tactic_choice_args in
    (d_tactic_choice_args := tl d_tactic_choice_args ; res)
  ) ? failwith `need a choice.`
;;

let get_id_arg () =
  ( let res = hd d_tactic_id_args in
    (d_tactic_id_args := tl d_tactic_id_args ;  res)
  ) ? failwith `need an id.`
;;

let get_id_args n =
  map get_id_arg (replicate () n)
;; 

let hyp_num_arg () =
  d_tactic_hyp_num_arg
;;

let set_d_tactic_args i terms choices ids =
  d_tactic_term_args := terms ;
  d_tactic_choice_args := choices ;
  d_tactic_id_args := ids ;
  d_tactic_hyp_num_arg := i 
;;

letref DE_list = []: (tok # tactic) list ;;


let undo_DE_definitions () =
  DE_list := remove_if (\x,(). not x=`E`) DE_list ;
  ()
;;


let define_DE name (T: tactic) =
  DE_list := update_named_list name T DE_list ;
  ()
;;

let current_DE_definitions () = map snd DE_list ;;

letref DI_list = []: (tok # tactic) list ;;

let current_DI_definitions () = map snd DI_list ;;

let undo_DI_definitions () =
  DI_list := remove_if (\x,(). not x=`I`) DI_list ;
  ()
;;


let define_DI name (T: tactic) =
  DI_list := update_named_list name T  DI_list ;
  ()
;;

letref ModE_list = []: (tok # (int->tactic)) list ;;
let current_ModE_definitions () = map snd ModE_list ;;

let undo_ModE_definitions () =
  ModE_list := [] ; ()
;;


let define_ModE name (T: int->tactic) =
  ModE_list := update_named_list name T ModE_list ;
  ()
;;

letref autotactic_additions = []: (tok#tactic) list ;;

let add_to_autotactic name tac =
  autotactic_additions := update_named_list name tac autotactic_additions ;
  ()
;;

let current_autotactic_additions () = map snd autotactic_additions ;;



letref inclusion_additions = []: (tok#(int->tactic)) list ;;

let add_to_inclusion name tac =
  inclusion_additions := update_named_list name tac inclusion_additions ;
  ()
;;

let current_inclusion_additions () = map snd inclusion_additions ;;


letref member_i_additions = []: (tok#tactic) list ;;

let add_to_member_i name tac =
  member_i_additions := update_named_list name tac member_i_additions ;
  ()
;;

let current_member_i_additions () = map snd member_i_additions ;;


letref Decidable_additions = []: (tok#tactic) list ;;

let add_to_Decidable name tac =
  Decidable_additions := update_named_list name tac Decidable_additions ;
  ()
;;

let current_Decidable_additions () = map snd Decidable_additions ;;



letref saved_proofs = []: (tok#proof) list ;;

let add_saved_proof name proof =
  saved_proofs := update_named_list name proof saved_proofs;
  ()
;;

let get_saved_proof name = 
  snd (find (\x. fst x = name) saved_proofs)
;; 

letref set_mtypes = [] : (term#term) list ;; 

let add_to_set_mtypes name term = 
  set_mtypes := update_named_list name term set_mtypes ;
  ()
;; 

let lookup a_list x = snd (assoc x a_list) ;;

let mtype_of_set_from_list t = lookup set_mtypes t ;; 

% associates mfun atoms with def names %
letref mfun_mdefs = [] : (tok#tok) list ;; 

let add_mfun_mdef mfun_atom def_name = 
  mfun_mdefs := update_named_list mfun_atom def_name mfun_mdefs ;
  ()
;; 

let mdef_of_mfun f = lookup mfun_mdefs f ;; 

letref eval_meta_constants = [] : tok list ;; 

let add_eval_meta_constants toks = 
  (eval_meta_constants := union toks eval_meta_constants) ; () 
;; 

let current_eval_meta_constants () = eval_meta_constants ;; 

letref ConsistentEnvs_additions = []: (tok#tactic) list ;;

let add_to_ConsistentEnv name tac =
  ConsistentEnvs_additions := update_named_list name tac ConsistentEnvs_additions ;
  ()
;;

let current_ConsistentEnvs_additions () = map snd ConsistentEnvs_additions ;;

letref Assume_additions = []: tok list ;; 
let add_to_Assume lemma_name = 
	Assume_additions := lemma_name . remove_if ($= lemma_name) Assume_additions ;; 
let current_Assume_additions () = Assume_additions ;; 


letref main_env_template = make_nil_term ;;
letref env_hyp_template = make_nil_term ;; 
letref subenv_hyp_template = make_nil_term ;; 
letref term_hyp_template = make_nil_term ;; 
letref lift_template = make_nil_term ;; 
letref term_val_type = make_nil_term ;; 

letref Inclusion_restricted_p = false ;; 

let reinitialize_lists () =
  Decidable_additions := [] ; 
  member_i_additions := [] ; 
  inclusion_additions := [] ; 
  autotactic_additions := [] ; 
  ConsistentEnvs_additions := [] ; 
  def_adders := [] ; 
  mfun_mdefs := [] ; 
  set_mtypes := [] ; 
  Inclusion_restricted_p := false ; 
  eval_meta_constants := [] ;
  undo_redex_definitions () ; 
  undo_DE_definitions () ; 
  undo_DI_definitions () ; 
  undo_ModE_definitions () ; 
	Assume_additions := []
;; 

