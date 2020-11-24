%-*- Tab-Width: 2 -*-%

letrec remove_prior_duplicates l =
  if null l then []
  if member (hd l) (tl l) then remove_prior_duplicates (tl l)
  else (hd l) . (remove_prior_duplicates (tl l))   
;;

letrec has_duplicates l =
  if null l then false 
  if member (hd l) (tl l) then true
  else has_duplicates (tl l)
;;

% If args is a list of terms which can be actual parameters
in an instance of the named def, and if they are in the order
in which they would appear in an instance term, then permute them
to the order given by the display form of the def.
%
let permute_args_for_def_instantiation name args =
  let formals = formal_list_of_def name  in
  let rhs_occs = rhs_formal_occurrences_of_def name in
  if not (length formals = length rhs_occs 
          & length formals = length args) 
     or has_duplicates rhs_occs
  then failwith `permute_args_for_def_instantiation` 
  else map (\id. select (find_position id rhs_occs) args)
           formals 
;;

let add_extraction_def t =
  let h.l = decompose_application t in
  let name = remove_underscore (destruct_term_of_theorem h)  in
  name, 
  permute_args_for_def_instantiation name l
;;

let add_def t =
  (add_extraction_def orelsef first_fun (current_def_adders ()))
  t
;;

let add_defs t = add_display_form add_def t ;;

let ext_name  = 
  remove_underscore o destruct_term_of_theorem o head_of_application
;;

% ids should be ordered according to def lhs. %
let add_matching_def_adder result_name pattern ids result_pred =
  let adder t =
    result_name ,
    assert result_pred (map (lookup (match pattern t ids)) ids)  in
  add_def_adder result_name adder
;;


letrec combine_alists l l' =
  if null l then l'
  if null l' then l 
  else 
    ( let (x,t).l'' = l in
      if (lookup l' x) = t then (combine_alists l'' l')
      else failwith `die`
      ?? [`die`] fail
      ?  (x,t).(combine_alists l'' l') 
    ) 
;;

let apply_to_one f l =
  letrec aux l =
    if null l then fail
    else (f (hd l) ? aux (tl l))  in
  aux l
;;

let accumulate_and_combine f init_value l =
  letrec aux accumulation revd_combination_so_far l_tail =
    if null l_tail then revd_combination_so_far
    else aux (f accumulation (hd l_tail))
             ((hd l_tail, accumulation) . revd_combination_so_far)
             (tl l_tail)      in
  rev (aux init_value [] l)
;;

let is_bound id = exists (\x,(). x=id) ;;

let uncurry f (x,y) = f x y;;


% If t has subterms u1,u2,...,un, and t' has subterms v1,...,vn,
then let ui',vi' be f(ui)(vi), and replace ui by ui' in t and vi
by vi' in t'.  (Depends on map_on_subterms doing the
applications in the order given by the function subterms.)
t,t' must have the same term_kind.
%
let map2_on_subterms f t t' = 
  if not term_kind t = term_kind t' then failwith `map2_on_subterms` ;
  let f = uncurry f in
  letref l,l' = (split o map f) (subterms t com subterms t')  in
  let next () = let h.r = l in l:=r; h  in
  let next' () = let h.r = l' in l':=r; h in
  map_on_subterms next t, map_on_subterms next' t'
;;

let map2_on_def_subterms f t t' =
  let f = uncurry f in
  let fun.args = decompose_ap t in
  let fun'.args' = decompose_ap t' in
  let new_args,new_args' = split (map f (args com args')) in
  make_ap (fun.new_args), make_ap (fun'.new_args')
;;


let all (P: *->bool) (l: * list) =
  letrec aux l = if null l then true else P (hd l) & aux (tl l) in
  aux l
;; 




let context_instantiated context bindings =
 all (\x,(). x=`NIL` or is_bound x bindings) context
;;


let extend_bindings_using_context context match_bindings p =
  letrec aux context_etc =
    if null context_etc then match_bindings
    else
      let ((x,A),ids) . rest = context_etc in
      let bindings = aux rest in  
      if exists (\v. member (dv v) ids & not is_bound (dv v) bindings)
                (free_vars A)
      then (  union (match A (get_type p (lookup bindings x)) ids)
                    bindings
              ? bindings
           )
      else bindings  in
  aux (accumulate_and_combine (\ids (x,A). x.ids) [] context)
;;


let match_in_context pattern instance context p =
  extend_bindings_using_context context
    (match pattern instance (map fst context)) p
;;


let destruct_iff t =
  let a,b = destruct_and t in
  let (c,d),(d',c') = destruct_implies a, destruct_implies b in
  if not (c=c' & d=d') then failwith `destruct_iff`
  else c,d
;;

let id = \x.x ;; 

% false <=> occurs nonce, true <=> once, failure o.w. %
let occurs_once x t =
  letrec aux t = % iff x occurs exactly once %
    if is_var_term t then destruct_var t = x
    else let n = length (filter id (map aux (subterms t))) in
         if n=0 then false if n=1 then true else fail in
  aux t ? failwith `more than 1 occurrence`
;; 


letrec optimize t =
  ( let f,a = destruct_apply t in
    let x,b = destruct_lambda f in
    if occurs_once x b then optimize (substitute b [mvt x, a])
    else optimize b
  )
  ? map_on_subterms optimize t
;; 


letrec find_hyp (P: (tok#term)->bool) p : int =
  letrec aux hyps i = 
    if P (destruct_declaration (hd hyps)) then i
    else aux (tl hyps) (i+1) in
  aux (hyps p) 1
;; 