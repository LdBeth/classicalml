%-*- Tab-Width: 2 -*-%

letref max_expansion = 0;;

letrec sum_list list =
  if null list then
    0
  else
    hd list + (sum_list (tl list));;


letrec count_refinements proof = 
  if is_refined proof then
    1 + sum_list (map count_refinements (children proof))
  else
    0;;

let is_tactic_refinement proof =
  is_refined proof & (rule_kind (refinement proof) = `TACTIC`);;

letrec count_real_refinements proof = 
  if is_tactic_refinement proof then
    (let real_refs =    (count_real_refinements (subproof_of_tactic_rule (refinement proof)))  in
        max_expansion := max max_expansion real_refs;
        real_refs + (sum_list (map count_real_refinements (children proof))))
  if is_refined proof then
    1 + sum_list (map count_real_refinements (children proof))
  else
    0;;

% Returns a list contianing %
% 1) actual refinements     %
% 2) primitive refinements  %
% 3) ratio of 2 to 1.       %


let theorem_stats thm_name =
	let p = proof_of_theorem thm_name	in
	let m = count_refinements  p
	  and n = count_real_refinements p	in
	[m;n;n/m];;


let average_and_sd l =
  let sum = sum_list l and
      sum_sqr = sum_list (map (\x.x*x) l) and
      n = length l in
    (sum/n,
     sqrt ((sum_sqr - (sum*sum/n))/n));;


let calc_stats stat_list = 
   let r=average_and_sd (map hd stat_list) and 
       p=   average_and_sd (map (hd o tl) stat_list) in
     print_tok `Average refinements per proof: `; 
     print_int (fst r); 
     print_tok `\RStandard deviation: `;
     print_int (snd r);
     print_tok `\RAverage primitive refinements per proof: `; 
     print_int (fst p); 
     print_tok `\RStandard deviation: `;
     print_int (snd p);
     print_tok `\RAverage expansion ratio: `;
     print_int ((fst p)/(fst r));
     print_tok `\RMaximum exapansion in library: `;
     print_int   max_expansion;;


let library_stats () =
  max_expansion := 0;    %reset the max count. %
	let stat_list = map (\x. theorem_stats x ? [0;0;0])  (library ()) in
    let clean_stat_list = filter (\x. not ( x = [0;0;0])) stat_list in
     clean_stat_list;;


