
let print x = print_to_snapshot_file x;;
let print_return x = print_return_to_snapshot_file ();;


letrec indent depth =
  if depth>0 
    then (print `|  `;indent (depth-1));;

letrec remove_trailing_empty_line (l: tok list) =
	if null l then []
	if length l > 1 then (hd l) . (remove_trailing_empty_line (tl l))
	if length (explode (hd l)) = 0 then []
	else l
;;


% Assumes first line already properly indented. Prints a final return. %
let print_term_to_snapshot_file depth term =
	let l = remove_trailing_empty_line (term_to_toks_for_print term)	in
	print (hd l) ; print_return () ;
	map (\x. indent depth ; print `   ` ; print x ; print_return ())
			(tl l) ;
  ()
;;


% Prints a final CR. %
let print_rule_to_snapshot_file depth rule =
	let l = remove_trailing_empty_line (rule_to_toks_for_print rule)	in
	indent (depth+1) ;
	print `BY ` ;	print (hd l) ; print_return () ;
	map (\tok. indent (depth+1); print `   `; print tok; print_return () )
			(tl l)
;;

let print_node depth parent_hyps proof =
	map (\i,x,A.
				if not ((x,A) = destruct_declaration (select i parent_hyps))
					 ? true
				then (	indent depth ; print (tok_of_int i) ; print `. ` ;
						 		(if not x = `NIL`
									then (print x ; print `:`)
						 		);
						 		print_term_to_snapshot_file depth A
						 )
			)
			(	upto 1 (length (hypotheses proof)) 
			 	com (map destruct_declaration (hypotheses proof))
			) ;
  indent (depth-1) ; if depth>0 then print `|- ` ; print `>> ` ; 
  print_term_to_snapshot_file depth (conclusion proof); 
  if (is_refined proof)
    then (print_rule_to_snapshot_file depth (refinement proof) ; ())
    else ((indent depth);(print `INCOMPLETE`; print_return ()))
;;



letrec print_proof depth parent_hyps proof =
  print_node depth parent_hyps proof ;
  if is_refined proof then
  	(map (print_proof (depth+1) (hypotheses proof)) (children proof);())
;;


let mm proof =
  (open_snapshot_file ();
  (print_proof 0 [] proof);
  close_snapshot_file ());
  (IDTAC proof);;





%
 Pretty print a NuPRL proof tree. Produces better looking proofs than 
   mm tactic in pproof.ml file does. 

   -written by Paul Jackson. November 14th '89.   


Print format for proof node is schematically as follows:

[...branches....]| 1. [id. (if not NIL)][...Hypothesis term.1........]
[...branches....]|    [............Hypothesis term.1.................]
       .                   .                             .
       .                   .                             .
[...branches....]|    [............Hypothesis term.1.................]
       .                   .                             .
       .                   .                             .
       .                   .                             .
[...branches....]| n. [id. (if not NIL)][...Hypothesis term.n........]
[...branches....]|    [............Hypothesis term.n.................]
       .                   .                             .
       .                   .                             .
[...branches....]|    [............Hypothesis term.n.................]
[...branches....]|->> [............Conclusion term...................]
[...branches....]?    [............Conclusion term...................]
       .                   .                             .
       .                   .                             .
[...branches....]?    [............Conclusion term...................]
[...branches....]? BY [............Refinement rule...................]
[...branches....]? !  [............Refinement rule...................]
       .                   .                             .
       .                   .                             .
[...branches....]? !  [............Refinement rule...................]
[...branches....]? !  

NOTE
1. Branch at ?'s printed only if node is not last sibling.
2. branch at !'s printed only if node has children.
3. term and rule text is folded so as to always stay in the appropriate
   region. 
4. A hypothesis is only printed if it is textually different from the
   same numbered hypothesis in the parent node.
5. If a hypothesis is hidden, []'s are put around the hypothesis number.
6. The root node does not have a branch entering the node.

The following functions are useful:

a. Invoked by typing into the transformation tactic window:

   ppp                             ..pretty print proof to snapshot file.
   ppp_file <file_name (a token)>  ..set snapshot file to <filename> then ppp.

b. Invoked at M> prompt:

   set_pp_width i       ..set number of columns to print proof with.

%



% the check if x null is inserted here because print_to_snapshot_file
  prints a null token as a "^" %

let print x = if not x=(implode []) then print_to_snapshot_file x;;
let print_return x = print_return_to_snapshot_file ();;

letref pp_width = 105 ;;
let set_pp_width i = pp_width := i ; () ;;

letrec repeat_chop_list i list = 
  (let a,b = chop_list i list in
    if b=[] then [a] else (a.(repeat_chop_list i b))
  ) ? [list]  
      % catch failure of chop_list when list shorter than i %
;;

let repeat_chop_string i string =
  map implode (repeat_chop_list i (explode string))
;;

let fold_long_lines i line_list =
  itlist $@ (map (repeat_chop_string i) line_list) []
;;

% nb print_branches expects branches in right to left order %

let print_branches branch_list = 
  map (\x. if x then print `| ` else print `  `) (rev branch_list) ;
  () 
;;

% expects branches for first line have been printed %

let print_block_body branches header line_list =
  let header_list = explode header in
  let header_length = length header_list in
  let width = pp_width - 2*(length branches) - header_length in
  let folded_lines = fold_long_lines width line_list in
  if 
    folded_lines = [] 
  then 
    print_return () 
  else
     (print header ; print (hd folded_lines) ; print_return ();
      let filler = implode (map (\x.` `) header_list) in
      map (\line. 
             print_branches branches ; print filler ;
             print line ; print_return ()
          )
          (tl folded_lines)
      ; ()
     )
;;
       
% format_hyp checks if a hypothesis is hidden, and 
  if so encloses hyp number in [] %

let format_hyps hyps hidden_hyps = 
    let format_hyp (i,x,A) = 
      let h.t = remove_trailing_empty_line (term_to_toks_for_print A) in
        (i,
           (if (member i hidden_hyps) 
                    then `[` ^ (tok_of_int i) ^ `]. ` 
                    else  (tok_of_int i) ^ `. `
           )
          ,
           ((if x=`NIL` then h else x ^ `:` ^ h ).t)
        )
    in 
      map format_hyp (upto 1 (length hyps)
                     com
                     (map destruct_declaration hyps))
;;

let print_hyps_to_snap_file branches parent_formatted_hyps hyps 
                            hidden_hyp_nums = 
      map (\(i,hyp_header,hyp_lines).  
             if ((
                 let (),parent_hyp_header,parent_hyp_lines =
                       (select i parent_formatted_hyps)
                 in
                   (not (hyp_lines = parent_hyp_lines))
                   or
                   (not (hyp_header = parent_hyp_header))
                )
                ? true)  % Catch failure of select when i
                           greater than number of parent hyps. %

             then  
               (print_branches branches 
                ; print_block_body branches hyp_header  
                                            hyp_lines
               )
          )
          (format_hyps hyps hidden_hyp_nums) ; ()
;;

let print_concl_to_snap_file branches concl_term =
    if not (branches = [])
      then (print_branches (tl branches) ; print `|-` ) 
    ; print_block_body branches `>> `
        (remove_trailing_empty_line (term_to_toks_for_print concl_term))
;;
   
let print_rule_to_snap_file branches rule = 
    print_branches (tl branches) ; print `BY` ;
    print_block_body branches ` `
      (remove_trailing_empty_line (rule_to_toks_for_print rule)) 
;;



let print_node_to_snap_file branches is_last_sibling has_children 
  parent_formatted_hyps proof =

  print_hyps_to_snap_file branches parent_formatted_hyps 
     (hypotheses proof) (hidden proof);
  let concl_branches = 
    if branches = [] then []
       else (not is_last_sibling).(tl branches)
  in
    print_concl_to_snap_file concl_branches (conclusion proof) ;
    if (is_refined proof)
      then print_rule_to_snap_file 
              (has_children.concl_branches) (refinement proof) 
      else (print_branches concl_branches ; print `INCOMPLETE` 
            ; print_return ()
           ) 
    ; print_branches (has_children.concl_branches) ; print_return ()
;;



letrec pprint_proof branches is_last_sibling parent_formatted_hyps proof =
  if 
    not (is_refined proof)
  then 
    print_node_to_snap_file branches is_last_sibling false 
                            parent_formatted_hyps proof
  else
   (let formatted_hyps = format_hyps (hypotheses proof) (hidden proof) in
    let offspring = (children proof) in
    let has_children = (not (offspring = [])) in
    print_node_to_snap_file branches is_last_sibling has_children
                            parent_formatted_hyps proof 
    ; 
    if has_children 
    then 
      (let new_branches = 
         (if (length branches) = 0 
            then [true]
            else (true.(not is_last_sibling).(tl branches)) 
         ) in
       let all_but_lastp,[lastp] = chop_list ((length offspring)-1) offspring in
       map (\p.
             pprint_proof new_branches false  formatted_hyps  p
           )
           all_but_lastp 
       ; pprint_proof new_branches true formatted_hyps  lastp
      )
   )  
;;


let ppp proof =
  (open_snapshot_file ();
  (pprint_proof [] true [] proof);
  close_snapshot_file ());
  (IDTAC proof)
;;

let ppp_file file_name proof =
   set_snapshot_file file_name 
   ; ppp proof
;;
