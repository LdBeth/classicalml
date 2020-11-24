%define type of tactics and tacticals%

lettype tactic = (proof -> ((proof list) # ((proof list) -> proof)));;

lettype tactical = (tactic -> tactic);;




ml_curried_infix `THEN` ;;
ml_curried_infix `THENL` ;;
ml_curried_infix `ORELSE` ;;


letrec mapshape nl fl l =  
  if null nl then nil
    else 
      (let m,l = chop_list (hd nl) l in 
        (hd fl)m . mapshape(tl nl)(tl fl)l) ;;

let $THEN (tac1:tactic) (tac2:tactic) (g:proof) =
  let gl,p = tac1 g in
     let gll,pl = split(map tac2 gl) in
       flat gll ,  (p o mapshape(map length gll)pl) ;;
 

let $THENL (tac1:tactic) (tac2l:tactic list) (g:proof) =
   let gl,p = tac1 g  in
     let gll,pl = split(map (\(tac2,g). tac2 g) tac2gl)
                  where tac2gl = combine(tac2l,gl) ? failwith `THENL`
       in
         flat gll  ,  (p o mapshape(map length gll)pl);;





let IDTAC  : tactic = \g. [g],hd;;

% If the tactic is equivilent to produces the same seq on a given ptree, then fail, and 
otherwise return the result of the tacitc.%

let PROGRESS (tac:tactic) (ptree : proof) =
  let rslt = tac ptree in
    if (length (fst rslt))=1 
      then
	let subgoal=(hd (fst rslt)) in
          if (hypotheses subgoal) = (hypotheses ptree) &
             (conclusion subgoal) = (conclusion ptree)
	  then failwith `PROGRESS`
          else rslt
    else rslt;;



let $ORELSE (f1:tactic) (f2:tactic) (g:proof) = (PROGRESS f1) g ? f2 g ;;

letrec REPEAT (f:tactic) (g:proof) =
  (((PROGRESS f) THEN REPEAT f) ORELSE IDTAC ) g ;;

let TRY (f:tactic) = f ORELSE IDTAC;;

ml_paired_infix `THENTRY`;;

let $THENTRY (f:tactic) (g:tactic) = f THEN (TRY g);;

% this tactical produces a complete tactic, i.e. one that either fails or
produces a complete tree, no unproved children.%

let COMPLETE (tac:tactic) =
        \goal. if null (fst achievement) then achievement
               else failwith `COMPLETE`
               where
                  achievement = tac goal;; 



