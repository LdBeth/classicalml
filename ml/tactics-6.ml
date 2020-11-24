%-*- Tab-Width: 2 -*-%


let ModifyConcl f p =
  (SubstConcl (f (concl p)) THEN RedefConcl) p
;;

let ModifyHyp f i p =
( SubstHyp (f (type_of_hyp i p)) i
  THENL [OnLastHyp RedefHyp; RedefConcl]
) p
;;





let ReduceConclToAssumedEqualities =
  Repeat
    (IfThenOnConcl
      (\c. (let [t;t'],() = destruct_equal c in not t=t') ? false)
      (EqI THEN Try (Refine equality)))
;;


