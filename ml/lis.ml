%List-processing functions for ML%
%Many of these functions could be coded in Lisp for speed%

let append x y = x @ y;;

let member element list =
  letrec aux x l =
    let h.t = l in
       if x=h then true
       else aux x t
  in
  (aux element list) ? false;;

let itlist f l x = rev_itlist f (rev l) x;;

% [x1; ...; xn]   --->   (fun x1 ... (fun (xn-1) xn)...)   for n>0 %
let end_itlist fun l =
    if null l then failwith `end_itlist`
    else (let last.rest = rev l in
          rev_itlist fun rest last);;

let eqfst x (y,z) = (x=y)
and eqsnd x (y,z) = (x=z);;

let assoc x = find(eqfst x);;
let rev_assoc x = find(eqsnd x);;

let intersect l1 l2 = filter (\x. member x l2) l1 ;;
let subtract l1 l2 = filter (\x. not member x l2) l1 ;;
let union l1 l2 = l1 @ (subtract l2 l1) ;;


%make a list into a set, stripping out duplicate elements%
let make_set l =
    itlist (\a s. if member a s then s else a.s) l [];;

letrec split l = 
    if null l then (nil,nil)
    else 
      (let (x1,x2) .l' = l  in
       let l1',l2' = split l' in (x1.l1', x2.l2'));;

let combine (l1,l2) =
    letrec aux l1 l2 =
	if null l1 & null l2 then nil
	else let h1.t1=l1 and h2.t2=l2 in (h1,h2) . (aux t1 t2) in
    (aux l1 l2) ? failwith `combine`;;

ml_paired_infix `com`;;
let $com = combine;;

%Check if the elements of `l` are all distinct%
letrec distinct l = 
    (null l) or
    (not (member (hd l) (tl l)) & distinct (tl l));;

% chop_list n [e1; ...; en; e[n+1]; ... ; e[n+m]   --->
        [e1; ...; en] , [e[n+1]; ...; e[n+m]]
%
let chop_list n l = 
    letrec aux n l = 
       if n=0 then (nil,l)
       else let h.t = l in
              let m,l' = aux (n-1) t in h.m, l'
    in
    (aux n l) ? failwith `chop_list`;;

let rotate_left (a.l) = l @ [a]
and rotate_right l =
    let ra.rl = rev l in ra . (rev rl)
;;

% [[1;2;3]; [4;5;6]; [7;8;9]]   --->   [1; 5; 9]        %
letrec diagonal ll =
    if null ll then []
    else hd (hd ll) . (diagonal (map tl (tl ll)));;

% [x1; ...; x(m+n)]   --->  [y1; ...; ym], [z1; ...; zn]
where the y's are all x's that satisfy p, the z's all other x's
%
let partition p l =
    itlist (\a (yes,no). if p a then (a.yes),no else yes, (a.no))
    l ([],[]);;


%make the list [x; x; ...; x] of length n%
let replicate x n =
    if n<0 then failwith `replicate`
    else
      letrec aux x n r =
         if n=0 then r
         else aux x (n-1) (x.r) in
      aux x n [];;

%make the list [from; from+1; ...; to]%
let upto from to =
    letrec aux from to result =
       if to < from then result
       else aux from (to - 1) (to . result) in
    aux from to [];;
