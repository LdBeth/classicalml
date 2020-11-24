%General purpose functions for ML%

%This should be a primitive.  TBK%

let isr x = not (isl x);;


let max x y =
  if x>y then x else y;;
      
%Returns the max of a list. %
letrec list_max list =
   letrec aux l max_so_far =
	if l=nil then max_so_far
	else let h.t = l in aux t (max h max_so_far) in
    aux list 0;;

let pair_to_list pair =
  [fst pair; (snd pair)];;

let triple_to_list triple =
  fst triple . (pair_to_list (snd triple));;

let quad_to_list quad =
  fst quad . (triple_to_list (snd quad));;



%Use the character "sep" to split the token into non-empty words
words2 `/` `abc//d/ef/`  -->  [`abc`; `d`; `ef`]
%
let words2 sep string =
    snd (itlist (\ch (chs,tokl). 
             if ch = sep then
                if null chs then [],tokl
                else [], (implode chs . tokl)
             else (ch.chs), tokl)
    (sep . explode string)
    ([],[]));;



%words `are you there`  -->  [`are`; `you`; `there`]    %
let words = words2 ` `;;


%maptok f `are you there` = [f `are`; f `you`; f `there`]       %
let maptok f tok = map f (words tok);;


let loadt tok = load tok true and loadf tok = load tok false;;
let compilet tok = compile tok true and compilef tok = compile tok false;;


%Token concatenation%
%for speed, these should be implemented in lisp%

let concat tok1 tok2 = implode( explode tok1 @ explode tok2) ;;
let concatl tokl =
    implode (itlist append (map explode tokl) nil);;

ml_curried_infix `^`;;
let $^ = concat;;

let curry f x y = f (x,y) ;;
let three_curry f x y z = f (x,y,z) ;;
let four_curry f x y z a = f (x,y,z,a) ;;
let uncurry f (x,y) = f x y ;;
let three_uncurry f (x,y,z) = f x y z ;;
let four_uncurry f (x,y,z,a) = f x y z a ;;

let message tok = print_string tok; print_newline();;


% Combinators %  % As in Curry & Feys %

ml_paired_infix `o`;;
ml_paired_infix `#`;;
ml_paired_infix `oo`;;

let $o(f,g)x = f(g x) ;;
let $# (f,g) (x,y) = (f x, g y);;
%composition for a function that takes a paired argument%
let $oo (f,(g,h)) x = f(g x, h x);;

let I x = x;;
let K x y = x;;
let KI = K I;;  % Dual of K; K and KI are analogs of fst and snd%
let C f x y = f y x         %  the permutator  %
and W f x   = f x x         %  the duplicator  %
and B f g x = f (g x)       %  the compositor  %  %curried form of "o"%
and S f g x = f x (g x);;
%
 S, K, I permit the definition of lambda-abstraction
 \x.x = I      actually unnecessary, since I = S K K)    
 \x.A = K A    where A is a constant or a variable other than x
 \x.(A B) = S (\x.A) (\x.B)                               
%

ml_paired_infix `Co`;;
let $Co (f,g) x y = f (g y) x;;    %     permutation-composition          %
                                   % Ainsi nomme car  $Co (f,g) = C (f o g) %

let pair x y = (x,y);;
let curry f x y = f(x,y);;


%sequencing operators for functions%
ml_curried_infix `thenf` ;;
ml_curried_infix `orelsef` ;;

%apply f and then g%
let thenf f g x = g(f x);;

%apply f or else g%
let orelsef f g x = f x ? g x;;

let all_fun x = x;;
let no_fun x = failwith `no_fun`;;

%this should be implemented more efficiently%
let first_fun fl x =
    itlist $orelsef fl no_fun x ? failwith `first_fun`;;

let every_fun fl x =
    itlist $thenf fl all_fun x ? failwith `first_fun`;;


%apply f repeatedly%
%letrec repeatf f x = (f thenf (repeatf f) elsef I) x;;%
letrec repeatf f x = (f thenf (repeatf f)) x ? x;;


let can f x = (f x ; true) ? false ;;





%check that the value x satisfies the predicate p%
%if so, pass x on%
let assert p x =  if p x then x else fail ;;

let syserror tok =
    print_string `ML system error `;
    print_string tok;
    print_newline();
    failwith `syserror`;;


%
Provides a simple backtrace, since it prefixes a token to the previous
failure token.  Warning:  this
  (1)  slows down failure propagation.
  (2)  works only with the innermost lambda of a curried function.
%
let set_fail_prefix tok fun arg =
    fun arg ?\tail failwith (concatl [tok; ` -- `; tail]);;



%Set a function's failure token%
let set_fail tok fun arg =
    fun arg ? failwith tok;;



letrec funpow n f x =
    if n=0 then x
    else funpow (n-1) f (f x);;
