lettype void = . ;; 

let base = ``lis gen primitives unify tacticals tactics pproof``
and tactics = ``init term-1 term-2 tactics-1 tactics-2 tactics-3 
                tactics-4 tactics-5 tactics-6 tactics-7 tactics-8 tactics-9 autotactic`` 
in
map (\x. load (complete_nuprl_path ``ml`` x) false) base ;
map (\x. load (complete_nuprl_path ``ml`` x) false) tactics
;; 









