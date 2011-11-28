Include "../lib/nat.g".

Define my_context :=
  fun(f:Fun(a:nat).bool)(a:nat).
    match (f a) with
      ff => tt
    | tt => tt
    end.

Classify
  foralli(f:Fun(a:nat).bool)
         (a:nat)
         (u:{ (my_context f a) = tt }).
  cinv (f a) trans symm eval (my_context f a)
                   u. 
