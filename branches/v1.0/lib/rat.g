Include "nat.g".
Include "pair.g".
Include "mult.g".

%Set "print_parsed".

Define rat : type := <pair nat nat>.
Define numer := fun(p:rat).(fst nat nat p).
Define denom := fun(p:rat).(snd nat nat p).

Define mkrat := fun(x y : nat).(mkpair nat nat x y).


Define rplus := 
  fun (x y : rat). 
    (mkrat (plus (mult (numer x) (denom y))
                 (mult (numer y) (denom x)))
           (mult (denom x) (denom y))).

Define rmult := 
  fun (x y : rat). 
    (mkrat (mult (numer x) (numer y))
           (mult (denom x) (denom y))).

Define eqrat := fun(x y : rat).(eqnat (mult (numer x) (denom y)) (mult (numer y) (denom x))).
Define lt := fun(x y : rat).(lt (mult (numer x) (denom y)) (mult (numer y) (denom x))). 
Define le := fun (x y : rat).(or (lt x y) (eqrat x y)).
