%- This runs through the examples in Chapter 2 -%

Include "../lib/plus.g".

Interpret (plus (S (S Z)) (S (S Z))).

Interpret (fun(x:nat).(plus x x) (S (S Z))).

Define double := fun(x:nat).(plus x x).

Interpret (double (S (S Z))).

Define double_plus := fun(x:nat)(y:nat). (plus (double x) (double y)).

Define double_plus_a := fun(x y:nat). (plus (double x) (double y)).

Classify double.

Classify Fun(x : nat). nat.

Define apply_twice := fun(f:Fun(x:nat).nat)(a:nat). (f (f a)).

Interpret (apply_twice double (S (S Z))).

Classify (plus (S (S Z))).

Define plus2 := (plus (S (S Z))).

Interpret (plus2 (S (S (S Z)))).

Define iszero := 
  fun(x:nat). 
    match x with 
      Z => tt 
    | S x' => ff
    end.

Interpret (iszero Z).

