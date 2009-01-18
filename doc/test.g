Include "../lib/mult.g".

Define plus224 := join (plus two two) four.

Classify cong (S *) plus224.

Classify cong (plus * *) plus224.


Define plus134 := join (plus one three) four.

Classify trans plus224 plus134.



%- 

Classify refl (fun loop(b:bool):bool. (loop b) tt).

Interpret (fun loop(b : bool) : bool. (loop b) tt).

Define Zplus := foralli(m:nat). join (plus Z m) m.

Classify [Zplus three].

Classify { (plus Z three) = three }.

Define iszero := 
  fun(x:nat). 
    match x with 
      Z => tt 
    | S x' => ff
    end.

Interpret (iszero (S Z)).


Classify plus224.

Define Zplus := foralli(m:nat). join (plus Z m) m.

Classify Zplus.


Define plusZa := foralli(m:nat). join (plus m Z) m.

Classify plusZ.


Define plus2 := (plus (S (S Z))).

Interpret (plus2 (S (S (S Z)))).

Define double := fun(x:nat).(plus x x).

Define apply_twice := fun(f:Fun(x:nat).nat)(a:nat). (f (f a)).

Interpret (apply_twice double (S (S Z))).

Classify (plus (S (S Z))).

Interpret (apply_twice (plus (S (S Z))) (S (S Z))).
-%

