Include "unowned.w".

Datatype nat := Z : unowned | S : Fun(x:unowned & nat).unowned.

Function plus(x:unowned)(y:unowned).unowned :=
  match x with
    Z => y
  | S x' => (S (plus x' y))
  end.
