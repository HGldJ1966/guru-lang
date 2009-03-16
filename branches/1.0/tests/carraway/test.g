Set "print_parsed".

Include "unowned.g".
Include "owned.g".

Datatype nat := Z : unowned | S : Fun(x:unowned & nat).unowned.

Global two := let one = (S Z) in (S one).

Function plus(x:unowned)(y:unowned).unowned :=
  match x with
    Z => y
  | S x' => (S (plus x' y))
  end.

