Include "unowned.w".

Datatype nat := Z : unowned | S : Fun(x:unowned & nat).unowned.

Function plus(x:unowned)(y:unowned).unowned :=
  match x with
    Z => y
  | S x' => (S (plus x' y))
  end.

Function mult(x:unowned)(y:unowned).unowned :=
  match x with
    Z => do (dec nat y) Z end
  | S x' => (plus (inc y) (mult x' y))
  end.

