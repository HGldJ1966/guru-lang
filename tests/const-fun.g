Include trusted "../lib/unowned.g".
Include trusted "../lib/nat.g".

%Define one := (S Z).

Define test :=
  fun(^n:nat).
  match n with
    Z => Z
  | S n' =>
      do
        (consume_unowned nat n')
        (inc nat one)
      end
  end.

Define main :=
  (test (S Z))
  .

%Set "debug_to_carraway".
Compile main to "const-fun.c".
