Include "../lib/nat.g".

Define f :=  % this checks, but in the Z case, n is consumed twice, isn't it?
  fun(n:nat).
  match n with
    Z => n
  | S n' => n'
  end.

Define main := (f Z).

Compile main to "match-bug.c".
