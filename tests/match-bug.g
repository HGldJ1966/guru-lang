Include "../lib/nat.g".

Define f :=  % this checks, but in the Z case, n is consumed twice, isn't it?
  fun(n:nat).
  match n with
    Z => Z
  | S _ => Z
  end.

Define main := (f Z).

Set "debug_simulate".
Set "debug_refs".
Set "debug_stages".

Compile main to "match-bug.c".
