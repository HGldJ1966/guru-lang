Include trusted "../lib/unowned.g".
Include trusted "../lib/bool.g".

Inductive Eq : Fun(a b:bool).type :=
  mk_eq : Fun(a b:bool)(u:{ a = b }).<Eq a b>.

Define Eq_lem :=
  foralli(a b:bool)(pf:<Eq a b>).
  case pf with mk_eq _ _ u =>
    hypjoin a b by u end
  end.
