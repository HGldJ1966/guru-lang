Include "../lib/mult.g".

Inductive comb : type :=
  k : comb
| s : comb
| app : Fun(c1 c2:comb). comb.

Define interp :=
  fun interp(c:comb):comb.
    match c with
      k => k
    | s => s
    | app c1 c2 =>
      let v1 = (interp c1) in
      let v2 = (interp c2) in
        match v1 with
          k => (app v1 v2)
        | s => (app v1 v2)
        | app v1a v2a =>
          match v1a with
            k => v2a
          | s => (app v1 v2)
          | app v1aa v1ab =>
              match v1aa with
                k => (app v1 v2) % should never happen
              | s => (app (app v1ab v2) (app v2a v2))
              | app _ _ => (app v1 v2)
              end
          end
        end
    end.
 
Define ks := 
  fun ks(n:nat):comb.
    match n with
      Z => k
    | S n' => (app (ks n') k)
    end.

Define ks_even :
  Forall(n:nat). Exists(u:{ (interp (ks (mult n two))) = k }).
                          { (interp (ks (S (mult n two)))) = (app k k) } :=
  induction(n:nat)
  return Exists(u:{ (interp (ks (mult n two))) = k }). { (interp (ks (S (mult n two)))) = (app k k) }
  with 
    Z => andi hypjoin (interp (ks (mult n two))) k by n_eq end
              hypjoin (interp (ks (S (mult n two)))) (app k k) by n_eq end
  | S n' => 
    existse [n_IH n']
    foralli(u1:{ (interp (ks (mult n' two))) = k })(u2:{ (interp (ks (S (mult n' two)))) = (app k k) }).

      andi hypjoin (interp (ks (mult n two))) k by n_eq u2 end
           hypjoin (interp (ks (S (mult n two)))) (app k k) by n_eq u1 end
  end.