Include "../lib/bool.g".

Inductive nat : type :=
  Z : nat
| S : Fun(x:nat).nat.


Define eqnat :=
  fun eqnat(n m:nat):bool.
    match n by u u return bool with
      Z => match m by u u return bool with
             Z => tt
           | S m' => ff
           end
   | S n' => match m by u u return bool with
               Z => ff
             | S m' => (eqnat n' m')
             end
   end.

Define eqnatTot : Forall(n m:nat).Exists(x:bool). { (eqnat n m) = x } :=
  induction(n:nat) by x1 x2 IH return 
      Forall(m:nat).Exists(x:bool). { (eqnat n m) = x } with
  Z => induction(m:nat) by y1 y2 u return
           Exists(x:bool). { (eqnat n m) = x } with
       Z => existsi tt { (eqnat n m) = * }
              trans cong (eqnat * m) x1
              trans cong (eqnat Z *) y1
                    join (eqnat Z Z) tt
     | S m' => existsi ff { (eqnat n m) = * }
              trans cong (eqnat * m) x1
              trans cong (eqnat Z *) y1
                    join (eqnat Z (S m')) ff
     end
| S n' => induction(m:nat) by y1 y2 u return
            Exists(x:bool). { (eqnat n m) = x } with
          Z => existsi ff { (eqnat n m) = * }
              trans cong (eqnat * m) x1
              trans cong (eqnat (S n') *) y1
                    join (eqnat (S n') Z) ff
        | S m' => existse [IH n' m'] foralli(x:bool)(u:{(eqnat n' m') = x}).
                    existsi x {(eqnat n m) = *}
                      trans cong (eqnat * m) x1
                      trans cong (eqnat (S n') *) y1
                      trans join (eqnat (S n') (S m'))
                                 (eqnat n' m')
                            u
        end
end.

Define x_eqnat_x : Forall(x:nat).{ (eqnat x x) = tt } :=
  induction(x:nat) by x1 x2 IH
        return { (eqnat x x) = tt } with
    Z => trans cong (eqnat * *) x1
               join (eqnat Z Z) tt
  | S x' => trans cong (eqnat * *) x1
            trans join (eqnat (S x') (S x'))
                       (eqnat x' x')
                  [IH x']
  end.

Define test := (eqnat Z Z).

Set "print_parsed".

Interpret test.
