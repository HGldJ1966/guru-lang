Include "nat_mod.g".



%===== return pair (q,r) where a = q*b + r for 0 <= r <= b
Define division :=
fun division( a b : nat ) : <pair nat <nat_mod b> >.
  match (lt a b) by ul uL with
    ff => 
      match (division a (minus b a)) with
        mkpair _ _ q r => (mkpair nat <nat_mod b> (S q) r)
      end
  | tt => (mkpair nat (nat_mod b) Z a)
  end.

%=====
Define div_q :=
fun division( a b : nat ) : nat.
  (fst nat <nat_mod b> (division a b)).
  
Define div_r :=
fun division( a b : nat ) : <nat_mod b>.
  (snd nat <nat_mod b> (division a b)).