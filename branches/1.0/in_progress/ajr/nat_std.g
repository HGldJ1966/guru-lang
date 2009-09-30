Include "../../guru-lang/lib/nat.g".
Include "fiber.g".
Include "../../guru-lang/lib/plus.g".

Define nat_pos : type := <fiber nat bool isZ ff>.

Define nat_to_nat_pos := 
fun( n : nat )( u : { (isZ n) = ff } ) : nat_pos. 
  (mk_fiber2 nat bool isZ ff n u).
  
Define nat_to_nat_pos_total : Forall( n : nat )( u : { (isZ n) = ff } ). Exists( z : nat_pos ). { (nat_to_nat_pos n u) = z } :=
foralli( n : nat )( u : { (isZ n) = ff } ).
  existsi (mk_fiber2 nat bool isZ ff n u) { (nat_to_nat_pos n u) = * }
          join (nat_to_nat_pos n u) (mk_fiber2 nat bool isZ ff n u).
Total nat_to_nat_pos nat_to_nat_pos_total.


Define nat_pos_to_nat := fun( n : nat_pos ) : nat. (fiber_data nat bool isZ ff n).

Define nat_pos_to_nat_total : Forall( n : nat_pos ). Exists( z : nat ). { (nat_pos_to_nat n) = z } :=
foralli( n : nat_pos ).
  existsi (fiber_data nat bool isZ ff n) { (nat_pos_to_nat n) = * }
          join (nat_pos_to_nat n) (fiber_data nat bool isZ ff n).
Total nat_pos_to_nat nat_pos_to_nat_total.


Define nat_pos_pf : Forall( n : nat_pos ). { (isZ (nat_pos_to_nat n)) = ff } := 
foralli( n : nat_pos ).
   trans cong (isZ *) join (nat_pos_to_nat n) (fiber_data nat bool isZ ff n)
         [fiber_pf2 nat bool isZ ff n].




%note the order of arguments here, RHS comes first
Define lt_nat_pos := 
fun( n : nat_pos )( x : nat ) : bool. 
  (lt x (nat_pos_to_nat n)).
  
Define lt_nat_pos_total : Forall( n : nat_pos )( x : nat ). Exists( z : bool ). { (lt_nat_pos n x) = z } :=
foralli( n : nat_pos )( x : nat ).
  existsi (lt x (nat_pos_to_nat n)) { (lt_nat_pos n x) = * } 
          join (lt_nat_pos n x) (lt x (nat_pos_to_nat n)).
Total lt_nat_pos lt_nat_pos_total.

