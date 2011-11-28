Include "nat_mod.g".
Include "group.g".



Define plus_mod :=        %DO_THIS
fun( n : nat_mod )( n1 n2 : <nat_mod n> ) : < nat_mod n >.
  abort <nat_mod n>.



Define group_nat_mod_P := fun( n : nat_mod ).< group <nat_mod n> (plus_mod n) >.


%-
Define group_nat_mod_p :=
fun( n : nat_mod ) : <group_nat_mod_P n>.
  (group_p <nat_mod n> (plus_mod n) Z
           ).
-%
