Include "nat_std.g".
Include "logic_defs.g".

%===== a negative nat, Z = -1, (S Z) = -2, etc.
Inductive neg_nat : type :=
  mk_neg_nat : Fun( n : nat ).neg_nat.

Define neg_nat_data :=
fun( n : neg_nat ) : nat.
  match n with
    mk_neg_nat n' => n'
  end.

%===== Z, the integers
Define type_family_abbrev int := <or_P nat neg_nat>.

Define int_pos := fun( n : nat ) : int. (or_p1 nat neg_nat n).
Define int_neg := fun( n : nat ) : int. (or_p2 nat neg_nat (mk_neg_nat n)).

%===== successor of an integer
Define int_S :=
fun( n : int ) : int.
  match n with
    or_p1 n' => (int_pos (S n'))
  | or_p2 n' => 
      match n'
        Z => (int_pos Z)
      | S n'' => (int_neg n'')
      end
  end.

%===== predecessor of an integer
Define int_P :=
fun( n : int ) : int.
  match n with
    or_p1 n' =>
      match n' with
        Z => (int_neg Z)
      | S n'' => (int_pos n'')
      end
  | or_p2 n' => (int_neg (S n'))
  end.
  
%===== absolute value
Define int_abs :=
fun( n1 n2 : int ) : nat.
  match n1 with
    or_p1 n1' => n1'
  | or_p2 n1' => (S (neg_nat_data n1'))
  end.

%===== plus for integers
Define int_plus :=
fun( n1 n2 : int ) : int.
  match n1 with
    or_p1 n1' => 
      match n1' with
        Z => n2
        S n1'' => (S_int (int_plus (int_pos n1'') n2))
      end
  | or_p2 n1' => 
      (P_int match (neg_nat_data n1') with
               Z => n2
             | S n1'' => (int_plus (int_neg n1'') n2)
             end )
  end.

%===== minus for integers
Define int_minus :=
fun( n1 n2 : int ) : int.
  match n1 with
    or_p1 n1' => 
      match n1' with
        Z => n2
        S n1'' => (P_int (int_minus (int_pos n1'') n2))
      end
  | or_p2 n1' => 
      (S_int match (neg_nat_data n1') with
               Z => n2
             | S n1'' => (int_minus (int_neg n1'') n2)
             end )
  end.


%-
%===== multiply for integers
Define int_mult :=
fun( n1 n2 : int ).
  match n1 with
    or_p1 n1' => 
      match n1' with
        Z => Z
        S n1'' => (int_plus n2 (int_mult (int_pos n1'') n2))
      end
  | or_p2 n1' => 
      match (neg_nat_data n1') with
        Z => Z
      | S n1'' => (int_minus n2 (int_mult (int_neg n1'') n2))
      end
  end.
-%
