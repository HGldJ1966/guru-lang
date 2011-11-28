Include "logic_defs.g".


Define and_P_symm :=
fun( A B : type )( s : <and_P A B > ) : <and_P B A>.
  match s with
    and_p _ _ a b => <and_P B A b a>
  end.
  
  
Define or_P_symm :=
fun( A B : type )( s : <or_P A B > ) : <or_P B A>.
  match s with
    or_p1 _ _ a => (or_p2 B A a)
  | or_p2 _ _ b => (or_p1 A B b)
  end.