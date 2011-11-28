Include "../../guru-lang/lib/nat.g".
Include "logic_defs.g".
Include "subset_rel.g".


%-

-%

%well ordering principle
%-
Define predicate well_ordering_principle_P :=
fun( f : Fun( n : nat ).nat ).
    Exists( a : <range nat nat f> ).
      Forall( b : <range nat nat f> ). { (le (range_data nat nat f a) (range_data nat nat f b)) = tt }
      
Define well_ordering_principle_p :=
fun( f : Fun( n : nat ).nat )( fne : <range_nonempty_P nat nat f> ) : <well_ordering_principle_P f fne>.   
  ...
-%


%============= statement b is a divisor of a
Define type_family_abbrev divisor_P := fun( a b : nat ).<range_P nat nat (mult b) a>.
                 
%============= a divisor of a
Inductive divisor : Fun( a : nat ) :=
  mk_divisor : Fun( a b : nat )( u : <divisor_P a b> ).<divisor a>. 
                 
Define divisor_data :=
fun( a : nat )( d : <divisor a> ) : nat.
  match d with
    mk_divisor _ b _ => b
  end.
  
%============= statement b is a multiple of a
Define type_family_abbrev multiple_P := fun( a b : nat ).<range_P nat nat (mult a) b>.

%============= a multiple of a
Define type_family_abbrev multiple := fun( a : nat ).<range nat nat (mult a)>.



%============= statement that c is a common divisor of a and b
Define type_family_abbrev common_divisor_P := fun( a b c : nat ).<and_P <divisor_P a c> <divisor_P b c> >.
%============= a common divisor of a and b
%Define type_family_abbrev common_divisor := fun( a b : nat ). <set_intersect nat (mult a) (mult b)>.

%============= statement that c is a common divisor of a and b
Define type_family_abbrev common_mulitple_P := fun( a b c : nat ).<set_intersect_P nat (mult a) (mult b) c>.
%============= a common divisor of a and b
Define type_family_abbrev common_mulitple := fun( a b : nat ). <set_intersect nat (mult a) (mult b)>.


%-
Inductive gcd_P : Fun( a b d : nat ) :=
  gcd_p : Fun( a b d : nat )( u : <common_divisor_P a b d> )
  
  
  
Inductive lcm_P : Fun( a b d : nat ) :=
  lcm_p : Fun( a b d : nat )( u : <common_divisor_P a b d> )
  
  
-%