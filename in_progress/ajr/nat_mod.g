Include "../../guru-lang/lib/nat.g".
Include "../../guru-lang/lib/minus.g".
Include "nat_std.g".


Define type_family_abbrev nat_mod := fun( n : nat_pos ). <fiber nat bool (lt_nat_pos n) tt>.


Define nat_to_nat_mod : Fun( n : nat_pos )( x : nat ). <nat_mod n> :=
fun nat_to_nat_mod( n : nat_pos )( x : nat ) : <nat_mod n>.
  match (lt_nat_pos n x) by ul uL with
    ff => (nat_to_nat_mod n (minus x (nat_pos_to_nat n)))
  | tt => (mk_fiber2 nat bool (lt_nat_pos n) tt x ul)
  end.

Define lt_S_implies_le : Forall( n1 n2 : nat )( u : { (lt n1 (S n2)) = tt } ). { (le n1 n2) = tt } :=
induction( n1 : nat) by un uN IHn1 return Forall( n2 : nat )( u : { (lt n1 (S n2)) = tt } ). { (le n1 n2) = tt } with
  Z => foralli( n2 : nat )( u : { (lt n1 (S n2)) = tt } ).
         trans cong (le * n2) un
               [Z_le n2]
| S n1' => 
    foralli( n2 : nat )( u : { (lt n1 (S n2)) = tt } ).
      case n2 with
        Z => contra trans trans symm u
                          trans cong (lt n1 (S *)) n2_eq
                          trans cong (lt * (S Z)) un
                          trans [S_lt_S n1' Z]
                                [lt_Z n1']
                          clash ff tt
                    { (le n1 n2) = tt }
      | S n2' => trans cong (le * n2) un
                 trans cong (le (S n1') *) n2_eq
                 trans [S_le_S n1' n2']
                       [IHn1 n1' n2' trans symm cong (lt n1' *) n2_eq
                                     trans symm trans cong (lt * (S n2)) un
                                                      [S_lt_S n1' n2]
                                           u]
      end
end.

Define minus_nZ_implies_lt : Forall( n1 n2 : nat )(ult:{ (lt n1 n2) = ff })
                                   ( u : { (isZ n2) = ff } ). { (lt (minus n1 n2) n1) = tt } :=
foralli( n1 n2 : nat )(ult:{ (lt n1 n2) = ff }) ( u : { (isZ n2) = ff } ).               
  case n2 with
    Z => contra trans trans symm u
                            hypjoin (isZ n2) tt by n2_eq end
                      clash tt ff
                { (lt terminates (minus n1 n2) by [minus_tot n1 n2 ult] n1) = tt  }  
  | S n2' => 
      case n1 with
        Z => contra trans trans symm ult
                                hypjoin (lt n1 n2) tt by n1_eq n2_eq end
                          clash tt ff    
                    { (lt terminates (minus n1 n2) by [minus_tot n1 n2 ult] n1) = tt  }  
      | S n1' => [lelt_trans terminates (minus n1 n2) by [minus_tot n1 n2 ult] n1' n1
                             trans cong (le * n1') hypjoin (minus n1 n2) (minus n1' n2') by n1_eq n2_eq end
                                   [minus_le n1' n2' terminates (minus n1' n2') by [minus_tot n1' n2' trans symm [S_lt_S n1' n2']
                                                                                                      trans cong (lt * (S n2')) symm n1_eq
                                                                                                      trans cong (lt n1 *) symm n2_eq
                                                                                                            ult]
                                                     refl (minus n1' n2')]
                             trans cong (lt n1' *) n1_eq 
                                   [lt_S n1'] ]
      end
  end.

%convert this to use ind_arg.g!!!

Define nat_to_nat_mod_total : Forall( n : nat_pos )( x : nat ). Exists( z : <nat_mod n> ). { (nat_to_nat_mod n x) = z } :=
foralli( n : nat_pos )( x : nat).
  [
    induction( y : nat ) by uy uY IHy return Forall( x' : nat )( u : { (lt x' y) = tt } ).
                                               Exists( z : <nat_mod n> ). { (nat_to_nat_mod n x') = z } with
      Z => foralli( x' : nat )( u : { (lt x' y) = tt } ).
             contra
                trans trans symm u 
                      trans cong (lt x' *) uy
                            [lt_Z x']
                      clash ff tt
                Exists( z : <nat_mod n> ). { (nat_to_nat_mod n x') = z }
    | S y' => 
        foralli( x' : nat )( u : { (lt x' y) = tt } ).
          case (lt_nat_pos n x') by ult uLt with
            ff => 
                  abbrev minus_tot_xn = terminates (minus x' (nat_pos_to_nat n)) by 
                                        [minus_tot x' (nat_pos_to_nat n) 
                                                   trans join (lt x' (nat_pos_to_nat n)) (lt_nat_pos n x') ult] in
                  existse [IHy y' minus_tot_xn
                                  [ltle_trans minus_tot_xn
                                              x' y' 
                                              [minus_nZ_implies_lt x' (nat_pos_to_nat n) 
                                                                   trans join (lt x' (nat_pos_to_nat n)) (lt_nat_pos n x') ult
                                                                   [nat_pos_pf n]]
                                              [lt_S_implies_le x' y' 
                                                               trans symm cong (lt x' *) uy
                                                                     u]]]
                          foralli( z : <nat_mod n> )( uz : { (nat_to_nat_mod n (minus x' (nat_pos_to_nat n))) = z } ).
                            existsi z { (nat_to_nat_mod n x') = * }
                                    trans hypjoin (nat_to_nat_mod n x') (nat_to_nat_mod n (minus x' (nat_pos_to_nat n))) by ult end
                                          uz
          | tt => abbrev ult' = trans join ((lt_nat_pos n) x') (lt_nat_pos n x') ult in
                  existsi (mk_fiber2 nat bool (lt_nat_pos n) tt x' ult') { (nat_to_nat_mod n x') = * }
                          hypjoin (nat_to_nat_mod n x') (mk_fiber2 nat bool (lt_nat_pos n) tt x' ult') by ult end
          end
    end
    (S x) x [lt_S x]].
Total nat_to_nat_mod nat_to_nat_mod_total.




Define nat_mod_to_nat : Fun( n : nat_pos )( x : <nat_mod n> ). nat :=
fun( n : nat_pos )( x : <nat_mod n> ) : nat.
  (fiber_data nat bool (lt_nat_pos n) tt x).
  
Define nat_mod_to_nat_total : Forall( n : nat_pos )( x : <nat_mod n> ). Exists( z : nat ). { (nat_mod_to_nat n x) = z } :=
foralli( n : nat_pos )( x : <nat_mod n> ).
  existsi (fiber_data nat bool (lt_nat_pos n) tt x) { (nat_mod_to_nat n x) = * }
          join (nat_mod_to_nat n x) (fiber_data nat bool (lt_nat_pos n) tt x).
Total nat_mod_to_nat nat_mod_to_nat_total.



Define nat_mod_pf : Forall( n : nat_pos )( x : <nat_mod n> ). { (lt_nat_pos n (nat_mod_to_nat n x)) = tt } :=
foralli( n : nat_pos )( x : <nat_mod n> ).
  trans cong ((lt_nat_pos n) *) join (nat_mod_to_nat n x) (fiber_data nat bool (lt_nat_pos n) tt x)
        [fiber_pf2 nat bool (lt_nat_pos n) tt x].
















Define mod : Fun( n x : nat )(u : { (isZ n ) = ff }). nat := 
fun( n x : nat )(u : { (isZ n ) = ff }) : nat.
  let n' = (nat_to_nat_pos n u) in
	(nat_mod_to_nat n' (nat_to_nat_mod n' x)).

Define mod_total : Forall( n x : nat )(u : { (isZ n ) = ff }). Exists( z : nat ). { (mod n x u) = z } :=
foralli( n x : nat )(u : { (isZ n ) = ff }).
  abbrev n' = (nat_to_nat_pos n u) in
  existsi (nat_mod_to_nat n' (nat_to_nat_mod n' x)) { (mod n x u) = * }
          join (mod n x u) (nat_mod_to_nat n' (nat_to_nat_mod n' x)).
Total mod mod_total.

Define mod_bound : Forall( n x : nat )(u : { (isZ n ) = ff }). { (lt (mod n x u) n) = tt } :=
foralli( n x : nat )(u : { (isZ n ) = ff }).
  abbrev n' = (nat_to_nat_pos n u) in
  trans join (lt (mod n x u) n) (lt_nat_pos n' (mod n x u))
  trans cong (lt_nat_pos n' *) join (mod n x u) (nat_mod_to_nat n' (nat_to_nat_mod n' x)) 
        [nat_mod_pf n' (nat_to_nat_mod n' x)].

