
Include "../lib/nat.g"
Include "../lib/bool.g"
Include "../lib/minus.g"

%-
Define myproof :=
  foralli(a b : nat)(x:{ (lt a b) = tt } ).
  unjoin x by with
    | foralli(p2 : { a = Z })(b' : nat)(p1 : { b = (S b') }).
      trans : { b = (S b') } p1
            : { (S b') != Z } clash (S b') Z
    | foralli(a' : nat)(p5 : { a = (S a') })(b' : nat)(p4 : { b = (S b') })
             (u : { (lt a' b') = tt }).
      trans : { b = (S b') } p4
            : { (S b') != Z } clash (S b') Z
  end.
-%

     %-
Define eqnat : Fun(^ #owned n m:nat).bool :=
  fun eqnat(^ #owned n m:nat):bool.
    match ! n with
      Z => match ! m with
             Z => tt
           | S m' => ff
           end
   | S n' => match ! m with
               Z => ff
             | S m' => (eqnat n' m')
             end
   end
   -%
Define eqnatEq2 : Forall(n m:nat)(u:{(eqnat n m) = tt}). { n = m } :=
  induction(n:nat) return
    Forall(m:nat)(u:{(eqnat n m) = tt}). { n = m } 
  with
    | Z =>
      foralli(m: nat)(u : { (eqnat n m) = tt }).
      lemma n_eq in
      unjoin u by with
      | foralli(p0 : { m = Z }).
        trans : { n = Z } n_eq
              : { Z = m } symm p0
      end 
    | S z' =>
      foralli(m: nat)(u : { (eqnat n m) = tt }).
      lemma n_eq in
      unjoin u by with
      | foralli(n' : nat)(p4 : { z' = n' })(m' : nat)(p3 : { m = (S m') })
        (u : { (eqnat n' m') = tt }).
        lemma 
          : { (eqnat z' m') = tt }
            trans : { (eqnat z' m') = (eqnat n' m') } cong (eqnat * m') p4
                  : { (eqnat n' m') = tt } u
        in
            
        hypjoin n m by
          : { z' = m' } [n_IH z' m' ##]
          : { m = (S m') } p3
          : { n = (S z') } n_eq
        end
      end
  end.

Define minus_lt2 : Forall
	(a b:nat)(u1:{ (le b a) = tt })(u2:{ (lt Z b) = tt }).{ (lt (minus a b) a) = tt }
	:=
  foralli(a: nat).
  induction (b:nat) return
    Forall(u1:{ (le b a) = tt })(u2:{ (lt Z b) = tt }).{ (lt (minus a b) a) = tt }
  with

    %- Z =>
       unjoin u2 by b_eq proving Forall(u1:{ (le b a) = tt })(u2:{ (lt Z b) = tt }).{ (lt (minus a b) a) = tt }
     | S b' => ...

     -%

    | default nat =>
      foralli(u1:{ (le b a) = tt })(u2:{ (lt Z b) = tt }).
      unjoin u2 by with
      | foralli(b' : nat)(b_eq : { b = (S b') }).
        lemma b_eq in
        unjoin u1 by with
        | foralli(n' : nat)(a' : nat)(a_eq : { a = (S a') })(u : { (eqnat n' a') = tt }).          
          lemma 
            : { (minus a b) = (minus a' b') }
              hypjoin (minus a b) (minus a' b') by a_eq b_eq end
          in
          case b' with
            | Z =>
              lemma 
                : { (minus a b) = a' }
                  trans : { (minus a b) = (minus a' b') } ##
                  trans : { (minus a' b') = (minus a' Z) } cong (minus a' *) b'_eq
                        : { (minus a' Z) = a' } join (minus a' Z) a'
              in
              hypjoin (lt (minus a b) a) tt by
                : { (minus a b) = a' } ##
                : { a = (S a') } a_eq
                : { (lt a' (S a')) = tt } [lt_S a']
              end
            | S b'' =>
              abbrev x = (minus a (S b')) in
              lemma 
                : { (lt Z b') = tt } 
                  hypjoin (lt Z b') tt by b'_eq end
                
                : { (lt b' b) = tt } 
                  transs
                    : { (lt b' b) = (lt b' (S b')) } cong (lt b' *) b_eq
                    : { (lt b' (S b')) = tt } [lt_S b'] 
                  end

                : { (lt b' a) = tt }
                  [ltle_trans b' b a ## u1]

                : { (le b' a) = tt }
                  [lt_implies_le b' a ##]

                
                : { (lt (S x) a) = tt }
                  hypjoin (lt (S x) a ) tt by
                    : { (minus a b') = (S x) } [minusS2 a b' ##]
                    : { (lt (minus a b') a) = tt } [b_IH b' ## ##]
                  end

                : { (lt x a) = tt }
                  [lt_trans x (S x) a [lt_S x] ##]
              in

              hypjoin (lt (minus a b) a) tt by
                : { (lt x a) = tt } ##
                : { b = (S b') } b_eq
              end              
          end
        end 
      end
  end.


%-
    | Z =>
      foralli(u1:{ (le b a) = tt })(u2:{ (lt Z b) = tt }).
      contra 
        trans symm b_eq
              [lt_implies_not_zero Z b u2]

        { (lt (minus a b) a) = tt }
    | S b' =>
      foralli(u1:{ (le b a) = tt })(u2:{ (lt Z b) = tt }).
      
      case a with
        | Z =>
          contra
            abbrev Z_lt_a = [ltle_trans Z b a u2 u1] in 
            trans [lt_implies_not_zero Z a Z_lt_a]
                  symm a_eq

            { (lt (minus a b) a) = tt }
        | S a' =>
          abbrev stripped = 
            hypjoin (minus a b) (minus a' b') by a_eq b_eq end
          in
          case b' with
            | Z =>
              abbrev a_minus_b_eq_a' =
                trans stripped
                trans cong (minus a' *) b'_eq
                      join (minus a' Z) a'
              in
              trans cong (lt * a) a_minus_b_eq_a'
              trans cong (lt a' *) a_eq 
                    [lt_S a']
            | S b'' =>
              abbrev z_lt_b' = hypjoin (lt Z b') tt by b'_eq end in
              abbrev b'_lt_b = 
                trans cong (lt b' *) b_eq
                      [lt_S b']
              in
              abbrev b'_lt_a = [ltle_trans b' b a b'_lt_b u1] in
              abbrev b'_le_a = [lt_implies_le b' a b'_lt_a] in
              abbrev x = (minus a (S b')) in
              abbrev Sx_lt_a = 
                trans cong (lt * a) 
                           symm [minusS2 a b' b'_lt_a] 
                      [b_IH b' b'_le_a z_lt_b']
              in
              abbrev x_lt_a = [lt_trans x (S x) a [lt_S x] Sx_lt_a] in

              trans cong (lt * a)
                         hypjoin (minus a b) x by b_eq end 
                    x_lt_a
          end % b'
      end % a
  end. %b
-%

Classify eqnatEq. 
