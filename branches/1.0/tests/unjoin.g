
Include "../lib/nat.g"
Include "../lib/bool.g"
Include "../lib/minus.g"
Include "../lib/vec.g"

%-
Define myproof :=
  foralli(a b : nat)(x:{ (lt a b) = tt } ).
  unjoin x with
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
    unjoin u with
    | foralli(p0 : { m = Z }).
      trans : { n = Z } n_eq
            : { Z = m } symm p0
    end 
  | S n' =>
    foralli(m: nat)(u : { (eqnat n m) = tt }).
    lemma n_eq in
    unjoin u with
    | foralli(m' : nat)(p3 : { m = (S m') })(u : { (eqnat n' m') = tt }).            
      hypjoin n m by
        : { n' = m' } [n_IH n' m' u]
        : { m = (S m') } p3
        : { n = (S n') } n_eq
      end
    end
  end.
  %-
Define eqnatNeq2 : Forall(n m:nat)(u:{(eqnat n m) = ff}). { n != m } :=
  induction (n:nat) return
    Forall(m:nat)(u:{(eqnat n m) = ff}). { n != m }
  with
  | Z =>
    foralli(m:nat)(u:{(eqnat n m) = ff}).
    lemma n_eq in
    unjoin u with
    | foralli(m' : nat)(p5 : { m = (S m') }).
      transs 
        : { n = Z } n_eq
        : { Z != (S m') } clash Z (S m')
        : { (S m') = m } symm p5  
      end
    end
  | S n' =>
    foralli(m:nat)(u:{(eqnat n m) = ff}).
    lemma n_eq in
    unjoin u with
    | foralli(p6 : { m = Z }).
      transs
        : { n = (S n') } n_eq
        : { (S n') != Z } clash (S n') Z
        : { Z = m } symm p6
      end
    | foralli(m' : nat)(p7 : { m = (S m') })(u : { (eqnat n' m') = ff }).
      lemma 
        : { (S n') != (S m') } 
          ncong (S *) (S n') (S m') 
                : { n' != m' } [n_IH n' m' u]         
      in
      transs 
        : { n = (S n') } n_eq
        : { (S n') != (S m') } ##
        : { (S m') = m } symm p7
      end
    end
  end

Define neqEqnat2 : Forall(n m : nat)(u:{n != m}).{ (eqnat n m) = ff } :=
  foralli(n m : nat)(u:{n != m}).
  case (eqnat n m) by v ign with
  | ff =>
    v
  | tt =>
    contra 
      trans : { n = m } [eqnatEq2 n m v]
            : { m != n } symm u

      { (eqnat n m) = ff } 
  end.
-%

%- unjoin wouldn't help here... it could enable us to avoid induction,
   but I think induction is more straightforward and compact.

Define eqnat_refl2 : Forall(x:nat).{ (eqnat x x) = tt } :=
  foralli(x:nat).
  case (eqnat x x) by u ign with
  | ff =>
    unjoin u by
      
    end
  | tt =>
  end
-%

% eqnat_symm - unjoin wouldn't help here

% Sneq_neq2 - unjoin wouldn't help here
    
% x_lt_x - wouldn't help

% x_eqnat_x - wouldn't help

% eqEqnat - wouldn't help

% x_le_x - wouldn't help

% leZ - wouldn't help

% unjoin should be symmetric - don't give any lemma special status. instead
% keep track of unjoined lemmas, and systematically unjoin all lemmas recursively.
%
% unjoin with
% | 
% |
% end.
%
% This would be based on all lemmas in the lemmas set.

%-
Define lt_Z : Forall(a:nat).{ (lt a Z) = ff } :=
  match (lt a Z) by v ign with
  | ff =>
    v
  | tt =>
    unjoin v with
    | contradiction =>
    end
  end.
 -%
 
 %-
Define lt_leff : Forall(a b:nat)(u:{ (lt a b) = tt }).{ (le b a) = ff }
  :=
  induction(a b: nat) return 
    return Forall(u:{ (lt a b) = tt }).{ (le b a) = ff }
  with
  | Z => 
    foralli(u:{ (lt a b) = tt }).
    unjoin u with
    | contradiction.
    end
  | S n' =>
  end
-%

%- Define lt_ltff -- a lot like lt_leff -%

%-
Define lt_lt_impliesEq2: Forall(x y:nat)(u: {(lt x y) = ff})(v:{(lt y x) = ff}).{x = y} :=
  induction(x:nat) return 
    Forall(y:nat)(u: {(lt x y) = ff})(v:{(lt y x) = ff}).{x = y} 
  with
  | Z =>
    foralli(y:nat)(u: {(lt x y) = ff})(v:{(lt y x) = ff}).
    lemma x_eq in
    unjoin u with 
    | foralli(p8 : { y = Z }).
      trans : { x = Z } x_eq
            : { Z = y } symm p8
    end
  | S x' =>
    foralli(y:nat)(u: {(lt x y) = ff})(v:{(lt y x) = ff}).
    lemma x_eq in
    unjoin u with
    | foralli(p10 : { y = Z }).
      lemma p10 in
      unjoin v with
              
    | foralli(b' : nat)(p11 : { y = (S b') })(u : { (lt x' b') = ff }).

    end
  end.
-%


%-
Define vec_vecc_shift2 : 
  Forall(A: type)
        (n: nat)
        (v: <vec A n>)
        (m: nat)
        (u: { (lt m n) = tt } )
        (a: A)
        .
        { (vec_get v m) = (vec_get (vecc a v) (S m)) }
  :=   
  foralli(A: type)(n: nat)(v: <vec A n>)(m: nat)(u: { (lt m n) = tt } )
         (a: A).

    lemma


    unjoin u with
    | foralli(p10 : { m = Z })(b' : nat)(p9 : { n = (S b') }).
      
    | foralli(a' : nat)(p13 : { m = (S a') })(b' : nat)
             (p12 : { n = (S b') })(u : { (lt a' b') = tt }).
    end.

-%

Define minus_lt2 : Forall
	(a b:nat)(u1:{ (le b a) = tt })(u2:{ (lt Z b) = tt }).{ (lt (minus a b) a) = tt }
	:=
  foralli(a: nat).
  induction (b:nat) return
    Forall(u1:{ (le b a) = tt })(u2:{ (lt Z b) = tt }).{ (lt (minus a b) a) = tt }
  with
    | Z =>
      foralli(u1:{ (le b a) = tt })(u2:{ (lt Z b) = tt }).
      lemma b_eq in
      unjoin u2 contra { (lt (minus a b) a) = tt }
    | S b' =>
      foralli(u1:{ (le b a) = tt })(u2:{ (lt Z b) = tt }).
      lemma b_eq in
      unjoin u1 with
      %-
      | foralli(a0 : nat)(a_eq : { a = (S a0) })(p3 : { b' = Z })
               (p1 : { a0 = Z })(u : { (eqnat b' a0) = tt }).

        lemma 
          : { (minus a b) = Z }
            hypjoin (minus a b) Z by
              : { a = (S a0) } a_eq
              : { b = (S b') } b_eq
              : { b' = Z } p3
              : { a0 = Z } p1 
            end
        in

        hypjoin (lt (minus a b) a) tt by
          : { (minus a b) = Z } ##
          : { a = (S a0) } a_eq
          : { a0 = Z } p1
        end


      | foralli(a0 : nat)(p7 : { a = (S a0) })(b'0 : nat)
               (p6 : { b' = (S b'0) })(p4 : { a0 = Z })
               (u : { (eqnat b' a0) = tt }).
        
        lemma p6 p4 in
        unjoin u contra { (lt (minus a b) a) = tt }
          

      | foralli(a0 : nat)(p7 : { a = (S a0) })(b'0 : nat)
               (p6 : { b' = (S b'0) })(a00 : nat)(p5 : { a0 = (S a00) })
               (u : { (lt b'0 a00) = ff })(u : { (eqnat b' a0) = tt }).

        

      (a0 : nat)(p15 : { a = (S a0) })(p11 : { b' = Z })
      (a00 : nat)(p10 : { a0 = (S a00) })

      (a0 : nat)(p15 : { a = (S a0) })(b'0 : nat)
      (p14 : { b' = (S b'0) })(a00 : nat)
      (p13 : { a0 = (S a00) })(u : { (lt b'0 a00) = tt })
      end.

      -%
      %-
      | foralli(a0 : nat)(p9 : { a = (S a0) })(u : { (eqnat b' a0) = tt }).
      
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
          -%
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

Classify neqEqnat2. 