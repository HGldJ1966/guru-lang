Include "nat.g".
Include "plus.g".

Define minus : Fun(a b:nat).nat :=
  fun minus(a b:nat):nat.
  match b by bp bt return nat with
    Z => a
  | S b' =>
      match a by ap at return nat with
        Z => abort nat
      | S a' => (minus a' b')
      end
  end.

Define minus_tot : Forall(a b:nat)(u:{ (lt a b) = ff }).Exists(c:nat).{ (minus a b) = c } :=
  induction(a:nat) by ap at IHa return Forall(b:nat)(u:{ (lt a b) = ff }).Exists(c:nat).{ (minus a b) = c } with
    Z =>
      induction(b:nat) by bp bt IHb return Forall(u:{ (lt a b) = ff }).Exists(c:nat).{ (minus a b) = c } with
        Z =>
          foralli(u:{ (lt a b) = ff }).
            existsi a { (minus a b) = * }
              hypjoin (minus a b) a by bp end
      | S b' =>
          foralli(u:{ (lt a b) = ff }).
            contra trans symm u
                   trans hypjoin (lt a b) tt by ap bp end
                         clash tt ff
              Exists(c:nat).{ (minus a b) = c }
      end
  | S a' =>
      induction(b:nat) by bp bt IHb return Forall(u:{ (lt a b) = ff }).Exists(c:nat).{ (minus a b) = c } with
        Z =>
          foralli(u:{ (lt a b) = ff }).
            existsi a { (minus a b) = * }
              hypjoin (minus a b) a by bp end
      | S b' =>
          foralli(u:{ (lt a b) = ff }).
            abbrev lt_a'_b' = trans symm [S_lt_S a' b']
                              trans cong (lt * (S b')) symm ap
                              trans cong (lt a *) symm bp
                                    u in
            existse [IHa a' b' lt_a'_b']
              foralli(c':nat)(cpf:{ (minus a' b') = c' }).
                existsi c' { (minus a b) = * }
                  trans hypjoin (minus a b) (minus a' b') by ap bp end
                        cpf
      end
  end.

Define minus_tot2 : Forall(a b:nat)(u:{ (le a b) = tt }).
                      Exists(c:nat).{ (minus b a) = c } :=
  foralli(a b:nat)(u:{ (le a b) = tt }).
    [minus_tot b a [le_tt_implies_lt_ff a b u]].

Define minusS1 : Forall(a b:nat)(u:{ (lt a b) = ff }).{ (minus (S a) b) = (S (minus a b)) } :=
  induction(a:nat) by ap at IHa return Forall(b:nat)(u:{ (lt a b) = ff }).{ (minus (S a) b) = (S (minus a b)) } with
    Z =>
      induction(b:nat) by bp bt IHb return Forall(u:{ (lt a b) = ff }).{ (minus (S a) b) = (S (minus a b)) } with
        Z =>
          foralli(u:{ (lt a b) = ff }).
            trans cong (minus (S a) *) bp
            trans join (minus (S a) Z)
                       (S (minus a Z))
                  cong (S (minus a *)) symm bp
      | S b' =>
          foralli(u:{ (lt a b) = ff }).
            contra trans join tt
                              (lt Z (S b'))
                   trans cong (lt * (S b')) symm ap
                   trans cong (lt a *) symm bp
                   trans u
                         clash ff tt
              { (minus (S a) b) = (S (minus a b)) }
      end
  | S a' =>
      induction(b:nat) by bp bt IHb return Forall(u:{ (lt a b) = ff }).{ (minus (S a) b) = (S (minus a b)) } with
        Z =>
          foralli(u:{ (lt a b) = ff }).
            trans cong (minus (S a) *) bp
            trans join (minus (S a) Z)
                       (S (minus a Z))
                  cong (S (minus a *)) symm bp
      | S b' =>
          foralli(u:{ (lt a b) = ff }).
            abbrev u' = symm trans symm u
                             trans cong (lt * b) ap
                             trans cong (lt (S a') *) bp
                                   join (lt (S a') (S b'))
                                        (lt a' b') in
            trans cong (minus (S *) b) ap
            trans cong (minus (S (S a')) *) bp
            trans join (minus (S (S a')) (S b'))
                       (minus (S a') b')
            trans [IHa a' b' u']
            trans join (S (minus a' b'))
                       (S (minus (S a') (S b')))
            trans cong (S (minus * (S b'))) symm ap
                  cong (S (minus a *)) symm bp
      end
  end.

Define x_minus_x : Forall(a:nat).{ (minus a a) = Z } :=
  induction(a:nat) by ap at IHa return { (minus a a) = Z } with
    Z =>
      trans cong (minus * *) ap
            join (minus Z Z) Z
  | S a' =>
      trans cong (minus * *) ap
      trans join (minus (S a') (S a'))
                 (minus a' a')
            [IHa a']
  end.

Define minus_eq_Z : Forall(a b:nat)(u:{(minus a b) = Z}). { a = b } :=
  induction(a:nat) return Forall(b:nat)(u:{(minus a b) = Z}). { a = b } with
    Z => foralli(b:nat)(u:{(minus a b) = Z}).
           case b with
             Z => hypjoin a b by a_eq b_eq end
           | S b' => contra trans trans hypjoin abort ! (minus a b)
                                        by a_eq b_eq end
                                    u
                            symm aclash Z
                     { a = b}
           end
  | S a' => 
    foralli(b:nat)(u:{(minus a b) = Z}).
      case b with
        Z => contra trans trans hypjoin (S a') (minus a b) by a_eq b_eq end
                                u
                          clash Z (S a')
               { a = b }
      | S b' => 
        hypjoin a b 
        by [a_IH a' b' hypjoin (minus a' b') Z by a_eq b_eq u end]
           a_eq b_eq end
      end
  end.

Define minusS2 : Forall(a b:nat)(u:{ (lt b a) = tt }).
                   { (minus a b) = (S (minus a (S b))) } :=
  induction(a:nat) by ap at IHa return Forall(b:nat)(u:{ (lt b a) = tt }).{ (minus a b) = (S (minus a (S b))) } with
    Z =>
      foralli(b:nat)(u:{ (lt b a) = tt }).
        contra trans symm u
               trans cong (lt b *) ap
               trans [lt_Z b]
                     clash ff tt
          { (minus a b) = (S (minus a (S b))) }
  | S a' =>
      foralli(b:nat)(u:{ (lt b a) = tt }).
        [ induction(z:bool) by zp zt IHz return Forall(zpf:{ (lt (S b) a') = z }).{ (minus a b) = (S (minus a (S b))) } with
            ff =>
              foralli(zpf:{ (lt (S b) a') = z }).
                % (le a' (S b)) = tt
                abbrev le_a'_Sb = [ltff_le (S b) a' trans zpf zp] in
                % now, either
                %   a' = S b  -->  minus a b = S S Z = S minus a S b
                %   a' < S b  -->  a' < S b < S a, so  a = S b  and  minus a b = S minus a S b
                [ induction(z2:bool) by z2p z2t IHz2 return Forall(z2pf:{ (eqnat a' (S b)) = z2 }).{ (minus a b) = (S (minus a (S b))) } with
                    ff =>
                      foralli(z2pf:{ (eqnat a' (S b)) = z2 }).
                        %   a' < S b  -->  a' < S b < S a, so  a = S b  and  minus a b = S minus a S b
                        abbrev lt_a'_Sb = symm trans symm le_a'_Sb
                                               trans join (le a' (S b))
                                                          (or (lt a' (S b)) (eqnat a' (S b)))
                                               trans cong (or (lt a' (S b)) *) trans z2pf z2p
                                                     [or_def2ff terminates (lt a' (S b)) by lt_total] in
                        abbrev lt_Sb_SSa' = trans cong (lt (S b) (S *)) symm ap
                                            trans join (lt (S b) (S a))
                                                       (lt b a)
                                                  u in
                        abbrev a_is_Sb = trans ap symm [ltltSS a' (S b) lt_a'_Sb lt_Sb_SSa'] in
                        trans cong (minus * b) a_is_Sb
                        trans [minusS1 b b [x_lt_x b]]
                        trans join (S (minus b b))
                                   (S (minus (S b) (S b)))
                              cong (S (minus * (S b))) symm a_is_Sb
                  | tt =>
                      foralli(z2pf:{ (eqnat a' (S b)) = z2 }).
                        abbrev a'_is_Sb = [eqnatEq a' (S b) trans z2pf z2p] in
                        trans cong (minus * b) ap            % minus (S a') b
                        trans cong (minus (S *) b) a'_is_Sb  % minus (S (S b)) b
                        trans [minusS1 (S b) b [ltff_S2 b b [x_lt_x b]]]
                        trans cong (S *)
                                   trans [minusS1 b b [x_lt_x b]]
                                         cong (S *)
                                              [x_minus_x b]
                              symm trans cong (S (minus * (S b))) ap
                                   trans cong (S (minus (S a') *)) symm a'_is_Sb
                                         cong (S *)
                                              trans [minusS1 a' a' [x_lt_x a']]
                                                    cong (S *)
                                                         [x_minus_x a']
                  end terminates (eqnat a' (S b)) by eqnatTot
                      join (eqnat a' (S b)) (eqnat a' (S b)) ]
          | tt =>
              foralli(zpf:{ (lt (S b) a') = z }).
                % (S (minus a' b)) = (S (minus a (S b)))
                symm trans symm cong (S *)
                                     trans [IHa a' b [lt_S2 b a' trans zpf zp]]
                                     trans symm [minusS1 a' (S b) [lt_ltff (S b) a' trans zpf zp]]
                                           cong (minus * (S b))
                                                symm ap
                     trans symm [minusS1 a' b [lt_ltff b a' [lt_S2 b a' trans zpf zp]]]
                           cong (minus * b) symm ap
          end terminates (lt (S b) a') by lt_total
              join (lt (S b) a') (lt (S b) a') ]
  end.

% just for symmetry with plusZ
Define minusZ : Forall(a:nat).{ (minus a Z) = a } :=
  foralli(a:nat).
    join (minus a Z) a.

Define minus_plus1 : Forall(a b:nat).{ (minus (plus a b) a) = b } :=
  induction(a:nat) by ap at IHa return Forall(b:nat).{ (minus (plus a b) a) = b } with
    Z =>
      foralli(b:nat).
        trans cong (minus (plus * b) *) ap
              join (minus (plus Z b) Z) b
  | S a' =>
      foralli(b:nat).
        symm trans symm [IHa a' b]
             trans join (minus (plus a' b) a')
                        (minus (plus (S a') b) (S a'))
                   cong (minus (plus * b) *) symm ap
  end.

Define minus_plus2 : Forall(a b:nat).{ (minus (plus a b) b) = a } :=
  induction(a:nat) by ap at IHa return Forall(b:nat).{ (minus (plus a b) b) = a } with
    Z =>
      foralli(b:nat).
        trans cong (minus (plus * b) b) ap
        trans join (minus (plus Z b) b)
                   (minus b b)
        trans [x_minus_x b]
              symm ap
  | S a' =>
      induction(b:nat) by bp bt IHb return { (minus (plus a b) b) = a } with
        Z =>
          trans cong (minus (plus a *) *) bp
          trans cong (minus * Z) [plusZ a]
                [minusZ a]
      | S b' =>
          symm trans symm [IHb b'] % (minus (plus a b') b') = a
               trans join (minus (plus a b') b')
                          (minus (S (plus a b')) (S b'))
               trans cong (minus * (S b'))
                          symm [plusS a b']
                     cong (minus (plus a *) *)
                          symm bp
      end
  end.

Define minus_le : Forall(x y z:nat)(u:{ (minus x y) = z }).{ (le z x) = tt } :=
  induction(x:nat) by xp xt IHx return Forall(y z:nat)(u:{ (minus x y) = z }).{ (le z x) = tt } with
    Z =>
      induction(y:nat) by yp yt IHy return Forall(z:nat)(u:{ (minus x y) = z }).{ (le z x) = tt } with
        Z =>
          induction(z:nat) by zp zt IHz return Forall(u:{ (minus x y) = z }).{ (le z x) = tt } with
            Z =>
              foralli(u:{ (minus x y) = z }).
                [eq_le z x trans zp symm xp]
          | S z' =>
              foralli(u:{ (minus x y) = z }).
                contra trans symm u
                       trans cong (minus * y) xp
                       trans cong (minus Z *) yp
                       trans join (minus Z Z) Z
                             symm trans zp
                                        clash (S z') Z
                  { (le z x) = tt }
          end
      | S y' =>
          foralli(z:nat)(u:{ (minus x y) = z }).
            contra trans symm u
                   trans cong (minus x *) yp
                   trans cong (minus * (S y')) xp
                   trans join (minus Z (S y'))
                              abort !
                         aclash z
              { (le z x) = tt }
      end
  | S x' =>
      induction(y:nat) by yp yt IHy return Forall(z:nat)(u:{ (minus x y) = z }).{ (le z x) = tt } with
        Z =>
          induction(z:nat) by zp zt IHz return Forall(u:{ (minus x y) = z }).{ (le z x) = tt } with
            Z =>
              foralli(u:{ (minus x y) = z }).
                trans cong (le * x) zp
                      [Z_le x]
          | S z' =>
              foralli(u:{ (minus x y) = z }).
                [eq_le z x trans symm u
                           trans cong (minus x *) yp
                                 [minusZ x]]
          end
      | S y' =>
          foralli(z:nat)(u:{ (minus x y) = z }).
            abbrev u' = symm trans symm u
                             trans cong (minus * y) xp
                             trans cong (minus (S x') *) yp
                                   join (minus (S x') (S y'))
                                        (minus x' y') in
            symm trans symm [le_S3 z x' [IHx x' y' z u']]
                       cong (le z *) symm xp
      end
  end.

Define Z_minus : Forall(y z:nat). { (minus Z y) != (S z) } :=
  foralli(y z:nat).
  case y with
    Z => trans hypjoin (minus Z y) Z by y_eq end
               clash Z (S z)
  | S y' =>  trans hypjoin (minus Z y) abort ! by y_eq end
                   aclash (S z)
  end.

Define minus_S_lt : Forall(x y z:nat)(u:{ (minus x y) = (S z)}).
                     { (lt y x) = tt } :=
  induction(x:nat) return Forall(y z:nat)(u:{ (minus x y) = (S z)}).
                            { (lt y x) = tt } with
    Z => foralli(y z:nat)(u:{ (minus x y) = (S z)}).
         contra
           trans symm u 
           trans cong (minus * y) x_eq
                 [Z_minus y z]
           { (lt y x) = tt }
  | S x' => 
    foralli(y z:nat)(u:{ (minus x y) = (S z)}).
    case y with
      Z => hypjoin (lt y x) tt
           by x_eq y_eq end
    | S y' => 
      trans hypjoin (lt y x) (lt y' x') by x_eq y_eq end
            [x_IH x' y' z hypjoin (minus x' y') (S z) by x_eq y_eq u end]
    end
  end.