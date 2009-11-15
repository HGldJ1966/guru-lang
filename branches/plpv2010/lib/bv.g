%Unset "check_drop_annos_idem".

Include "pow.g".
Include "vec.g".

Define bv := <vec bool>.
Define bv_head := (vec_head bool).
Define bv_tail := (vec_tail bool).
Define bvn := (vecn bool).
Define bvc := (vecc bool).
Define bv_reverse := (vec_reverse bool). 
Define bv_get := (vec_get bool).
Define bv_append := (vec_append bool).
Define eqbv := (eqvec bool iff).
Define eqbv_eq := [eqvec_eq bool iff iff_eq].
Define eqbv_tot 
 : Forall(l:nat)(v1 v2:<bv l>). 
    Exists(b:bool). { (eqbv v1 v2) = b }
 := [eqvec_tot bool iff iff_tot].
Total eqbv eqbv_tot.
Define eqbv_refl := [eqvec_refl bool iff iff_refl].

% the least significant bit is first.

Define to_nat : Fun(spec l:nat)(c:<bv l>).nat := 
  fun to_nat(spec l:nat)(c:<bv l>):nat.
    match c by uc vc with
      vecn A' => Z
    | vecc A' l' a' c' => 
        abbrev P = inj <vec * **> symm vc in
        (condS cast a' by P 
          (mult2 (to_nat l' cast c' by cong <vec * l'> P)))
    end.

%-
Set "print_parsed".

Define to_nat_test1 := join (to_nat (mkvec ff (mult2 (pow2 (pow2 (pow2 (S Z))))))) Z.

Unset "print_parsed".
-%

Define to_nat_tot
  : Forall(l:nat)(v:<bv l>). Exists(n:nat). { (to_nat v) = n} :=
  induction(l:nat)(v:<bv l>) by uv vv IH 
  return Exists(n:nat). { (to_nat v) = n} with
    vecn A => existsi Z { (to_nat v) = *}
                hypjoin (to_nat v) Z by uv inj <vec ** *> vv end
  | vecc A l' a v' => 
      existse [IH l' cast v' by cong <vec * l'> symm inj <vec * **> vv]
      foralli(n:nat)(u:{(to_nat v') = n}).
        existse [mult_total (S (S Z)) n] 
        foralli(n2:nat)(u2:{(mult2 n) = n2}).
          [induction(b:bool) by ub ign ign 
           return Forall(bb:{a = b}). Exists(n:nat). {(to_nat v) = n} with
             ff => foralli(bb:{a = b}).
                   existsi n2 { (to_nat v) = *}
                     trans hypjoin (to_nat v) (mult2 (to_nat v'))
                            by uv trans bb ub end
                     trans cong (mult2 *) u
                           u2
           | tt => foralli(bb:{a = b}).
                   existsi (S n2) { (to_nat v) = *}
                     trans hypjoin (to_nat v) (S (mult2 (to_nat v')))
                            by uv trans bb ub end
                     trans cong (S (mult2 *)) u 
                           cong (S *) u2
           end
          cast a by symm inj <vec * **> vv join a a]
  end.

Total to_nat to_nat_tot.

Inductive to_bv_t : type :=
  mk_to_bv_t : Fun(spec l:nat)(v:<bv l>).to_bv_t.

Define to_bv : Fun(n:nat).to_bv_t := 
  fun to_bv(n:nat):to_bv_t.
    match (isZ n) with
      ff => match (to_bv (div2 n)) with
              mk_to_bv_t l v => 
                (mk_to_bv_t (S l) (bvc l (mod2 n) v))
            end
    | tt => (mk_to_bv_t Z bvn)
    end.

% Set "debug_terminates".

Define to_bv_tot : Forall(n n':nat)(u:{(le n' n) = tt}). Exists(r:to_bv_t).
                     { (to_bv n') = r} :=
  induction(n:nat) by un ign IH
  return Forall(n':nat)(u:{(le n' n) = tt}). Exists(r:to_bv_t).
          { (to_bv n') = r} with
    Z => foralli(n':nat)(u:{(le n' n) = tt}).
           existsi (mk_to_bv_t Z bvn) { (to_bv n') = *} 
             hypjoin (to_bv n') (mk_to_bv_t bvn)
             by [le_Z1 n' trans cong (le n' *) symm un u] end
  | S n1 => induction(n':nat) by un' ign ign 
            return Forall(u:{(le n' n) = tt}).Exists(r:to_bv_t).
                     { (to_bv n') = r} with
              Z => foralli(u:{(le n' n) = tt}).
                      existsi (mk_to_bv_t Z bvn) { (to_bv n') = *} 
                        hypjoin (to_bv n') (mk_to_bv_t bvn)
                        by un' end
            | S n1' => 
               foralli(u:{(le n' n) = tt}).
               abbrev d2 = terminates (div2 (S n1')) by div2_total in
               existse [IH n1 d2 
                         [le_trans d2 n1' n1 
                            [div2_le n1']
                            symm trans symm u
                                 trans cong (le * n) un'
                                 trans cong (le (S n1') *) un
                                       [S_le_S n1' n1 ]]]
               induction(r1:to_bv_t) by ur1' ign ign 
               return Forall(ur1:{(to_bv d2) = r1}).
                      Exists(r:to_bv_t). { (to_bv n') = r} with
               mk_to_bv_t l v => 
                 foralli(ur1:{(to_bv d2) = r1}).
                 abbrev r = (mk_to_bv_t (S l)
                              (bvc l terminates (mod2 n') by mod2_total v)) in
                 existsi r { (to_bv n') = *}
                   trans cong (to_bv *) un'
                         hypjoin (to_bv (S n1')) r by trans ur1 ur1' un' end
               end
            end
   end.
               
Define normalize :=
  fun normalize(spec l:nat)(v:<bv l>):to_bv_t .
    match v by uv vv with
      vecn A => (mk_to_bv_t Z bvn)
    | vecc A l' a v' =>
        abbrev P = symm inj <vec * **> vv in
        match (normalize l' cast v' by cong <vec * l'> P) with
          mk_to_bv_t l2 v2 =>
            match v2 by uv2 vv2 with
              vecn A =>
                match cast a by P with
                 ff => (mk_to_bv_t Z bvn)
               | tt => (mk_to_bv_t (S Z) (bvc Z tt bvn))
               end
            | vecc A a' l2' v2' =>
                (mk_to_bv_t (S l2) (bvc l2 cast a by P v2))
            end
         end
    end.

Define normalize_tot :=
  induction(l:nat)(v:<bv l>) 
  return Exists(r:to_bv_t). {(normalize v) = r} with
    vecn A => existsi (mk_to_bv_t Z bvn) {(normalize v) = *}
                hypjoin (normalize v) (mk_to_bv_t bvn) by v_eq end 
  | vecc A l' a v' =>
    abbrev P = symm inj <vec * **> v_Eq in
    abbrev cv' = cast v' by cong <vec * l'> P in
    existse [v_IH l' cv']
    induction(r1:to_bv_t) 
    return Forall(ur1:{(normalize v') = r1}).
           Exists(r:to_bv_t). {(normalize v) = r} with
      mk_to_bv_t rl rv =>
        foralli(ur1:{(normalize v') = r1}).
        case rv with
          vecn A =>
            abbrev ca = cast a by P in
            case ca with 
              ff => existsi (mk_to_bv_t Z bvn) {(normalize v) = *}
                      hypjoin (normalize v) (mk_to_bv_t bvn)
                      by ur1 r1_eq rv_eq v_eq ca_eq end
            | tt => existsi (mk_to_bv_t (S Z) (bvc Z tt bvn))
                     {(normalize v) = *}
                     hypjoin (normalize v) (mk_to_bv_t (bvc tt bvn))
                     by ur1 r1_eq rv_eq
                        v_eq ca_eq end
            end 
         | vecc A l2' a' v2' => 
           existsi (mk_to_bv_t (S rl) (bvc rl cast a by P rv))
             {(normalize v) = *}
             hypjoin (normalize v) 
                     (mk_to_bv_t (bvc a rv))
             by v_eq ur1 r1_eq rv_eq end
         end 
      end
  end.


Define to_nat_eq_Z1 : Forall(l:nat)(v:<bv l>)(u:{ (to_nat v) = Z}).
                       { (normalize v) = (mk_to_bv_t bvn) } :=
  induction(l:nat)(v:<bv l>) 
  return Forall(u:{ (to_nat v) = Z}).
           { (normalize v) = (mk_to_bv_t bvn) } with
    vecn A => foralli(u:{ (to_nat v) = Z}).
                hypjoin (normalize v) (mk_to_bv_t bvn) by v_eq end
  | vecc A l' a v' => 
     foralli(u:{ (to_nat v) = Z}).
     abbrev P = symm inj <vec * **> v_Eq in
     abbrev cv' = cast v' by cong <vec * l'> P in
     abbrev P1 = symm trans symm u
                        hypjoin (to_nat v) 
                                (condS a (mult2 (to_nat v')))
                        by v_eq end in
     abbrev nv' = terminates (to_nat l' cv') by to_nat_tot in
     abbrev m = terminates (mult2 nv') by mult_total in
     abbrev Pa = [condS_Z1 cast a by P m P1] in
     abbrev Pm = [condS_Z2 cast a by P m P1] in
     abbrev Pnv' = [mult_eq_Z (S Z) nv' Pm] in
       hypjoin (normalize v) (mk_to_bv_t bvn)
       by v_eq Pa [v_IH l' cv' Pnv'] end
   end.

Define to_nat_eq_Z2 : Forall(l:nat)(v:<bv l>)
                            (u: { (normalize v) = (mk_to_bv_t bvn) }).
                       { (to_nat v) = Z} :=
  induction(l:nat)(v:<bv l>) 
  return Forall(u: { (normalize v) = (mk_to_bv_t bvn) }).
                       { (to_nat v) = Z} with
    vecn A => foralli(u: { (normalize v) = (mk_to_bv_t bvn) }).
                hypjoin (to_nat v) Z by v_eq end
  | vecc A l' a v' => 
     foralli(u: { (normalize v) = (mk_to_bv_t bvn) }).
     abbrev P = symm inj <vec * **> v_Eq in
     abbrev cv' = cast v' by cong <vec * l'> P in
     abbrev nv' = terminates (normalize spec l' cv') by normalize_tot in
     case nv' with
        mk_to_bv_t l2 v2 =>
        case v2 with
          vecn A => 
            abbrev ca = cast a by P in
            case ca with
              ff => hypjoin (to_nat v) Z 
                    by v_eq ca_eq 
                       [v_IH l' cv' 
                          trans nv'_eq cong (mk_to_bv_t *) v2_eq]
                    end
            | tt => 
              contra 
                trans
                  trans symm u
                        hypjoin (normalize v) 
                                (mk_to_bv_t (bvc tt bvn))
                        by v_eq nv'_eq v2_eq ca_eq end
                  ncong (mk_to_bv_t *) 
                    (mk_to_bv_t (bvc tt bvn)) 
                    (mk_to_bv_t bvn)
                    clash (bvc tt bvn) bvn
              { (to_nat v) = Z} 
              
            end
        | vecc A a2 l2' v2' => 
          contra 
            trans
              trans symm u
                    hypjoin (normalize v) 
                            (mk_to_bv_t  (bvc a v2))
                    by v_eq nv'_eq v2_eq end
              ncong (mk_to_bv_t *) 
                (mk_to_bv_t (bvc a v2)) 
                (mk_to_bv_t bvn)
                clash (bvc a v2) bvn
           { (to_nat v) = Z} 
        end
     end
  end.

Define to_bv_nat : Forall(l:nat)(v:<bv l>).
                   { (to_bv (to_nat v)) = (normalize v) } :=
  induction(l:nat)(v:<bv l>) 
  return { (to_bv (to_nat v)) = (normalize v) } with
    vecn A => hypjoin (to_bv (to_nat v)) (normalize v) by v_eq end
  | vecc A l' a v' => 
     abbrev P = symm inj <vec * **> v_Eq in
     abbrev cv' = cast v' by cong <vec * l'> P in
     abbrev ca = cast a by P in           
     abbrev iv = terminates 
                   (condS ca 
                      terminates
                        (mult2 terminates (to_nat spec l' cv') by to_nat_tot)
                      by mult_total)
                 by condS_tot in
     abbrev P1 = hypjoin (to_nat v) iv by v_eq end in
     trans cong (to_bv *) P1
       %- { (to_bv i) = (normalize l v) } -% 
       case iv with
         Z => trans cong (to_bv *) iv_eq
              trans join (to_bv Z) (mk_to_bv_t bvn) 
                    symm [to_nat_eq_Z1 l v trans P1 iv_eq]
       | S n => abbrev nv' = terminates (normalize spec l' cv') by normalize_tot in
                case nv' with
                 mk_to_bv_t rl rv =>
                   trans cong (to_bv *) iv_eq
                   trans join (to_bv (S n))
                              match (to_bv (div2 (S n))) with
                              mk_to_bv_t v => 
                                (mk_to_bv_t (bvc (mod2 (S n)) v))
                              end
                   trans cong match * with
                              mk_to_bv_t v => 
                                (mk_to_bv_t (bvc (mod2 (S n)) v))
                              end
                           trans cong (to_bv *)
                                   trans cong (div2 *) 
                                           trans symm iv_eq
                                             join iv (condS a
                                                       (mult2 (to_nat v')))
                                         [div2_mult2 ca
                                           terminates (to_nat l' cv') 
                                           by to_nat_tot]
                           trans [v_IH l' cv']
                           nv'_eq
                   trans join match (mk_to_bv_t rv) with
                              mk_to_bv_t v => 
                                (mk_to_bv_t (bvc (mod2 (S n)) v))
                              end
                           (mk_to_bv_t (bvc (mod2 (S n)) rv))
                   trans cong (mk_to_bv_t (bvc (mod2 *) rv))
                           symm iv_eq
                   trans cong (mk_to_bv_t (bvc * rv))
                            trans cong (mod2 *)
                                   join iv (condS a (mult2 (to_nat v')))
                              [mod2_mult2 ca 
                               terminates
                                 (to_nat l' cast v' by cong <vec * l'> P)
                               by to_nat_tot]

                         %- { (mk_to_bv_t (bvc a rv)) = (normalize v) } -%
                          case rv with
                            vecn A => 
                              case ca with 
                                ff => 
                                contra
                                  trans
                                    trans symm iv_eq
                                      hypjoin iv Z 
                                      by [to_nat_eq_Z2 l' cv' 
                                           trans nv'_eq
                                                 cong (mk_to_bv_t *) rv_eq]
                                       ca_eq end
                                    clash Z (S n)
                                  { (mk_to_bv_t (bvc a rv)) = (normalize v) }
                              | tt => 
                                hypjoin (mk_to_bv_t (bvc a rv))
                                        (normalize v)
                                by v_eq ca_eq nv'_eq rv_eq end
                              end
                          | vecc A a2 l2 v2 => 
                              hypjoin (mk_to_bv_t (bvc a rv)) (normalize v)
                              by v_eq rv_eq nv'_eq end
                          end
                 end % case nv'
       end % case iv
  end.

Define lt_to_nat : Forall(l:nat)(v:<bv l>).
                   { (lt (to_nat v) (pow2 l)) = tt } :=
  induction(l:nat)(v:<bv l>)
  return { (lt (to_nat v) (pow2 l)) = tt } with
    vecn A => hypjoin (lt (to_nat v) (pow2 l)) tt
              by v_eq inj <vec ** *> v_Eq end
  | vecc A l' a v' => 
    abbrev P = symm inj <vec * **> v_Eq in
    abbrev cv' = cast v' by cong <vec * l'> P in
    abbrev nv' = terminates (to_nat spec l' cv') by to_nat_tot in
    abbrev p2 = terminates (pow2 l') by pow_total in
    abbrev ca = cast a by P in
    abbrev PP = trans hypjoin (mult2 (pow2 l'))
                              (plus (pow2 l') (pow2 l'))
                      by [plusZ p2] end
                  [pow2_add l'] in
    case ca with
      ff => 
      trans cong (lt * (pow2 l))
              hypjoin (to_nat v) (mult2 nv')
              by v_eq ca_eq end
      trans cong (lt (mult2 nv') *) 
              trans cong (pow2 *) inj <vec ** *> v_Eq 
                    join (pow2 (S l')) (mult2 (pow2 l'))
         [mult_lt (S Z) nv' p2 [v_IH l' cv']]
    | tt => 
      trans cong (lt * (pow2 l))
              hypjoin (to_nat v) (S (mult2 nv'))
              by v_eq ca_eq end
      trans cong (lt (S (mult2 nv')) (pow2 *)) inj <vec ** *> v_Eq 
        symm
        trans symm [lt_S_mult2 nv' p2 [mult_lt (S Z) nv' p2 [v_IH l' cv']]]
              cong (lt (S (mult2 nv')) *) PP
    end

  end.

Define to_nat_inj : Forall(l:nat)(v1 v2:<bv l>)
                          (u:{ (to_nat v1) = (to_nat v2) }).
                      { v1 = v2 } :=
  induction(l:nat)(v1:<bv l>)
  return Forall(v2:<bv l>)
               (u:{ (to_nat v1) = (to_nat v2) }).
             { v1 = v2 } 
  with
    vecn A1 =>
     foralli(v2:<bv l>)
            (u:{ (to_nat v1) = (to_nat v2) }).
     case v2 with
       vecn A2 =>
         hypjoin v1 v2 by v1_eq v2_eq end
     | vecc A2 l2 b2 v2' =>
         contra
           trans trans symm inj <vec ** *> v1_Eq
                       inj <vec ** *> v2_Eq
                 clash (S l2)  Z
           { v1 = v2 }
     end
  | vecc A1 l1 cb1 cv1' =>
     foralli(v2:<bv l>)
            (u:{ (to_nat v1) = (to_nat v2) }).
     case v2 with
       vecn A2 =>
       contra
         trans trans symm inj <vec ** *> v1_Eq
                     inj <vec ** *> v2_Eq
               clash Z (S l1)
         { v1 = v2 }
     | vecc A2 l2 cb2 cv2' => 
       abbrev PA1 = symm inj <vec * **> v1_Eq in
       abbrev PA2 = symm inj <vec * **> v2_Eq in
       abbrev b1 = cast cb1 by PA1 in
       abbrev b2 = cast cb2 by PA2 in
       abbrev v1' = cast cv1' by cong <vec * l1> PA1 in
       abbrev v2' = cast cv2' 
                    by trans cong <vec * l2> PA2 
                             cong <vec bool *> 
                               inj (S *)
                                  trans symm inj <vec ** *> v2_Eq
                                        inj <vec ** *> v1_Eq  in
       abbrev t1 = terminates (to_nat l1 v1') by to_nat_tot in
       abbrev t2 = terminates (to_nat l1 v2') by to_nat_tot in

       abbrev eqcond1cond2 =
           hypjoin (condS b1 (mult2 (to_nat v1'))) 
                   (condS b2 (mult2 (to_nat v2')))
           by v1_eq v2_eq u end in

       abbrev eqb1b2 = 
         trans symm [mod2_mult2 b1 t1]
         trans cong (mod2 *) eqcond1cond2
               [mod2_mult2 b2 t2]  in

       abbrev eqt1t2 =
         trans symm [div2_mult2 b1 t1]
         trans cong (div2 *) eqcond1cond2
               [div2_mult2 b2 t2]  in

       trans v1_eq
       trans cong (vecc * v1')
               eqb1b2
       trans cong (vecc b2 *)
               [v1_IH l1 v1' v2' eqt1t2] 
             symm v2_eq
     end
  end.

% the carry bit is set iff incrementing overflows.

Inductive bv_inc_t : Fun(l:nat).type :=
  mk_bv_inc_t : Fun(spec l:nat)(v:<bv l>)(carry:bool).<bv_inc_t l>.

Define bv_inc : Fun(spec l:nat)(v:<bv l>).<bv_inc_t l> :=
  fun bv_inc(spec l:nat)(v:<bv l>):<bv_inc_t l>.
    match v with
      vecn A => cast (mk_bv_inc_t Z bvn tt)
                by cong <bv_inc_t *> symm inj <vec ** *> v_Eq 
    | vecc A l' x v' => 
      abbrev P = symm inj <vec * **> v_Eq in
      abbrev cx = cast x by P in
      abbrev cv' = cast v' by cong <vec * l'> P in
      match cx with
        ff => cast (mk_bv_inc_t (S l') (bvc l' tt cv') ff)
              by cong <bv_inc_t *> symm inj <vec ** *> v_Eq
      | tt => 
        let r = (bv_inc l' cv') in
        match r with
          mk_bv_inc_t l'' v'' carry =>
          cast (mk_bv_inc_t (S l'') (bvc l'' ff v'') carry)
          by trans cong <bv_inc_t (S *)> 
                     symm inj <bv_inc_t *> r_Eq
                   cong <bv_inc_t *>
                     symm inj <vec ** *> v_Eq
        end
      end
    end.

Define bv_inc_tot : Forall(l:nat)(v:<bv l>).Exists(r:<bv_inc_t l>). 
                          { (bv_inc v) = r } :=
   induction(l:nat)(v:<bv l>) return Exists(r:<bv_inc_t l>). 
                                           { (bv_inc v) = r } with
     vecn A => existsi cast (mk_bv_inc_t Z bvn tt) 
                       by cong <bv_inc_t *> symm inj <vec ** *> v_Eq
                 { (bv_inc v) = * }
                 hypjoin (bv_inc v) (mk_bv_inc_t bvn tt)
                 by v_eq end
   | vecc A l' a' v' => 
      abbrev P = symm inj <vec * **> v_Eq in
      abbrev ca' = cast a' by P in
      abbrev cv' = cast v' by cong <vec * l'> P in
      case ca' with
        ff => existsi cast (mk_bv_inc_t (S l') (bvc l' tt cv') ff)
                      by cong <bv_inc_t *> symm inj <vec ** *> v_Eq
                { (bv_inc v) = * }
                hypjoin (bv_inc v) (mk_bv_inc_t (bvc tt v') ff)
                by v_eq ca'_eq end
      | tt => 
        abbrev r = terminates (bv_inc spec l' cv') by [v_IH l' cv'] in
        case r with
          mk_bv_inc_t l'' v'' carry => 
          existsi cast (mk_bv_inc_t (S l'') (bvc l'' ff v'') carry)
                  by cong <bv_inc_t *> 
                       trans cong (S *) symm inj <bv_inc_t *> r_Eq
                             symm inj <vec ** *> v_Eq
            { (bv_inc v) = * }
            hypjoin (bv_inc v) (mk_bv_inc_t (bvc ff v'') carry)
            by v_eq ca'_eq r_eq end
        end
      end
   end.

Define to_nat_bv_inc : Forall(l:nat)(v:<bv l>)(v2:<bv l>)(carry:bool)
                             (u: { (bv_inc v) = (mk_bv_inc_t v2 carry) }).
                             { (S (to_nat v)) = (condplus carry (pow2 l)
                                                  (to_nat v2)) } :=
  induction(l:nat)(v:<bv l>) 
  return Forall(v2:<bv l>)(carry:bool)
               (u: { (bv_inc v) = (mk_bv_inc_t v2 carry) }).
               { (S (to_nat v)) = (condplus carry (pow2 l) (to_nat v2)) } with
    vecn A => 
      foralli(v2:<bv l>)(carry:bool)
             (u: { (bv_inc v) = (mk_bv_inc_t v2 carry) }).
         abbrev P = hypjoin (mk_bv_inc_t vecn tt) (mk_bv_inc_t v2 carry)
                    by v_eq u end in
           hypjoin (S (to_nat v)) (condplus carry (pow2 l) (to_nat v2))
           by v_eq
              inj (mk_bv_inc_t * **) P 
              inj (mk_bv_inc_t ** *) P
              inj <vec ** *> v_Eq
           end
  | vecc A l' a' v' => 
      foralli(v2:<bv l>)(carry:bool)
             (u: { (bv_inc v) = (mk_bv_inc_t v2 carry) }).
      abbrev P = symm inj <vec * **> v_Eq in
      abbrev ca' = cast a' by P in
      abbrev l_eq = inj <vec ** *> v_Eq in
      case ca' with
        ff => 
         abbrev P = hypjoin (mk_bv_inc_t (vecc tt v') ff) 
                            (mk_bv_inc_t v2 carry)
                    by v_eq u ca'_eq end in
         hypjoin (S (to_nat v)) (condplus carry (pow2 l) (to_nat v2))
         by v_eq 
            ca'_eq
            inj (mk_bv_inc_t * **) P 
            inj (mk_bv_inc_t ** *) P
            l_eq
         end
      | tt => 
        abbrev cv' = cast v' by cong <vec * l'> P in
        abbrev r = terminates (bv_inc spec l' cv') by bv_inc_tot in
        case r with
          mk_bv_inc_t l'' v2'' carry'' => 

           abbrev rIH = [v_IH l' cv' cast v2'' by cong <bv *> symm inj <bv_inc_t *> r_Eq
                           carry'' r_eq] in
           abbrev P = hypjoin (mk_bv_inc_t v2 carry) (mk_bv_inc_t (bvc ff v2'') carry'')
                      by u v_eq ca'_eq r_eq end in
           abbrev v2_eq = inj (mk_bv_inc_t * **) P in
                trans hypjoin (S (to_nat v)) (mult2 (S (to_nat v')))
                      by v_eq ca'_eq 
                         [mult2_S terminates (to_nat l' cv') by to_nat_tot] 
                      end
                trans cong (mult2 *) rIH
                trans [ mult2_condplus carry'' terminates (pow2 l') by pow_total 
                          terminates (to_nat l'' v2'') by to_nat_tot]
                      hypjoin (condplus carry'' 
                                 (mult2 (pow2 l')) (mult2 (to_nat v2'')))
                              (condplus carry
                                 (pow2 l) (to_nat v2))
                      by l_eq v2_eq inj (mk_bv_inc_t ** *) P end

        end
      end
  end.

Define bv_full : Fun(l:nat).<bv l> := (mkvec bool tt).

Define bv_inc_notfull
  : Forall(l:nat)(v1 v2:<bv l>)(carry:bool)
          (u1: { (lt (to_nat v1) (to_nat (bv_full l))) = tt})
          (u2: { (bv_inc v1) = (mk_bv_inc_t v2 carry) }).
     { carry = ff } :=
  foralli(l:nat)(v1 v2:<bv l>)(carry:bool)
         (u1: { (lt (to_nat v1) (to_nat (bv_full l))) = tt})
         (u2: { (bv_inc v1) = (mk_bv_inc_t v2 carry) }).
  case carry with
    ff => carry_eq
  | tt => 
    abbrev tfull = terminates (bv_full l) by mkvec_tot in
    abbrev tnfull = terminates (to_nat l tfull) by to_nat_tot in
    abbrev pl = terminates (pow2 l) by pow_total in
    abbrev tnv1 = terminates (to_nat l v1) by to_nat_tot in
    contra
      trans 
        trans symm [x_lt_x tnv1]
          [ltle_trans tnv1 tnfull tnv1
             u1
             [lt_pred tnv1 (S tnv1) tnfull join (S tnv1) (S tnv1) 
               [ltle_trans tnfull pl (S tnv1)
                 [lt_to_nat l tfull]
                 trans cong (le (pow2 l) *)
                          trans [to_nat_bv_inc l v1 v2 carry u2]
                             hypjoin (condplus carry (pow2 l) (to_nat v2))
                                     (plus (pow2 l) (to_nat v2))
                             by carry_eq end
                   [plus_implies_le pl
                    terminates (to_nat l v2) by to_nat_tot]]]]
        clash tt ff
      { carry = ff }
  end.

Define to_nat_append
  : Forall(l1 l2:nat)(v1:<bv l1>)(v2:<bv l2>).
          { (to_nat (vec_append v1 v2)) = (plus (to_nat v1)
                                             (mult (pow2 l1) (to_nat v2))) } :=
  foralli(l1 l2:nat)(v1:<bv l1>)(v2:<bv l2>).
    abbrev tn2 = terminates (to_nat l2 v2) by to_nat_tot in
    [induction(l1:nat)(v1:<bv l1>) 
       return { (to_nat (vec_append v1 v2)) = (plus (to_nat v1)
                                                (mult (pow2 l1) (to_nat v2))) } 
     with
       vecn A => hypjoin (to_nat (vec_append v1 v2))
                         (plus (to_nat v1) (mult (pow2 l1) (to_nat v2)))
                 by v1_eq inj <vec ** *> v1_Eq 
                    [plusZ tn2] end
     | vecc A l1' a v1' => 
       abbrev P = symm inj <vec * **> v1_Eq in
       abbrev cv1' = cast v1' by cong <vec * l1'> P in
       abbrev tn1' = terminates (to_nat l1' cv1') by to_nat_tot in
       abbrev q = terminates
                    (mult
                       terminates (pow2 l1') by pow_total
                       tn2)
                  by mult_total in
         trans 
           hypjoin (to_nat (vec_append v1 v2))
                   (condS a (mult2 (plus (to_nat v1')
                                         (mult (pow2 l1') (to_nat v2)))))
           by [v1_IH l1' cv1'] v1_eq end
         trans
           cong (condS a *)
              [mult2_plus tn1' q]
         trans
           [condS_plus cast a by P
             terminates (mult2 tn1') by mult_total
             terminates (mult2 q) by mult_total]
         trans
           cong (plus * (mult2 q)) 
             hypjoin (condS a (mult2 (to_nat v1'))) (to_nat v1)
             by v1_eq end
         cong (plus (to_nat v1) *)
           trans
             [mult2_mult_pow2 l1' tn2]
             hypjoin (mult (pow2 (S l1')) (to_nat v2))
                     (mult (pow2 l1) (to_nat v2))
             by inj <vec ** *> v1_Eq end
     end
     l1 v1].

Define to_nat_neq 
  : Forall(l:nat)(v1:<bv l>)(v2:<bv l>)
          (u:{ (eqnat (to_nat v1) (to_nat v2)) = ff }).
      { (eqbv v1 v2) = ff } :=
  foralli(l:nat)(v1:<bv l>)(v2:<bv l>)
         (u:{ (eqnat (to_nat v1) (to_nat v2)) = ff }).
  case (eqbv l v1 v2) by x y with
    ff => x
  | tt => 
    contra
      trans
        trans symm u
        trans cong (eqnat (to_nat *) (to_nat v2)) 
                    [eqbv_eq l v1 v2 x]
              [x_eqnat_x (to_nat l v2)]
        clash tt ff
      { (eqbv v1 v2) = ff }
  end.

Define to_nat_eq
  : Forall(l:nat)(v1:<bv l>)(v2:<bv l>)
          (u:{(eqbv v1 v2) = tt}).
     {(eqnat (to_nat v1) (to_nat v2)) = tt} :=
  foralli(l:nat)(v1:<bv l>)(v2:<bv l>)
         (u:{(eqbv v1 v2) = tt}).
  trans cong (eqnat (to_nat v1) (to_nat *)) 
          symm [eqbv_eq l v1 v2 u]
        [eqnat_refl (to_nat l v1)].
   
Define trusted to_nat_neq1 : Forall(l:nat)(v1:<bv l>)(v2:<bv l>)
                                   (u:{(eqbv v1 v2) = ff}).
                               {(eqnat (to_nat v1) (to_nat v2)) = ff} := truei.

Define bv_shift: Fun(x:nat)(spec n:nat)(l:<bv (S n)>). <bv (S n)> :=
  fun bv_shift(x:nat)(spec n:nat)(l:<bv (S n)>): <bv (S n)>.
  match x with
    Z => l
  | S x' => (bv_shift x' n cast (bv_append n (S Z) (bv_tail n l) (bvc Z ff bvn)) by
                                cong <bv *> trans [plusS n Z] %is there an easier way?
                                                  cong (S *) [plusZ n])
  end.

Define bv_or : Fun(spec n:nat)(l1:<bv n>)(l2:<bv n>).<bv n> :=
  fun bv_or(spec n:nat)(l1:<bv n>)(l2:<bv n>) : <bv n>.
  match l1 with
    vecn _ => cast (vecn bool) by symm l1_Eq
  | vecc _ n' b1 l1' =>
      match l2 with
        vecn _ => abort <bv n>
      | vecc _ n'' b2 l2' =>
          % have: <bv n> = <bv (S n')>
          % have: <bv n> = <bv (S n'')>
          abbrev p1 = inj <bv *> l1_Eq in % n = (S n')
          abbrev p2 = inj <bv *> l2_Eq in % n = (S n'')
          abbrev p3 = inj (S *) trans symm p2 p1 in
          let l2'' = cast l2' by cong <bv *> p3 in
          cast (vecc bool n' (or b1 b2) (bv_or n' l1' l2'')) by
            cong <bv *> symm p1
      end
  end.

