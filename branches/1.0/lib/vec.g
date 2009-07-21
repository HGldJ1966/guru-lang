Include "plus.g".
Include "list.g".
Include "mult.g".
Include "bool.g".

%Set "print_parsed".

Inductive vec : Fun(A:type)(n:nat).type :=
  vecn : Fun(A:type).<vec A Z>
| vecc : Fun(A:type)(spec n:nat)(a:A)(l:<vec A n>).
              <vec A (S n)>.

Define vec_fold : Fun( A B C : type )( spec n : nat )(^#owned cookie:C)
               ( f : Fun(^#owned cookie:C)( ^#owned a : A )( y : B). B )
               (b:B)( ^#owned v : <vec A n>). B :=
   fun vec_fold( A B C : type )( spec n : nat )(^#owned cookie:C)
               ( f : Fun(^#owned cookie:C)( ^#owned a : A )( y : B). B )
               (b:B)( ^#owned v : <vec A n>): B.
   match v with
      vecn A' => b
      | vecc A' n' a' l' => (f cookie a' (vec_fold A B C n' cookie f b l'))
   end.

Define vec_foldr := vec_fold.
Define vec_foldl : Fun( A B C : type )( spec n : nat )(^#owned cookie:C)
                      ( f : Fun(^#owned cookie:C)( a : A )( y : B). B )
                      (b:B)( v : <vec A n>). B :=
  fun vec_foldl( A B C : type )( spec n : nat )(^#owned cookie:C)
               ( f : Fun(^#owned cookie:C)( a : A )( y : B). B )
               (b:B)( v : <vec A n>): B.
  match v with
    vecn _ => b
  | vecc _ n' a' v' => (vec_foldl A B C n' cookie f (f cookie a' b) v')
  end.

Define vec_append :=
fun vec_append(A:type)(spec n m:nat)(l1 : <vec A n>)(l2 : <vec A m>):
              <vec A (plus n m)>.
    match l1 with
      vecn _ => cast l2 by
                cong <vec A *>
                 symm trans
                        cong (plus * m)
                            inj <vec ** *> l1_Eq
                        join (plus Z m) m
    | vecc _ n' x l1' => 
       cast
          (vecc A (plus n' m) x (vec_append A n' m l1' l2)) 
       by cong <vec A *>
             trans
               symm join (plus (S n') m)
                         (S (plus n' m))
               cong (plus * m)
                 symm inj <vec ** *> l1_Eq
    end.

Define vec_cat :=
  fun vec_cat(A:type)(spec n m:nat)(l : <vec <vec A m> n>):
      <vec A (mult n m)>.
    match l with
      vecn A' => cast (vecn A) 
                 by cong <vec A *> 
                     hypjoin Z (mult n m) by inj <vec ** *> l_Eq end
    | vecc A' n' a' l' => 
        abbrev P = symm inj <vec * **> l_Eq in
        cast (vec_append A m 
                terminates (mult n' m) by mult_total
                a' (vec_cat A n' m l'))
        by cong <vec A *> hypjoin (plus m (mult n' m)) (mult n m)
                          by symm inj <vec ** *> l_Eq end
    end.

Inductive vec_cat2_t : Fun(A:type).type :=
  mk_vec_cat2_t : Fun(A:type)(spec l:nat)(v:<vec A l>).<vec_cat2_t A>.

Define vec_cat2 :=
  fun vec_cat2(A:type)(spec m:nat)(l : <list <vec A m>>):<vec_cat2_t A>.
    match l with
      nil A' => (mk_vec_cat2_t A Z (vecn A)) 
    | cons A' a' l' => 
        abbrev P = symm inj <list *> l_Eq in
        let r = (vec_cat2 A m l') in
        match r with
          mk_vec_cat2_t A'' l' v' =>
            (mk_vec_cat2_t A
              terminates (plus m l') by plus_total
              (vec_append A m l' a' v'))
        end
    end.

Define mkvec :=
  fun mkvec(A:type)(a:A)(n:nat):<vec A n>. 
    match n by un vn with
      Z => cast (vecn A) by cong <vec A *> symm un
    | S n' => cast (vecc A n' a (mkvec A a n')) by cong <vec A *> symm un
    end.

Define mkvec_tot : Forall(A:type)(a:A)(n:nat). 
                    Exists(r:<vec A n>). {(mkvec a n) = r} :=
  foralli(A:type)(a:A).
    induction(n:nat) return Exists(r:<vec A n>). {(mkvec a n) = r} with
      Z => existsi cast (vecn A) by cong <vec A *> symm n_eq
             { (mkvec a n) = * }
             hypjoin (mkvec a n) vecn
             by n_eq end
    | S n' => 
      existse [n_IH n']
      foralli(r:<vec A n'>)(ur:{(mkvec a n') = r}).
        existsi cast (vecc A n' a r) by cong <vec A *> symm n_eq
          {(mkvec a n) = * }
          hypjoin (mkvec a n) (vecc a r)
          by ur n_eq end
    end.         

Total mkvec mkvec_tot.

Define mkvec_sz : Forall(A:type)(a:A)(n:nat).
                   { (lt size a size (mkvec a (S n))) = tt } :=
  foralli(A:type)(a:A)(n:nat).
    trans cong (lt size a *) 
            trans cong size *
                   evalto (mkvec a (S n)) (vecc a (mkvec a n))
                  join size (vecc a (mkvec a n)) 
                       (S (plus size a size (mkvec a n)))
          [lt_Splus size a size terminates (mkvec A a n) by mkvec_tot].
         

Define vec_get :=
  fun vec_get(A:type)(spec n:nat)(l:<vec A n>)(m:nat)(u:{ (lt m n) = tt }):A.
    match l by ul vl with
      vecn A' => abort A
    | vecc A' n' a' l' =>
         match m with
           Z => a'
         | S m' => (vec_get A n' l' m'
                      symm
                      trans symm u
                      trans cong (lt * n) m_eq
                      trans cong (lt (S m') *) inj <vec ** *> vl
                            [S_lt_S m' n'])
         end
    end.

Define vec_get_sztot 
  : Forall(A:type)(n:nat)(l:<vec A n>)(m:nat)(u:{ (lt m n) = tt }).
      Exists(r:A)(s:{ (lt size r size l) = tt}) . { (vec_get l m) = r } :=
  foralli(A:type).
    induction(n:nat)(l:<vec A n>)
    return Forall(m:nat)(u:{ (lt m n) = tt }).
             Exists(r:A)(s:{ (lt size r size l) = tt}).
              { (vec_get l m) = r } with
      vecn A' => 
        foralli(m:nat)(u:{ (lt m n) = tt }).
          contra
            trans trans hypjoin ff (lt m n) by [lt_Z m]
                                               symm inj <vec ** *> l_Eq end
                        u
                  clash tt ff
            Exists(r:A)(s:{ (lt size r size l) = tt}). { (vec_get l m) = r } 
    | vecc A' n' a' l' => 
        abbrev a = cast a' by symm inj <vec * **> l_Eq in
        foralli(m:nat)(u:{ (lt m n) = tt }).
        case m with
          Z => existsi a 
                 Exists(s:{ (lt size * size l) = tt}).{ (vec_get l m) = * }
               andi trans cong (lt size a size *) 
                              l_eq
                      trans cong (lt size a *) 
                              join size (vecc a' l') (S (plus size a' size l'))
                        [lt_Splus size a' size l']
                 hypjoin (vec_get l m) a by l_eq m_eq end
        | S m' => 
          existse [l_IH n' cast l' by cong <vec * n'> symm inj <vec * **> l_Eq
                    m' trans symm [S_lt_S m' n'] 
                             hypjoin (lt (S m') (S n')) tt 
                             by u inj <vec ** *> l_Eq m_eq end]
           foralli(r:A)(s:{ (lt size r size l') = tt})
                  (ur:{(vec_get l' m') = r}).
             existsi r 
                Exists(s:{ (lt size * size l) = tt}).{ (vec_get l m) = * }
             andi [lt_trans size r size l' size l s 
                     trans cong (lt size l' *)
                             hypjoin size l (S (plus size a' size l'))
                             by l_eq end
                     trans cong (lt size l' (S *))
                             [plus_comm size a' size l']
                           [lt_Splus size l' size a']]
              trans hypjoin (vec_get l m) (vec_get l' m') by l_eq m_eq end
                    ur
        end
    end.

Define vec_get_tot 
  : Forall(A:type)(n:nat)(l:<vec A n>)(m:nat)(u:{ (lt m n) = tt }).
      Exists(r:A). { (vec_get l m) = r } :=
  foralli(A:type)(n:nat)(l:<vec A n>)(m:nat)(u:{ (lt m n) = tt }).
    existse [vec_get_sztot A n l m u]
    foralli(r:A)(s:{(lt size r size l) = tt})
           (u:{(vec_get l m) = r}).
      existsi r
        {(vec_get l m) = *}
        u.

Define vec_update :=
    fun vec_update(A:type)(spec n:nat)(l:<vec A n>)(m:nat)(a:A)
               (u:{ (lt m n) = tt }):<vec A n>.
      match l with 
        vecn A' => abort <vec A n>
      | vecc A' n' a' l' =>
        abbrev P1 = symm inj <vec * **> l_Eq in
        abbrev cl' = cast l' by cong <vec * n'> P1 in
        cast
           match m with
             Z => (vecc A n' a cl')
           | S m' => (vecc A n' cast a' by P1 
                        (vec_update A n' cl' m' a
                           symm
                           trans symm u
                           trans cong (lt * n) m_eq 
                           trans cong (lt (S m') *) inj <vec ** *> l_Eq
                                 [S_lt_S m' n']))
           end
        by
         cong <vec A *> symm inj <vec ** *> l_Eq
      end.

Define vec_head : Fun(A:type)(spec n:nat)(l:<vec A (S n)>). A :=
  fun(A:type)(spec n:nat)(l:<vec A (S n)>).
    match l by x1 x2 return A with
      vecn A' => abort A
    | vecc A' n' x' l' => cast x' by symm inj <vec * **> x2
    end.

Define vec_head_total : Forall(A:type)(n:nat)(l:<vec A (S n)>).
                    Exists(x:A). { (vec_head l) = x } :=
  foralli(A:type)(n:nat).
    induction(l:<vec A (S n)>) by x1 x2 IH 
    return Exists(x:A). { (vec_head l) = x } with
      vecn A' => contra trans inj <vec ** *> x2 
                             clash Z (S n)
                 Exists(x:A). { (vec_head l) = x }
    | vecc A' n' x' l' => existsi cast x' by symm inj <vec * **> x2
                          { (vec_head l) = * }
                          trans cong (vec_head *) x1
                                join (vec_head (vecc x' l'))
                                     x'
    end.

Define vec_tail : Fun(A:type)(spec n:nat)(l:<vec A (S n)>). <vec A n> :=
  fun(A:type)(spec n:nat)(l:<vec A (S n)>).
    match l with
	  vecn _ => abort <vec A n>
	| vecc _ _ _ l' => cast l' by refl <vec A n> 
	end.

Define vec_append_assoc : Forall(A:type)(n1 : nat)(l1 : <vec A n1>)
                      (n2 n3 : nat)(l2 : <vec A n2>)(l3 : <vec A n3>).
                      { (vec_append (vec_append l1 l2) l3) =
                        (vec_append l1 (vec_append l2 l3)) } :=
  foralli(A:type).
  induction(n1:nat)(l1:<vec A n1>) by x1 x2 IH return Forall(n2 n3 : nat)
                      (l2 : <vec A n2>)(l3 : <vec A n3>).
                      { (vec_append (vec_append l1 l2) l3) =
                        (vec_append l1 (vec_append l2 l3)) } with
    vecn A' => foralli(n2 n3 : nat)
               (l2 : <vec A n2>)(l3 : <vec A n3>). 
           % transform the LHS to (vec_append ! n2 n3 l2 l3)
           trans cong (vec_append (vec_append * l2) l3) 
                   x1
           trans join (vec_append (vec_append vecn l2) l3)
                   (vec_append vecn (vec_append l2 l3))
           symm cong (vec_append * (vec_append l2 l3)) x1
   | vecc A' n1' x' l1' => 
      foralli(n2 n3 : nat)(l2 : <vec A n2>)(l3 : <vec A n3>). 
            trans cong (vec_append (vec_append * l2) l3) x1
            trans cong (vec_append * l3)
                    join (vec_append (vecc x' l1') l2)
                         (vecc x' (vec_append l1' l2))
            trans join (vec_append (vecc x' (vec_append l1' l2)) l3)
                       (vecc x' (vec_append (vec_append l1' l2) l3))
            trans cong (vecc x' *)
                          [IH n1' cast l1' by cong <vec * n1'> 
                                                inj <vec * **> symm x2
                              n2 n3 l2 l3]
            trans join (vecc x' (vec_append l1' (vec_append l2 l3)))
                   (vec_append (vecc x' l1') (vec_append l2 l3))
            symm cong (vec_append * (vec_append l2 l3)) x1
  end.

Define vec_reverse_h
  : Fun(A:type)(spec n m:nat)(l1:<vec A n>)(l2:<vec A m>).<vec A (plus n m)> :=
  fun vec_reverse_h(A:type)(spec n m:nat)(l1:<vec A n>)(l2:<vec A m>)
      :<vec A (plus n m)> .
    match l1 by ul1 vl1 with
      vecn A' => cast l2 by cong <vec A *> hypjoin m (plus n m) 
                                           by inj <vec ** *> vl1 end
    | vecc A' n' a' l1' =>
      abbrev P = symm inj <vec * **> vl1 in
      cast
        (vec_reverse_h A n' (S m) 
           cast l1' by cong <vec * n'> P
           (vecc A m cast a' by P l2))
      by cong <vec A *>
           trans symm [plusS_hop n' m]
                 cong (plus * m) symm inj <vec ** *> vl1
    end.

Define vec_reverse := 
  fun(A:type)(spec n:nat)(l1:<vec A n>). 
    cast (vec_reverse_h A n Z l1 (vecn A)) by cong <vec A *> 
                                                [plusZ n].

Define vec_map : Fun(A B:type)(spec n:nat)
                    (f:Fun(x:A).B)(l:<vec A n>). <vec B n> :=
  fun vec_map(A B:type)(spec n:nat)(f:Fun(x:A).B)(l:<vec A n>): <vec B n>.
    match l by x1 x2 return <vec B n> with
      vecn A' => cast (vecn B) by cong <vec B *> symm inj <vec ** *> x2
    | vecc A' n' x' l' =>
        cast (vecc B n' (f cast x' by symm inj <vec * **> x2) 
                (vec_map A B n' f cast l' by cong <vec * n'> 
                                              symm inj <vec * **> x2))
        by cong <vec B *> symm inj <vec ** *> x2
    end.

Define eqvec : Fun(A:type)(eqA:Fun(x y:A).bool)(spec n:nat)
                  (x y:<vec A n>).bool :=
  fun eqvec(A:type)(eqA:Fun(x y:A).bool)(spec n:nat)(x y:<vec A n>):bool.
    match x by ux vx with
      vecn A' => 
         match y by uy vy with
           vecn B' => tt
         | vecc B' m' b' y' => ff
         end
    | vecc A' n' a' x' => 
        match y by uy vy with
          vecn B' => ff
        | vecc B' m' b' y' => 
           abbrev PA' = symm inj <vec * **> vx in
           abbrev PB' = symm inj <vec * **> vy in
           (and (eqA cast a' by PA' cast b' by PB')
                (eqvec A eqA n' 
                    cast x' by cong <vec * n'> PA'
                    cast y' by trans cong <vec * m'> PB'
                                     cong <vec A *> 
                                       inj (S *)
                                         trans symm inj <vec ** *> vy
                                               inj <vec ** *> vx))
        end
   end.


%Set "show_spec_args".
%Set "print_parsed".

Define eqvec_tot 
  : Forall(A:type)
          (eqA:Fun(x y:A).bool)
          (eqA_tot : Forall(x y:A).Exists(b:bool). {(eqA x y) = b})
          (n:nat)
          (x y:<vec A n>).
          Exists(b:bool). { (eqvec eqA x y) = b } :=
  foralli(A:type)(eqA:Fun(x y:A).bool)
         (eqA_tot : Forall(x y:A).Exists(b:bool). {(eqA x y) = b}).
  induction(n:nat)(x:<vec A n>) by ux vx IH 
  return Forall(y:<vec A n>).
         Exists(b:bool). { (eqvec eqA x y) = b } with
    vecn A' => 
      induction(y:<vec A n>) by uy vy ign 
      return Exists(b:bool). { (eqvec eqA x y) = b } with
        vecn A'' => 
          existsi tt { (eqvec eqA x y) = * }
            hypjoin (eqvec eqA x y) tt by ux uy end
      | vecc A'' n'' a'' y'' =>
          contra
            trans
              trans symm inj <vec ** *> vx
                    inj <vec ** *> vy
              clash (S n'') Z
          Exists(b:bool). { (eqvec eqA x y) = b } 
      end
  | vecc A' n' a' x' => 
      induction(y:<vec A n>) by uy vy ign 
      return Exists(b:bool). { (eqvec eqA x y) = b } with
        vecn A'' => 
          contra
            trans
              trans symm inj <vec ** *> vx
                    inj <vec ** *> vy
              clash Z (S n') 
          Exists(b:bool). { (eqvec eqA x y) = b }
      | vecc A''  n'' a'' y'' => 
        existse [eqA_tot cast a' by symm inj <vec * **> vx
                         cast a'' by symm inj <vec * **> vy]
        foralli(r:bool)(ur:{(eqA a' a'') = r}).
          abbrev nP = inj (S *) 
                       trans symm inj <vec ** *> vy
                             inj <vec ** *> vx in
          existse [IH n' cast x' by cong <vec * n'> symm inj <vec * **> vx
                         cast y'' by trans cong <vec A'' *> nP
                                           cong <vec * n'> 
                                             symm inj <vec * **> vy]
          foralli(r2:bool)(ur2:{(eqvec eqA x' y'') = r2}).
          existse [and_tot r r2] foralli(r3:bool)(ur3:{(and r r2) = r3}).
            existsi r3 {(eqvec eqA x y) = *}
              trans hypjoin (eqvec eqA x y) 
                            (and (eqA a' a'') (eqvec eqA x' y''))
                    by ux uy end
              trans cong (and (eqA a' a'') *) ur2
              trans cong (and * r2) ur
                    ur3
      end
  end.

Define eqvec_refl 
  : Forall(A:type)
          (eqA:Fun(x y:A).bool)
          (eqA_refl : Forall(x:A). {(eqA x x) = tt})
          (n:nat)
          (x:<vec A n>).
      { (eqvec eqA x x) = tt } :=
  foralli(A:type)
         (eqA:Fun(x y:A).bool)
         (eqA_refl : Forall(x:A). {(eqA x x) = tt}).
  induction(n:nat)(x:<vec A n>) return {(eqvec eqA x x) = tt} with
    vecn ign => hypjoin (eqvec eqA x x) tt by x_eq end
  | vecc ign1 n' a x' => hypjoin (eqvec eqA x x) tt 
                         by x_eq [x_IH n' x'] [eqA_refl a] end
  end.

Define eqvec_eq 
  : Forall(A:type)
          (eqA:Fun(x y:A).bool)
          (eqA_eq : Forall(x y:A)(u:{(eqA x y) = tt}).{x = y})
          (n:nat)
          (x y:<vec A n>)
          (u: { (eqvec eqA x y) = tt }).
          { x = y } :=
  foralli(A:type)(eqA:Fun(x y:A).bool)
         (eqA_eq : Forall(x y:A)(u:{(eqA x y) = tt}).{x = y}).
  induction(n:nat)(x:<vec A n>) by ux vx IH 
  return Forall(y:<vec A n>)
               (u: { (eqvec eqA x y) = tt }).
               { x = y } with
    vecn A' => 
      induction(y:<vec A n>) by uy vy ign 
      return Forall(u: { (eqvec eqA x y) = tt }).
               { x = y } with
        vecn A'' => 
          foralli(u: { (eqvec eqA x y) = tt }).
            hypjoin x y by ux uy end
      | vecc A'' n'' a'' y'' =>
          foralli(u: { (eqvec eqA x y) = tt }).
          contra
            trans
              trans symm inj <vec ** *> vx
                    inj <vec ** *> vy
              clash (S n'') Z
            { x = y }
      end
  | vecc A' n' a' x' => 
      induction(y:<vec A n>) by uy vy ign 
      return Forall(u: { (eqvec eqA x y) = tt }).
                   { x = y } with
        vecn A'' => 
          foralli(u: { (eqvec eqA x y) = tt }).
          contra
            trans
              trans symm inj <vec ** *> vx
                    inj <vec ** *> vy
              clash Z (S n') 
          {x = y}
      | vecc A'' n'' a'' y'' => 
         foralli(u: { (eqvec eqA x y) = tt }).
         abbrev andP = symm trans symm u
                                  hypjoin (eqvec eqA x y) 
                                          (and (eqA a' a'') 
                                               (eqvec eqA x' y''))
                                  by ux uy end in
         abbrev nP = inj (S *) 
                       trans symm inj <vec ** *> vy
                             inj <vec ** *> vx in
         abbrev a1 = cast a' by symm inj <vec * **> vx in
         abbrev a2 = cast a'' by symm inj <vec * **> vy in
         abbrev x1 = cast x' by cong <vec * n'> symm inj <vec * **> vx in
         abbrev y1 = cast y'' by trans cong <vec A'' *> nP
                                       cong <vec * n'> 
                                          symm inj <vec * **> vy in
         existse cinv (eqA a1 a2) andP
         foralli(r1:bool)(ur1:{(eqA a' a'') = r1}).
         existse cinv (eqvec A eqA n' x1 y1) 
                   trans cong (and (eqA a' a'') *) 
                           symm eval (eqvec eqA x1 y1) 
                         andP
         foralli(r2:bool)(ur2:{ (eqvec eqA x' y'') = r2}).
           abbrev to_names = trans cong (and (eqA a' a'') *) ur2
                                   cong (and * r2) ur1 in
           abbrev names_tt = trans symm to_names andP in
           abbrev eqa_tt = trans ur1 [and_eq_tt1 r1 r2 names_tt] in
           abbrev as_eq = [eqA_eq a1 a2 eqa_tt] in 
           abbrev eqvec_tt = trans ur2 [and_eq_tt2 r1 r2 names_tt] in
           abbrev xy_eq = [IH n' x1 y1 eqvec_tt] in
            trans ux 
            trans cong (vecc * x') as_eq
            trans cong (vecc a'' *) xy_eq
                  symm uy
      end
  end.

Define vec_exists : Fun(A C:type)( spec n : nat )(^#owned c:C)
                      (f:Fun(^#owned c:C)(^#owned a:A).bool)(^#owned l:<vec A n>).bool :=
fun(A C:type)( spec n : nat )(^#owned c:C)(f:Fun(^#owned c:C)(^#owned a:A).bool).
  (vec_foldr A bool C n c fun(^#owned c:C)(^#owned a:A)(b:bool).(or (f c a) b) ff).
    
Define vec_forall : Fun(A C:type)( spec n : nat )(^#owned c:C)
                      (f:Fun(^#owned c:C)(^#owned a:A).bool)(^#owned l:<vec A n>).bool :=
fun(A C:type)( spec n : nat )(^#owned c:C)(f:Fun(^#owned c:C)(^#owned a:A).bool).
  (vec_foldr A bool C n c fun(^#owned c:C)(^#owned a:A)(b:bool).(and (f c a) b) tt).
    
Define list_to_vec : Fun( A : type )( L : < list A > ). <vec A (length A L)> :=
fun list_to_vec( A : type )( L : < list A > ) : <vec A (length A L)>.
  match L with
    nil _ => cast (vecn A) by
                cong <vec A *>
                  symm trans cong (length A *) L_eq
                  join (length A nil) Z

  | cons _ a L' => cast (vecc A (length A L') a (list_to_vec A L')) by
                cong <vec A *>
                    symm trans cong (length *) L_eq
                              join (length (cons a L')) (S (length L'))
  end.
  
Define vec_to_list : Fun( A : type )(spec n:nat)(V : <vec A n>). <list A > :=
fun vec_to_list( A : type )(spec n:nat)(V : <vec A n>): < list A >.
  match V with
    vecn _ => (nil A)
  | vecc _ n' a V' => (cons A a (vec_to_list A n' V'))
  end.


Define list_vec_list:
   Forall (A:type)(L:<list A>).{(vec_to_list (list_to_vec L)) = L} :=
   foralli (A:type).
   induction (L:<list A>)
   return {(vec_to_list (list_to_vec L)) = L} with

        nil _ => trans cong (vec_to_list (list_to_vec *)) L_eq
                 trans join (vec_to_list (list_to_vec nil)) nil
                       symm L_eq


      | cons _ a L' =>  trans cong (vec_to_list (list_to_vec *)) L_eq
                        trans join (vec_to_list (list_to_vec (cons a L')))
                                   (cons a (vec_to_list (list_to_vec L')))
                        trans cong (cons a *) [L_IH L']
                              symm  L_eq
end.
  

Define vec_list_vec:
   Forall (A:type)(n:nat)(V:<vec A n>).{(list_to_vec (vec_to_list V)) = V} :=
   foralli (A:type).
   induction (n:nat)(V:<vec A n>)
   return {(list_to_vec (vec_to_list V)) = V} with

       vecn _ => trans cong (list_to_vec (vec_to_list *)) V_eq
                 trans join (list_to_vec (vec_to_list vecn)) vecn
                       symm V_eq

      | vecc _ n' a V' => trans cong (list_to_vec (vec_to_list *)) V_eq
                          trans join (list_to_vec (vec_to_list (vecc a V')))
                                     (vecc a (list_to_vec (vec_to_list V')))
                          trans cong (vecc a *) [V_IH n' V']
                                symm V_eq
end.
