Include "plus.g".
Include "list.g".
Include "mult.g".
Include "bool.g".

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

Define vec_append_total : Forall(A:type)(n m:nat)(l1 : <vec A n>)(l2 : <vec A m>).
	Exists(l : <vec A (plus n m)>).{ (vec_append l1 l2) = l } :=
  foralli(A:type).
  induction(n m:nat)(l1:<vec A n>) return Forall
  	(l2:<vec A m>)
  	.Exists(l : <vec A (plus n m)>).{ (vec_append l1 l2) = l }
  with
  	vecn _ => foralli
			(l2:<vec A m>).
			abbrev n_eq = inj <vec ** *> l1_Eq in
			abbrev p1 = hypjoin m (plus n m) by n_eq end in
			abbrev l2' = cast l2 by cong <vec A *> p1 in
  		existsi l2' { (vec_append l1 l2) = * }
  		hypjoin (vec_append l1 l2) l2 by l1_eq end
  | vecc _ n' a l1' => foralli
			(l2:<vec A m>).
			abbrev n_eq = inj <vec ** *> l1_Eq in
  		existse [l1_IH n' m l1' l2]
  		foralli(l':<vec A (plus n' m)>)(l'_pf:{ (vec_append l1' l2) = l' }).
			abbrev p1 = hypjoin (S (plus n' m)) (plus n m) by n_eq end in
			abbrev l = cast (vecc A (plus n' m) a l') by cong <vec A *> p1 in
  		existsi l { (vec_append l1 l2) = * }
  		hypjoin (vec_append l1 l2) l by l1_eq l'_pf end
  end.

Total vec_append vec_append_total.

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

Total vec_get vec_get_tot.

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

Define vec_update_tot :
  Forall(A:type)(n:nat)(l:<vec A n>)
        (i:nat)(a:A)
        (u:{ (lt i n) = tt }).
  Exists(l':<vec A n>)
    .{ (vec_update l i a) = l' }
  :=
  foralli(A:type).
  induction(n:nat)(l:<vec A n>) return 
    Forall(i:nat)(a:A)
					(u:{ (lt i n) = tt }).
		Exists(l':<vec A n>)
			.{ (vec_update l i a) = l' }
  with
    vecn _ =>
      foralli(i:nat)(a:A)
						 (u:{ (lt i n) = tt })
			.
      abbrev n_Z = inj <vec ** *> l_Eq in
      abbrev p = hypjoin (lt i n) ff by n_Z [lt_Z i] end in
      contra trans symm u
             trans p
                   clash ff tt
						Exists(l':<vec A n>)
							.{ (vec_update l i a) = l' }

  | vecc _ n' a' l' =>
      foralli(i:nat)(a:A)
 						 (u:{ (lt i n) = tt })
			.
			abbrev n_eq = inj <vec ** *> l_Eq in
			case i with
				Z =>
					abbrev r' = cast (vecc A n' a l') by cong <vec A *> symm n_eq in
					existsi r' { (vec_update l i a) = * }
					hypjoin (vec_update l i a) r' by l_eq i_eq end
			| S i' =>
					abbrev u' = hypjoin (lt i' n') tt by [S_lt_S i' n'] n_eq i_eq u end in
					existse [l_IH n' l' i' a u']
					foralli(r:<vec A n'>)(r_pf:{ (vec_update l' i' a) = r }).
					abbrev r' = cast (vecc A n' a' r) by cong <vec A *> symm n_eq in
					existsi r' { (vec_update l i a) = * }
					hypjoin (vec_update l i a)  r' by l_eq i_eq r_pf end
			end
  end
  .

Total vec_update vec_update_tot.

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
  : Fun(A:type)(spec n m:nat)(l1:<vec A n>)(l2:<vec A m>).
       <vec A (plus n m)> :=
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

Define vec_reverse 
  : Fun(A:type)(spec n:nat)(l:<vec A n>).<vec A n> := 
  fun(A:type)(spec n:nat)(l1:<vec A n>). 
    cast (vec_reverse_h A n Z l1 (vecn A)) by cong <vec A *> 
                                                [plusZ n].

%-
Returns the last element of a vector. This function is defined recursively,
rather than in terms of other functions such as reverse, so that it is 
easy to reason about.
-%
Define vec_last :
  Fun(A: type)(spec n: nat)(u: { n != Z } )(l: <vec A n>).A
  :=
  fun vec_last(A: type)(spec n: nat)(u: { n != Z } )(l: <vec A n>) : A .
  match l with
    | vecn _ =>
      impossible
        transs
          inj <vec ** *> l_Eq
          symm u
        end
              
        A
    | vecc _ n' a l' => 
      match l' with
        | vecn _ => 
          a
        | vecc _ n'' _ l'' =>
          abbrev n'_neq_Z = 
            transs
              inj <vec ** *> l'_Eq
              clash (S n'') Z
            end
          in

          (vec_last A n' n'_neq_Z l')
      end
  end.

Define vec_first_n :
  Fun(A: type)
     (spec inputVecLength: nat)
     (v: <vec A inputVecLength>)
     (n: nat)
     (u: { (le n inputVecLength) = tt } ). <vec A n>
  :=
  fun vec_first_n(A: type)    
                 (spec inputVecLength: nat)
                 (v: <vec A inputVecLength>)
                 (n: nat)
                 (u: { (le n inputVecLength) = tt } ) 
                 : <vec A n>.
  match n with
    | Z =>
      cast (vecn A) by cong <vec A *> symm n_eq
    | S n' =>
      match v with
        | vecn _ =>
          impossible
            abbrev inputVecLength_eq_Z = inj <vec A *> v_Eq in
            abbrev n_le_Z = 
              trans cong (le n *) symm inputVecLength_eq_Z
                    u
            in
            abbrev n_eq_Z = [le_Z1 n n_le_Z] in
            transs 
              symm n_eq
              n_eq_Z
              clash Z (S n')
            end

            <vec A n>
        | vecc A restLength a rest =>
          abbrev inputVecLength_eq_SrestLength =
            inj <vec A *> v_Eq
          in
          abbrev n'_lt_n =
            [ltle_trans 
              n'
              (S n')
              n
              [lt_S n']
              [eq_le (S n') n symm n_eq]
            ]
          in
          abbrev n'_lt_inputVecLength =
            [ltle_trans n' n inputVecLength n'_lt_n u]
          in
          abbrev n'_le_restLength =
            hypjoin (le n' restLength) tt by
              inputVecLength_eq_SrestLength
              n'_lt_inputVecLength
              [le_eq_lt_S n' restLength]
            end
          in
          abbrev ret = 
            (vecc
              A
              n'
              a 
              (vec_first_n A restLength rest n' n'_le_restLength)   
            )
          in
          cast ret by cong <vec A *> symm n_eq
      end
  end.         

%-
Returns a list containing all elements of a vector except the last. 
This function is defined recursively, rather than in terms of other functions 
such as reverse, so that it is easy to reason about.
-%
Define vec_all_but_last :
  Fun(A: type)(spec n: nat)(spec m: nat)(u: { n = (S m) } )(l: <vec A n>). <vec A m>
  :=
  fun vec_all_but_last(A: type)
                      (spec n: nat)
                      (spec m: nat)
                      (u: { n = (S m) } )
                      (l: <vec A n>) 
                      : <vec A m> .
  match l with
    | vecn _ =>
      impossible
        transs
          symm u
          inj <vec ** *> l_Eq
          clash Z (S m)
        end
              
        <vec A m>
    | vecc _ n' a l' => 
      abbrev Sn'_eq_n = inj <vec A *> symm l_Eq in
      abbrev Sn'_eq_Sm =
        transs 
          Sn'_eq_n
          u
        end
      in
      abbrev n'_eq_m = inj (S *) Sn'_eq_Sm in
      match l' with
        | vecn _ => 
          cast (vecn A) by
            abbrev Z_eq_n' = inj <vec A *> symm l'_Eq in
            abbrev Z_eq_m = trans Z_eq_n' n'_eq_m in
            cong <vec A *> Z_eq_m                
        | vecc _ n'' _ l'' =>
          abbrev n'_eq_Sn'' = inj <vec ** *> l'_Eq in
          abbrev n_eq_Sn' = inj <vec ** *> l_Eq in
          abbrev rest_all_but_last =
            (vec_all_but_last A n' n'' n'_eq_Sn'' l')
          in
          cast (vecc A n'' a rest_all_but_last) by
            abbrev Sn''_eq_n' = 
              inj <vec A *> 
                  symm l'_Eq
            in
            abbrev Sn''_eq_m = 
              trans Sn''_eq_n' 
                    n'_eq_m
            in
            cong <vec A *> Sn''_eq_m 
      end
  end.

%-
Define vec_back_cons :
  Forall(A: type)(n: nat)(u: { n != Z })(v: <vec A n>).
    { (vec_append (vec_all_but_last v) (vecc (vec_last v) vecn)) = v }
  :=
  foralli(A: type)(n: nat)(u: { n != Z })(v: <vec A n>).
  hypjoin (vec_append (vec_all_but_last v) (vecc (vec_last v) vecn)) v by end.

  foralli(A: type).
  induction(n: nat)
  return
    Forall(u: { n != Z })(v: <vec A n>). 
      { (vec_append (vec_all_but_last v) (vec_last v)) = v }
  with
    | Z =>
      foralli(u: { n != Z })(v: <vec A n>).
        contra
          trans n_eq
                symm u

          { (vec_append (vec_all_but_last v) (vec_last v)) = v }
    | S n' =>
      foralli(u: { n != Z })(v: <vec A n>).
      case v with
        | vecn _ =>
          contra
            transs
              symm n_eq 
              inj <vec A *> v_Eq
              clash Z (S n)
            end

            { (vec_append (vec_all_but_last v) (vec_last v)) = v }
        | vecc A restLen a rest =>
          abbrev Sn'_eq_SrestLen =
            trans symm n_eq
                  inj <vec A *> v_Eq
          end
          abbrev n'_eq_restLen = inj (S *) Sn'_eq_SrestLen in
          
          case n' with
            | Z =>
              
          
      end

      %case n' with
      %  | Z =>
      %    case v with
      %  | S n'' =>
      %end      
  end.
  -%
   
  %hypjoin (vec_append (vec_all_but_last v) (vec_last v)) v by end.

Define vec_vecc_shift : 
  Forall(A: type)
        (n: nat)
        (v: <vec A n>)
        (m: nat)
        (u: { (lt m n) = tt } )
        (a: A)
        . 
        abbrev v' = (vecc a v) in 
        { (vec_get v m) = (vec_get v' (S m)) }
  :=   
  foralli(A: type)(n: nat).
  case n with
    | Z =>
      foralli(v: <vec A n>)(m:nat)(u: { (lt m n) = tt } )(a: A).
      contra
        transs
          symm u
          cong (lt m *) n_eq
          [lt_Z m]
          clash ff tt
        end
        
        abbrev v' = (vecc a v) in
        { (vec_get v m) = (vec_get v' (S m)) }
    | S n' =>
      foralli(v: <vec A n>)(m:nat)(u: { (lt m n) = tt } )(a: A).
      abbrev v' = (vecc a v) in

      case v with
        | vecn _ =>
          abbrev Z_neq_n =
            trans clash Z (S n') 
                  symm n_eq
          in

          contra
            trans inj <vec ** *> v_Eq
                  Z_neq_n

            { (vec_get v m) = (vec_get v' (S m)) }
        | vecc _ restLen x rest =>
          hypjoin (vec_get v m) (vec_get v' (S m)) by v_eq end
      end
  end.  

Define vec_vecc_last_invariant :
  Forall(A: type)
        (n: nat)
        (u: { n != Z })
        (v: <vec A n>)
        (a: A)
        .
        { (vec_last v) = (vec_last (vecc a v)) }
  :=
  foralli(A: type)(n: nat)(u: { n != Z })(v: <vec A n>)(a: A).
  abbrev v' = (vecc a v) in
  case v with
    | vecn _ =>
      contra
        transs
          inj <vec ** *> v_Eq
          symm u
        end
        
        { (vec_last v) = (vec_last (vecc a v)) }
    | vecc _ n' a' rest =>
      hypjoin (vec_last v) (vec_last v') by v_eq end
  end.

Define last_eq_get_pred_n :
  Forall(A: type)
        (n: nat)
        (m: nat)
        (u: { (S m) = n })
        (v: <vec A n>)
        .
        { (vec_get v m) = (vec_last v) }
  :=
  foralli(A: type).
  induction(n: nat) 
  return
    Forall(m: nat)(u: { (S m) = n })(v: <vec A n>). { (vec_get v m) = (vec_last v) }
  with
    | Z =>
      foralli(m: nat)(u: { (S m) = n })(v: <vec A n>).
      contra
        transs
          symm n_eq %{ (Z = n) }
          symm u
          clash (S m) Z
        end

        { (vec_get v m) = (vec_last v) }
    | S n' =>
      foralli(m: nat)(u: { (S m) = n })(v: <vec A n>).
      abbrev Sn'_eq_Sm =
        trans u
              n_eq
      in
      abbrev m_eq_n' = inj (S *) Sn'_eq_Sm in
        
      case v with
        | vecn _ =>
          contra
            transs
              symm n_eq
              inj <vec ** *> v_Eq
              clash Z (S n')
            end

            { (vec_get v m) = (vec_last v) }
        | vecc _ restLen a rest =>
          abbrev SrestLen_eq_Sn' =
            trans inj <vec ** *> symm v_Eq %(S restLen) = n
                  n_eq
          in
          abbrev restLen_eq_n' = inj (S *) SrestLen_eq_Sn' in

          case m with
            | Z =>
              %we need to know rest = vecn in this case ****************
              
              case rest with
                | vecn _ =>
                  hypjoin (vec_get v m) (vec_last v) by v_eq m_eq rest_eq end
                | vecc _ x _ _ =>
                  contra
                    transs
                      symm m_eq
                      m_eq_n'
                      symm restLen_eq_n'
                      inj <vec ** *> rest_Eq %<vec A restLen> = <vec A (S x)>
                      clash (S x) Z
                    end

                    { (vec_get v m) = (vec_last v) }
              end
            | S m' =>
              abbrev Sm'_eq_n' = hypjoin (S m') n' by m_eq_n' m_eq n_eq end in
              abbrev Sm'_le_n' = [eq_le (S m') n' Sm'_eq_n'] in
              abbrev m'_lt_Sm' = [lt_S m'] in
              abbrev m'_lt_n' = [ltle_trans m' (S m') n' m'_lt_Sm' Sm'_le_n'] in
              % (vec_get rest m') = (vec_last rest)
              abbrev indStep = 
                [n_IH 
                  n' 
                  m' 
                  Sm'_eq_n' 
                  cast rest by cong <vec A *> restLen_eq_n'
                ]
              in
              abbrev n'_neq_Z =
                trans symm Sm'_eq_n'
                      clash (S m') Z
              in      
              % { (vec_last rest) = (vec_last (vecc a rest)) }
              abbrev last_rest_eq_last_v =
                [vec_vecc_last_invariant 
                  A 
                  n' 
                  n'_neq_Z 
                  cast rest by cong <vec A *> restLen_eq_n'
                  a
                ]
              in

              % { (vec_get rest m') = (vec_get (vecc a rest) (S m')) }
              % hypjoin makes this unnecessary. however, if we use this as a
              % hypjoin lemma, guru claims that it doesn't prove an equation.
              % is this a bug?
              abbrev rest_shift =
                [vec_vecc_shift
                  A
                  n'
                  cast rest by cong <vec A *> restLen_eq_n'
                  m'
                  m'_lt_n'
                  a
                ]
              in

              hypjoin (vec_get v m) (vec_last v) by 
                indStep
                last_rest_eq_last_v
                v_eq
                m_eq
              end
              
          end
      end
  end.

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

Define eqvec_neq 
  : Forall(A:type)
          (eqA:Fun(x y:A).bool)
          (eqA_refl : Forall(x:A). {(eqA x x) = tt})
          (n:nat)
          (x y:<vec A n>)
          (u: { (eqvec eqA x y) = ff }).
          { x != y } :=
  foralli(A:type)(eqA:Fun(x y:A).bool)
          (eqA_refl : Forall(x:A). {(eqA x x) = tt})
          (n:nat)
          (x y:<vec A n>)
          (u: { (eqvec eqA x y) = ff }).
    diseqi foralli(v:{x = y}).
           contra
             transs symm u
                    cong (eqvec eqA * y) v
                    [eqvec_refl A eqA eqA_refl n y]
                    clash tt ff
             end
           False.
	   
Define neq_vecneq
  : Forall(A:type)
          (eqA:Fun(x y:A).bool)
          (eqA_eq : Forall(x y:A)(u:{(eqA x y) = tt}).{x = y})
          (eqA_tot : Forall(x y:A).Exists(b:bool). {(eqA x y) = b})
          (n:nat)
          (x y:<vec A n>)
          (u: { x != y }).
          { (eqvec eqA x y) = ff } :=
  foralli(A:type)
         (eqA:Fun(x y:A).bool)
         (eqA_eq : Forall(x y:A)(u:{(eqA x y) = tt}).{x = y})
         (eqA_tot : Forall(x y:A).Exists(b:bool). {(eqA x y) = b})
         (n:nat)
         (x y:<vec A n>)
         (u: { x != y }).
    case terminates (eqvec A eqA n x y) by [eqvec_tot A eqA eqA_tot n x y] by v _ with
      ff => v
    | tt => contra
              trans [eqvec_eq A eqA eqA_eq n x y v]
                    symm u 
            { (eqvec eqA x y) = ff }
    end.

Define eqvec_symm
  : Forall(A:type)
          (eqA:Fun(x y:A).bool)
          (eqA_refl : Forall(x:A). {(eqA x x) = tt})
          (eqA_eq : Forall(x y:A)(u:{(eqA x y) = tt}).{x = y})
          (eqA_tot : Forall(x y:A).Exists(b:bool). {(eqA x y) = b})
          (n:nat)
          (x y:<vec A n>).
      { (eqvec eqA x y) = (eqvec eqA y x) } :=
  foralli(A:type)
         (eqA:Fun(x y:A).bool)
         (eqA_refl : Forall(x:A). {(eqA x x) = tt})
         (eqA_eq : Forall(x y:A)(u:{(eqA x y) = tt}).{x = y})
         (eqA_tot : Forall(x y:A).Exists(b:bool). {(eqA x y) = b})
	 (n:nat)
	 (x y:<vec A n>).
  case terminates (eqvec A eqA n x y) by [eqvec_tot A eqA eqA_tot n x y] by q1 _ with
    ff => trans q1
                symm [neq_vecneq A eqA eqA_eq eqA_tot n y x symm [eqvec_neq A eqA eqA_refl n x y q1]]
  | tt => trans cong (eqvec eqA * y) [eqvec_eq A eqA eqA_eq n x y q1]
                cong (eqvec eqA y *) symm [eqvec_eq A eqA eqA_eq n x y q1]
  end.

Define eqvec_trans
  : Forall(A:type)
          (eqA:Fun(x y:A).bool)
          (eqA_refl : Forall(x:A). {(eqA x x) = tt})
          (eqA_eq : Forall(x y:A)(u:{(eqA x y) = tt}).{x = y})
          (eqA_tot : Forall(x y:A).Exists(b:bool). {(eqA x y) = b})
          (n:nat)
          (x y z:<vec A n>)
          (u1: { (eqvec eqA x y) = tt })
          (u2: { (eqvec eqA y z) = tt }).
      { (eqvec eqA x z) = tt } :=
  foralli(A:type)
         (eqA:Fun(x y:A).bool)
         (eqA_refl : Forall(x:A). {(eqA x x) = tt})
         (eqA_eq : Forall(x y:A)(u:{(eqA x y) = tt}).{x = y})
         (eqA_tot : Forall(x y:A).Exists(b:bool). {(eqA x y) = b})
	 (n:nat)
	 (x y z:<vec A n>)
	 (u1: { (eqvec eqA x y) = tt })
         (u2: { (eqvec eqA y z) = tt }).
  case terminates (eqvec A eqA n x y) by [eqvec_tot A eqA eqA_tot n x y] by q1 _ with
    ff =>
      contra
        trans
	  trans symm q1 u1
	  clash tt ff
	{ (eqvec eqA x z) = tt }
  | tt =>
      case terminates (eqvec A eqA n y z) by [eqvec_tot A eqA eqA_tot n y z] by q2 _ with
        ff => contra
	        trans
		  trans symm q2 u2
		  clash tt ff
		{ (eqvec eqA x z) = tt }
      | tt => symm trans symm [eqvec_refl A eqA eqA_refl n x]
                   cong (eqvec eqA x *)
	           trans [eqvec_eq A eqA eqA_eq n x y q1]
	                 [eqvec_eq A eqA eqA_eq n y z q2]
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

Define spec vec_all : Fun(A:type)( spec n : nat )
                         (f:Fun(a:A).bool)(l:<vec A n>).bool :=
  fun(A:type)( spec n : nat )
     (f:Fun(a:A).bool)(l:<vec A n>).
        (vec_forall A bool n tt fun(c:bool)(a:A).(f a) l).

% fast-failing version
Define vec_allff : Fun(A:type)(spec n:nat)(f:Fun(a:A).bool)(v:<vec A n>).bool :=
  fun vec_all (A:type)(spec n:nat)(f:Fun(a:A).bool)(v:<vec A n>) : bool.
    match v with
      vecn _ => tt
    | vecc _ n' a v' => match (f a) with
                          ff => ff
                        | tt => (vec_all A n' f v')
                        end
    end.

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

Define vec_update_get :
  Forall(A:type)(n:nat)(l:<vec A n>)
        (m:nat)(a:A)
        (u:{ (lt m n) = tt }).
    { (vec_get (vec_update l m u a) m u) = a }
  :=
  foralli(A:type).
  induction(n:nat)(l:<vec A n>) return 
    Forall(m:nat)(a:A)
          (u:{ (lt m n) = tt }).
      { (vec_get (vec_update l m u a) m u) = a }
  with
    vecn _ =>
      foralli(m:nat)(a:A)
             (u:{ (lt m n) = tt }).
      abbrev n_Z = inj <vec ** *> l_Eq in
      abbrev p = hypjoin (lt m n) ff by n_Z [lt_Z m] end in
      contra trans symm u
             trans p
                   clash ff tt
             { (vec_get (vec_update l m u a) m u) = a }
  | vecc _ n' a' l' =>
      foralli(m:nat)(a:A)
             (u:{ (lt m n) = tt }).
      case m with
        Z => hypjoin (vec_get (vec_update l m u a) m u) a by m_eq l_eq end
      | S m' =>
          abbrev n'_pf = inj <vec ** *> l_Eq in
          abbrev p1 = hypjoin (lt (S m') (S n')) tt by m_eq u n'_pf end in
          abbrev u' = hypjoin (lt m' n') tt by [S_lt_S m' n'] p1 end in
          
          hypjoin (vec_get (vec_update l m u a) m u)
                  a
                  by l_eq m_eq [l_IH n' l' m' a u'] end
      end
  end
  .

Define vec_update_get_gt :
  Forall(A:type)(n:nat)(l:<vec A n>)
        (m i:nat)(a:A)
        (u1:{ (lt m n) = tt })
        (u2:{ (lt i m) = tt })
    .{ (vec_get (vec_update l i a) m) = (vec_get l m) }
  :=
  foralli(A:type).
  induction(n:nat)(l:<vec A n>) return 
    Forall(m i:nat)(a:A)
					(u1:{ (lt m n) = tt })
					(u2:{ (lt i m) = tt })
				.{ (vec_get (vec_update l i a) m) = (vec_get l m) }
  with
    vecn _ =>
      foralli(m i:nat)(a:A)
						(u1:{ (lt m n) = tt })
						(u2:{ (lt i m) = tt })
			.
      abbrev n_Z = inj <vec ** *> l_Eq in
      abbrev p = hypjoin (lt m n) ff by n_Z [lt_Z m] end in
      contra trans symm u1
             trans p
                   clash ff tt
						{ (vec_get (vec_update l i a) m) = (vec_get l m) }

  | vecc _ n' a' l' =>
      foralli(m i:nat)(a:A)
					(u1:{ (lt m n) = tt })
					(u2:{ (lt i m) = tt })
			.
      case m with
        Z =>
	        contra
						trans symm hypjoin (lt i m) ff by m_eq [lt_Z i] end
						trans u2
									clash tt ff
						{ (vec_get (vec_update l i a) m) = (vec_get l m) }
      | S m' =>
        	case i with
        	  Z =>
        	  	hypjoin (vec_get (vec_update l i a) m) (vec_get l m) by l_eq m_eq i_eq end
        	| S i' =>
							abbrev n_eq = inj <vec ** *> l_Eq in
							abbrev u1' = hypjoin (lt m' n') tt by [S_lt_S m' n'] m_eq n_eq u1 end in
							abbrev u2' = hypjoin (lt i' m') tt by [S_lt_S i' m'] m_eq i_eq u2 end in
							abbrev ih = [l_IH n' l' m' i' a u1' u2'] in
							hypjoin (vec_get (vec_update l i a) m) (vec_get l m) by l_eq m_eq i_eq ih end
					end
      end
  end
  .

Define vec_update_get_lt :
  Forall(A:type)(n:nat)(l:<vec A n>)
        (m i:nat)(a:A)
        (u1:{ (lt i n) = tt })
        (u2:{ (lt m i) = tt })
    .{ (vec_get (vec_update l i a) m) = (vec_get l m) }
  :=
  foralli(A:type).
  induction(n:nat)(l:<vec A n>) return 
    Forall(m i:nat)(a:A)
					(u1:{ (lt i n) = tt })
					(u2:{ (lt m i) = tt })
				.{ (vec_get (vec_update l i a) m) = (vec_get l m) }
  with
    vecn _ =>
      foralli(m i:nat)(a:A)
						(u1:{ (lt i n) = tt })
						(u2:{ (lt m i) = tt })
			.
      abbrev n_Z = inj <vec ** *> l_Eq in
      abbrev p = hypjoin (lt i n) ff by n_Z [lt_Z i] end in
      contra trans symm u1
             trans p
                   clash ff tt
						{ (vec_get (vec_update l i a) m) = (vec_get l m) }
  | vecc _ n' a' l' =>
      foralli(m i:nat)(a:A)
					(u1:{ (lt i n) = tt })
					(u2:{ (lt m i) = tt })
			.
      case m with
        Z =>
        	case i with
        	  Z => contra
        	  				trans symm hypjoin (lt m i) ff by m_eq i_eq end
        	  				trans u2
        	  							clash tt ff
        	  				{ (vec_get (vec_update l i a) m) = (vec_get l m) }
        	| S i' =>
		        	hypjoin (vec_get (vec_update l i a) m) (vec_get l m) by m_eq l_eq i_eq end
        	end
      | S m' =>
        	case i with
        	  Z => contra
        	  				trans symm hypjoin (lt m i) ff by m_eq i_eq end
        	  				trans u2
        	  							clash tt ff
        	  				{ (vec_get (vec_update l i a) m) = (vec_get l m) }
        	| S i' =>
							abbrev n_eq = inj <vec ** *> l_Eq in
							abbrev u1' = hypjoin (lt i' n') tt by [S_lt_S i' n'] i_eq n_eq u1 end in
							abbrev u2' = hypjoin (lt m' i') tt by [S_lt_S m' i'] m_eq i_eq u2 end in
							abbrev ih = [l_IH n' l' m' i' a u1' u2'] in
							hypjoin (vec_get (vec_update l i a) m) (vec_get l m) by l_eq m_eq i_eq ih end
					end
      end
  end
  .

Define vec_update_get_distinct :
  Forall(A:type)(n:nat)(l:<vec A n>)
        (m i:nat)(a:A)
        (u1:{ (lt m n) = tt })
        (u2:{ (lt i n) = tt })
        (u3:{ m != i })
    .{ (vec_get (vec_update l i a) m) = (vec_get l m) }
  :=
  foralli(A:type)(n:nat)(l:<vec A n>)
        (m i:nat)(a:A)
        (u1:{ (lt m n) = tt })
        (u2:{ (lt i n) = tt })
        (u3:{ m != i })
  .
  case (lt m i) by q1 _ with
    ff =>
    	case (lt i m) by q2 _ with
    		ff =>
    			abbrev p1_1 = [lt_ff_implies_le m i q1] in
    			abbrev p1_2 = [lt_ff_implies_le i m q2] in
    			abbrev p1 = [le_bounds m i p1_2 p1_1] in
    			contra trans p1 symm u3
    				{ (vec_get (vec_update l i a) m) = (vec_get l m) }
    	| tt => [vec_update_get_gt A n l m i a u1 q2]
    	end
  | tt => [vec_update_get_lt A n l m i a u2 q1]
  end.


Define vec_sz_Z_vecn :=
  foralli(A:type)(l:<vec A Z>).
  case l with
  	vecn _ => l_eq
  | vecc _ n' a l' =>
  		abbrev Z_eq = inj <vec ** *> l_Eq in % Z = (S n')
  		contra Z_eq { l = vecn }
  end.

Define all_vec_get_implies_eq :
	Forall(A:type)(n:nat)(l m:<vec A n>)
				(u:Forall(i:nat)(q:{ (lt i n) = tt }).{ (vec_get l i) = (vec_get m i) })
			 .{ l = m }
	:=
  foralli(A:type).
  induction(n:nat)(l:<vec A n>) return
    Forall(m:<vec A n>)
    			(u:Forall(i:nat)(q:{ (lt i n) = tt }).{ (vec_get l i) = (vec_get m i) })
      .{ l = m }
  with
    vecn _ =>
			foralli(m:<vec A n>)
						 (u:Forall(i:nat)(q:{ (lt i n) = tt }).{ (vec_get l i) = (vec_get m i) })
			.
      abbrev n_eq = inj <vec A *> l_Eq in
      abbrev m_eq = [vec_sz_Z_vecn A cast m by cong <vec A *> n_eq] in
      hypjoin l m by l_eq m_eq end
  | vecc _ n' a' l' =>
			foralli(m:<vec A n>)
						 (u:Forall(i:nat)(q:{ (lt i n) = tt }).{ (vec_get l i) = (vec_get m i) })
			.
      abbrev n_eq = inj <vec A *> l_Eq in
      case m with
      	vecn _ =>
      		abbrev n_eq' = inj <vec ** *> m_Eq in
      		contra trans symm n_eq'
      					 trans n_eq
      					 			 clash (S n') Z
      			{ l = m }
     	| vecc _ mn' ma' m' =>
					abbrev n_eq' = inj <vec A *> m_Eq in
					abbrev m'_1 = inj (S *) symm trans symm n_eq n_eq' in
					abbrev m' = cast m' by cong <vec A *> m'_1 in
					abbrev u' = foralli(i':nat)(q':{ (lt i' n') = tt }).
											abbrev p1 = hypjoin (lt (S i') n) tt by q' n_eq end in
											hypjoin (vec_get l' i') (vec_get m' i') by l_eq m_eq [u (S i') p1] end in
					abbrev p1 = hypjoin (lt Z n) tt by n_eq end in
					abbrev p2 = hypjoin a' ma' by l_eq m_eq [u Z p1] end in
					abbrev ih = [l_IH n' l' m' u'] in
					hypjoin l m by ih p2 l_eq m_eq end
      end
  end.


Define all_vec_get_implies_mkvec :
	Forall(A:type)(a:A)(n:nat)(l:<vec A n>)
				(u:Forall(m:nat)(q:{ (lt m n) = tt }).{ (vec_get l m) = a })
			 .{ l = (mkvec a n) }
	:=
  foralli(A:type)(a:A).
  induction(n:nat)(l:<vec A n>) return
    Forall(u:Forall(m:nat)(q:{ (lt m n) = tt }).{ (vec_get l m) = a })
      .{ l = (mkvec a n) }
  with
    vecn _ =>
      foralli(u:Forall(m:nat)(q:{ (lt m n) = tt }).{ (vec_get l m) = a }).
      abbrev n_eq = inj <vec A *> l_Eq in
      hypjoin l (mkvec a n) by l_eq n_eq end
  | vecc _ n' a' l' =>
      foralli(u:Forall(m:nat)(q:{ (lt m n) = tt }).{ (vec_get l m) = a }).
      abbrev n_eq = inj <vec A *> l_Eq in
      abbrev p2 = hypjoin (lt Z n) tt by n_eq end in
      abbrev a_eq = hypjoin a' a by l_eq [u Z p2] end in
      abbrev u' = foralli(m':nat)(q':{ (lt m' n') = tt }).
                  abbrev p1 = hypjoin (lt (S m') n) tt by q' n_eq end in
                  hypjoin (vec_get l' m') a by l_eq [u (S m') p1] end in
      hypjoin l (mkvec a n) by [l_IH n' l' u'] l_eq a_eq n_eq end
  end.


Define vec_update_twice :
  Forall(A:type)(n:nat)(v:<vec A n>)
        (i:nat)(a a':A)
        (u:{ (lt i n) = tt }).
    { (vec_update (vec_update v i a) i a') = (vec_update v i a') }
  :=
  foralli(A:type)(n:nat)(v:<vec A n>)
        (i:nat)(a a':A)
        (u:{ (lt i n) = tt }).
	abbrev v' = (vec_update A n v i a u) in
	abbrev v'' = (vec_update A n v' i a' u) in
  abbrev p1 =
		foralli(m:nat)(u2:{ (lt m n) = tt }).
		case (eqnat m i) by q1 _ with
			ff =>
				abbrev u3 = [eqnat_ff_implies_neq m i q1] in
			 	trans [vec_update_get_distinct A n v' m i a' u2 u u3]
				trans [vec_update_get_distinct A n v m i a u2 u u3]
				      symm [vec_update_get_distinct A n v m i a' u2 u u3]
		| tt =>
				abbrev p1 = [eqnatDef m i q1] in
				trans cong (vec_get (vec_update (vec_update v i a) i a') *) p1
				trans [vec_update_get A n v' i a' u]
				trans symm [vec_update_get A n v i a' u]
				      cong (vec_get (vec_update v i a') *) symm p1
		end
		in
	[all_vec_get_implies_eq A n v'' (vec_update A n v i a' u) p1]
	.

Define vec_update_back :
  Forall(A:type)(n:nat)(v:<vec A n>)
        (i:nat)
        (u:{ (lt i n) = tt }).
    { (vec_update v i (vec_get v i)) = v }
  :=
  foralli(A:type)(n:nat)(v:<vec A n>)
        (i:nat)
        (u:{ (lt i n) = tt }).
	abbrev x = (vec_get A n v i u) in
	abbrev v' = (vec_update A n v i x u) in
  abbrev p1 =
		foralli(m:nat)(u2:{ (lt m n) = tt }).
		case (eqnat m i) by q1 _ with
			ff =>
				abbrev u3 = [eqnat_ff_implies_neq m i q1] in
				[vec_update_get_distinct A n v m i x u2 u u3]
		| tt =>
				abbrev p1 = [eqnatDef m i q1] in
				trans cong (vec_get (vec_update v i (vec_get v i)) *) p1
				trans [vec_update_get A n v i x u]
							cong (vec_get v *) symm p1
		end
		in
	[all_vec_get_implies_eq A n v' v p1]
	.

Define vec_update_append :
  Forall(A:type)(a:A)(n1 n2:nat)(l1:<vec A n1>)(l2:<vec A n2>).
     { (vec_update (vec_append l1 l2) n1 a) = (vec_append l1 (vec_update l2 Z a)) } :=
  foralli(A:type)(a:A).
  induction(n1 n2:nat)(l1:<vec A n1>)
  return Forall(l2:<vec A n2>).
          { (vec_update (vec_append l1 l2) n1 a) = (vec_append l1 (vec_update l2 Z a)) } with
  vecn _ => foralli(l2:<vec A n2>).
              hypjoin (vec_update (vec_append l1 l2) n1 a) (vec_append l1 (vec_update l2 Z a))
              by l1_eq inj <vec ** *> l1_Eq end
| vecc _ n1' x l1' => 
  foralli(l2:<vec A n2>).
      hypjoin (vec_update (vec_append l1 l2) n1 a) (vec_append l1 (vec_update l2 Z a))
      by l1_eq inj <vec ** *> l1_Eq [l1_IH n1' n2 l1' l2] end
end.


Define vec_all_vecc_tt_head :
  Forall(A:type)
        (f:Fun(a:A).bool)
        (a:A)(n:nat)(v:<vec A n>)
        (u:{ (vec_all f (vecc a v)) = tt }).
    { (f a) = tt }
  :=
  foralli(A:type)
         (f:Fun(a:A).bool)
         (a:A)(n:nat)(v:<vec A n>)
         (u:{ (vec_all f (vecc a v)) = tt }).
  abbrev p1 = eval (vec_all f (vecc a v)) in
  abbrev p2 = cinv (f a) trans symm p1 u in
  existse p2
  foralli(z1:bool)(z1_pf:{ (f a) = z1 }).

  case z1 with
    ff => contra
            trans symm u
            trans hypjoin (vec_all f (vecc a v)) ff by z1_pf z1_eq end
                  clash ff tt
            { (f a) = tt }
  | tt => hypjoin (f a) tt by z1_pf z1_eq end
  end
  .

Define  vec_all_vecc_tt_tail :
  Forall(A:type)
        (f:Fun(a:A).bool)
        (a:A)(n:nat)(v:<vec A n>)
        (u:{ (vec_all f (vecc a v)) = tt }).
    { (vec_all f v) = tt }
  :=
  foralli(A:type)
        (f:Fun(a:A).bool)
        (a:A)(n:nat)(v:<vec A n>)
        (u:{ (vec_all f (vecc a v)) = tt }).
  abbrev p1 = eval (vec_all f (vecc a v)) in
  abbrev p2 = cinv (f a) trans symm p1 u in
  existse p2
  foralli(z1:bool)(z1_pf:{ (f a) = z1 }).
  case z1 with
    ff => contra
            trans symm u
            trans hypjoin (vec_all f (vecc a v)) ff by z1_pf z1_eq end
                  clash ff tt
            { (vec_all f v) = tt }
  | tt => hypjoin (vec_all f v) tt by z1_pf z1_eq u end
  end
  .

% prove a lemma that says if vec_all holds for a vector v with some predicate f,
% and f holds for an element, then vec_all with f holds for the vector we get by updating v (in bounds).
Define vec_all_update :
  Forall(A:type)(n:nat)(m:nat)(v:<vec A n>)(a:A)
        (f:Fun(a:A).bool)
        (u1 : { (lt m n) = tt})
        (u2 : { (vec_all f v) = tt})
        (u3 : { (f a) = tt}).
  { (vec_all f (vec_update v m a u1)) = tt } :=
  foralli(A:type)(n:nat)(m:nat)(v:<vec A n>)(a:A)
        (f:Fun(a:A).bool)
        (u1 : { (lt m n) = tt})
        (u2 : { (vec_all f v) = tt})
        (u3 : { (f a) = tt}).
  [induction(n:nat)(v:<vec A n>) return
    Forall(m:nat)(u1 : { (lt m n) = tt }) 
                 (u2 : { (vec_all f v) = tt }).
      { (vec_all f (vec_update v m a u1)) = tt } with
    vecn _ => foralli(m:nat)(u1 : { (lt m n) = tt })
                     (u2 : { (vec_all f v) = tt }).
      abbrev n_Z = inj <vec ** *> v_Eq in
      abbrev p = hypjoin (lt m n) ff by n_Z [lt_Z m] end in
      contra trans symm u1
             trans p
                   clash ff tt
             { (vec_all f (vec_update v m a u1)) = tt }
    | vecc _ n' x v' =>
      foralli(m:nat)(u1 : { (lt m n) = tt })
             (u2 : { (vec_all f v) = tt }).
      abbrev P = trans symm cong (vec_all f *) v_eq u2 in
      case m with
        Z => 
            hypjoin (vec_all f (vec_update v m a u1)) tt
            by m_eq v_eq u3
               [vec_all_vecc_tt_tail A f x n' v' P]
	    end
      | S m' => 
            abbrev n'_pf = inj <vec ** *> v_Eq in
            abbrev p1 = hypjoin (lt (S m') (S n')) tt by m_eq u1 n'_pf end in
            abbrev u1' = hypjoin (lt m' n') tt by [S_lt_S m' n'] p1 end in

            hypjoin (vec_all f (vec_update v m a u1)) tt
            by m_eq v_eq u3
               [vec_all_vecc_tt_head A f x n' v' P]
	       [v_IH n' v' m' hypjoin (lt m' n') tt
                             by u1' m_eq v_eq end
               [vec_all_vecc_tt_tail A f x n' v' P]]
	     end
        end
    end n v m u1 u2].

Define vec_all_get :
  Forall(A:type)(n:nat)(m:nat)(v:<vec A n>)
        (f:Fun(a:A).bool)
        (u1 : { (lt m n) = tt})
        (u2 : { (vec_all f v) = tt}).
  { (f (vec_get v m)) = tt } :=
  foralli(A:type)(n:nat)(m:nat)(v:<vec A n>)
        (f:Fun(a:A).bool)
        (u1 : { (lt m n) = tt})
        (u2 : { (vec_all f v) = tt}).
  [induction(n:nat)(v:<vec A n>) return
    Forall(m:nat)(u1 : { (lt m n) = tt }) 
                 (u2 : { (vec_all f v) = tt }).
      { (f (vec_get v m)) = tt } with
    vecn _ => foralli(m:nat)(u1 : { (lt m n) = tt })
                     (u2 : { (vec_all f v) = tt }).
      abbrev n_Z = inj <vec ** *> v_Eq in
      abbrev p = hypjoin (lt m n) ff by n_Z [lt_Z m] end in
      contra trans symm u1
             trans p
                   clash ff tt
             { (f (vec_get v m)) = tt }
    | vecc _ n' x v' => 
      foralli(m:nat)(u1 : { (lt m n) = tt })
             (u2 : { (vec_all f v) = tt }).
      abbrev P = trans symm cong (vec_all f *) v_eq u2 in
      case m with
        Z =>
	    abbrev p1 = hypjoin (vec_get v m) x by m_eq v_eq end in

	    trans cong (f *) p1 [vec_all_vecc_tt_head A f x n' v' P]
      | S m' => 
	    [v_IH n v m u1 u2]
        end
    end n v m u1 u2].

Define mkvec_implies_vec_get : Forall
	(A:type)(a:A)(n:nat)(v:<vec A n>)(i:nat)(u:{ (lt i n) = tt})
	.{ (vec_get (mkvec a n) i) = a }
	:=
	foralli(A:type)(a:A).
	induction(n:nat)(v:<vec A n>) return Forall
		(i:nat)(u:{ (lt i n) = tt})
		.{ (vec_get (mkvec a n) i) = a }
	with
	| vecn _ => foralli
		(i:nat)(u:{ (lt i n) = tt})
		.
		cabbrev n_eq = inj <vec ** *> v_Eq
		contra
		trans symm u
		trans hypjoin (lt i n) ff by n_eq [lt_Z i] end
					clash ff tt
		{ (vec_get (mkvec a n) i) = a }
	| vecc _ n' x v' => foralli
		(i:nat)(u:{ (lt i n) = tt})
		.
		cabbrev n_eq = inj <vec ** *> v_Eq
		case i with
		| Z =>
			hypjoin (vec_get (mkvec a n) i) a by i_eq n_eq end
		| S i' =>
			cabbrev u' = hypjoin (lt i' n') tt by u i_eq n_eq end
			cabbrev ih = [v_IH n' v' i' u']
			hypjoin (vec_get (mkvec a n) i) a by i_eq n_eq ih end
		end
	end

Define trusted mkvec_implies_vec_all :
  Forall(A:type)(a:A)(n:nat)(v:<vec A n>)
        (f:Fun(a:A).bool)
        (u1: { v = (mkvec a n) })
        (u2: { (f a) = tt }).
        { (vec_all f v) = tt } :=
  foralli(A:type)(a:A)(f:Fun(a:A).bool).
  induction(n:nat)(v:<vec A n>) return
    Forall(u1: { v = (mkvec a n) })(u2: { (f a) = tt})
        .{ (vec_all f v) = tt }
  with
    vecn _ =>
      foralli(u1: { v = (mkvec a n) })(u2: { (f a) = tt}).
      hypjoin (vec_all f v) tt by v_eq end
  | vecc _ n' a' v' =>
      foralli(u1: { v = (mkvec a n) })(u2: { (f a) = tt}).

      abbrev n_eq = inj <vec A *> v_Eq in
      abbrev p1 = hypjoin (mkvec a n) (vecc a (mkvec a n')) by n_eq end in
      abbrev p2 = hypjoin (mkvec a n) (vecc a' v') by v_eq u1 end in
      abbrev p3 = trans symm p1 p2 in
      % show a = a'

      truei

  end.
