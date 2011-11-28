
Include "../lib/nat.g"
Include "../lib/bool.g"
Include "../lib/minus.g"
Include "../lib/vec.g"
Include "../lib/minmax.g"
Include "../../versat/src/lib_includes.g"
Include "../../versat/src/cnf-lemma.g"
  
Define matchLet :=
  fun(x : nat)(y : bool).
  match x with
  | Z =>
    tt
  | S n' =>
    let z = (and y tt) in
    z
  end.

Define matchLetProof
  : Forall(x : nat)(y: bool)(u1 : { (matchLet x y) = tt })
          (x' : nat)(u2 : { x = (S x')}). { y = tt }
:=
  foralli(x : nat)(y: bool)(u1 : { (matchLet x y) = tt })
         (x' : nat)(u2 : { x = (S x')}).
  lemma u2 in
  unjoin u1 with
  | foralli(p0 : { (and y tt) = tt }).
    unjoin p0 with
    | foralli(u : {y = tt}).
      u
    end
  end.

Inductive list2 : Fun(A:type).type :=
  | nil2 : Fun(A:type).<list2 A>
  | cons2 : Fun(A:type)(a:A)(l:<list2 A>). <list2 A>.

Define length_eq_Z2
  : Forall(A:type)(l:<list A>)
          (u:{ (length l) = Z}).
     { l = nil } :=
  foralli(A:type)(l:<list A>)
         (u:{ (length l) = Z}).
  unjoin u with
  | foralli(p0 : { l = nil }).
    p0
  end.

Define matchArgs :=
  fun(x : nat)(y : nat).
  let z = 
    match x with
    | Z =>
      one
    | S x' =>
      two
    end
  in
  (max z y).

Define matchArgsProof
:=
  foralli(x y : nat)(u : { (matchArgs x y) = two }).
  unjoin u with
  | foralli(p0 : { x = Z })(u : { (max one y) = two }).
    lemma
      : { (le y (max one y)) = tt }
        [max_easy y one]
      : { (le (max one y) two) = tt }
        [eq_le (max one y) two u]
    in
    [le_trans y (max one y) two ## ##] 
  | foralli(x0 : nat)(p0 : { x = (S x0) })(u : { (max two y) = two }).
    lemma
      : { (le y (max two y)) = tt }
        [max_easy y two]
      : { (le (max two y) two) = tt }
        [eq_le (max two y) two u]
    in
    [le_trans y (max two y) two ## ##]
  end.

Define list_setmember2 
	: Forall(A:type)(a:A)
			  (eqA:Fun(^#owned x y: A).bool)
			  (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
        (eqA_refl: Forall(a: A). { (eqA a a) = tt })
        (l'' l':<list A>).
    { (member a (append l' (cons a l'')) eqA) = tt }
:=
  foralli(A:type)(a:A)(eqA:Fun(^ #owned x y: A).bool)
         (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
         (eqA_refl: Forall(a: A). { (eqA a a) = tt })
         (l'' l': <list A>).
  [member_append_cons A a l' l'' eqA eqA_total eqA_refl].




Define eqlistEq2 : Forall(A:type)
                        (l1 l2:<list A>)
                        (eqA:Fun(x1 x2:A).bool)
                        (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o })
                        (eqA_eq:Forall(x1 x2:A)(u:{ (eqA x1 x2) = tt }).{ x1 = x2 })
                        (u:{ (eqlist eqA l1 l2) = tt }). { l1 = l2 } := 

  foralli(A:type).
  induction(l1:<list A>) by l1_eq l1_Eq IHl1 
    return Forall(l2:<list A>)
                 (eqA:Fun(x1 x2:A).bool)
                 (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o })
                 (eqA_eq:Forall(x1 x2:A)(u:{ (eqA x1 x2) = tt }).{ x1 = x2 })
                 (u:{ (eqlist eqA l1 l2) = tt }).
                 { l1 = l2 } 
  with
  | nil _ =>
    foralli(l2 : <list A>)(eqA:Fun(x1 x2:A).bool)
            (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o })
            (eqA_eq:Forall(x1 x2:A)(u:{ (eqA x1 x2) = tt }).{ x1 = x2 })
            (u:{ (eqlist eqA l1 l2) = tt }).

    lemma l1_eq in
    unjoin u with
    | foralli(p0 : { l2 = nil }).
      hypjoin l1 l2 by l1_eq p0 end
    end
  | cons _ h1 t1 =>
    foralli(l2 : <list A>)(eqA:Fun(x1 x2:A).bool)
            (eqA_total:Forall(x1 x2:A).Exists(o:bool).{ (eqA x1 x2) = o })
            (eqA_eq:Forall(x1 x2:A)(u:{ (eqA x1 x2) = tt }).{ x1 = x2 })
            (u:{ (eqlist eqA l1 l2) = tt }).
    lemma l1_eq in
    unjoin u with
    | foralli(l21 : A)(l22 : <list A>)
             (p0 : { l2 = (cons l21 l22) })
             (u : { (and (eqA h1 l21) (eqlist eqA t1 l22)) = tt }).
      lemma
        : { (eqlist eqA t1 l22) = tt }
          [and_eq_tt2 
            terminates (eqA h1 l21) by eqA_total
            terminates (eqlist A eqA t1 l22) by [eqlist_total A eqA eqA_total t1 l22]
            u
          ]

        : { (eqA h1 l21) = tt }
          [and_eq_tt1 
            terminates (eqA h1 l21) by eqA_total 
            terminates (eqlist A eqA t1 l22) by [eqlist_total A eqA eqA_total t1 l22] 
            u
          ]        
      in 
      hypjoin l1 l2 by
        : { h1 = l21 } [eqA_eq h1 l21 ##]
        : { t1 = l22 } [IHl1 t1 l22 eqA eqA_total eqA_eq ##]
        : { l2 = (cons l21 l22) } p0
        : { l1 = (cons h1 t1) } l1_eq
      end
    end
  end.


Define nth_append2 : Forall(A:type)(n:nat)(l:<list A>)(a:A)
                          (u:{(nth n l) = a}).
                       Exists(l1 l2:<list A>).
                         { l = (append l1 (cons a l2)) } :=
  foralli(A:type).
  induction (n: nat) 
    return Forall(l:<list A>)(a:A)(u:{(nth n l) = a}).
      Exists(l1 l2:<list A>). { l = (append l1 (cons a l2)) } 
  with
  | Z =>
    foralli(l:<list A>)(a:A)(u:{(nth n l) = a}).
    lemma n_eq in
    unjoin u with
    | foralli(l1 : A)(l2 : <list A>)(p0 : { l = (cons l1 l2) })
              (u : { l1 = a }).

      existsi (nil A) 
              Exists(e2 : <list A>). { l = (append * (cons a e2)) }
              existsi l2
                      { l = (append nil (cons a *)) }
                      hypjoin l (append nil (cons a l2)) by
                        : { l = (cons l1 l2) } p0
                        : { l1 = a } u
                      end
    end
  | S n' =>
    foralli(l:<list A>)(a:A)(u:{(nth n l) = a}).
    lemma n_eq in
    unjoin u with
    | foralli(l1 : A)(l2 : <list A>)(p0 : { l = (cons l1 l2) })
             (u : { (nth A n' l2) = a }).
      abbrev q0 =
      : Exists(l21 l22: <list A>). { l2 = (append l21 (cons a l22)) }
        [n_IH n' l2 a u]
      in

      abbrev q1 = 
      : Forall(l21 l22: <list A>)(u : { l2 = (append l21 (cons a l22)) }).
      Exists(v1 v2 : <list A>). { l = (append v1 (cons a v2)) }
        foralli(l21 l22: <list A>)(u : { l2 = (append l21 (cons a l22)) }).
        existsi (cons A l1 l21)
                Exists(v2 : <list A>). { l = (append * (cons a v2)) }
                existsi l22
                        { l = (append (cons l1 l21) (cons a *)) }
                        hypjoin l (append (cons l1 l21) (cons a l22)) by
                          : { l = (cons l1 l2) } p0
                          : { l2 = (append l21 (cons a l22)) } u
                        end
      in
      
      existse q0
              q1
    end
  end.


%-
  unjoin u with
  | foralli(p0 : { n = Z })(l1 : A)(l2 : <list A>)
           (p1 : { l = (cons l1 l2) })(u : { l1 = a }).

    existsi (nil A) 
            Exists(e2 : <list A>). { l = (append * (cons a e2)) }
            existsi l2
                    { l = (append nil (cons a *)) }
                    hypjoin l (append nil (cons a l2)) by
                      : { l = (cons l1 l2) } p1
                      : { l1 = a } u
                    end

  | foralli(n0 : nat)(p0 : { n = (S n0) })(l1 : A)(l2 : <list A>)
           (p1 : { l = (cons l1 l2) })(u : { (nth A n0 l2) = a }).
    lemma
      : Exists(l2' : <list A>). { l = (append 
    in
  end.

-%
Define set_nth_other2 : Forall(A:type)(l:<list A>)(n m:nat)(b:A)
                             (u:{ n != m }).
                        { (nth n (set_nth m l b)) = (nth n l) } :=
  foralli(A:type).
  induction(l:<list A>) 
    return Forall(n m:nat)(b:A)
                 (u:{ n != m }).
            { (nth n (set_nth m l b)) = (nth n l) } with
  | nil _ =>
    foralli(n m:nat)(b:A)(u:{ n != m }).
      hypjoin (nth n (set_nth m l b)) (nth n l) by l_eq end
  | cons _ a l' =>
    foralli(n m:nat)(b:A)(u:{ n != m }).
      case m with
        Z =>     
          case n with
            Z => contra trans m_eq
                              trans symm n_eq u
                   { (nth n (set_nth m l b)) = (nth n l) }
          | S n' => 
              hypjoin (nth n (set_nth m l b)) (nth n l)
                by l_eq m_eq n_eq end
          end
      | S m' => 
          case n with
            Z => hypjoin (nth n (set_nth m l b)) (nth n l)
                   by l_eq m_eq n_eq end
          | S n' => 
            hypjoin (nth n (set_nth m l b)) (nth n l)
              by l_eq m_eq n_eq 
                 [l_IH l' n' m' b 
                    diseqi foralli(u1:{n' = m'}).
                           contra
                             transs cong (S *) u1
                                    symm m_eq
                                    symm trans symm n_eq u 
                             end
                           False]
              end
          end
      end
  end.

Define foldr2 
  : Fun(S A : type)(acc : Fun(s : S)(a : A). S)(init : S)(l : <list2 A>). S
:=
  fun foldr2(S A : type)(acc : Fun(s : S)(a : A). S)(s : S)(l : <list2 A>):S.
  match l with
  | nil2 _ => 
    s
  | cons2 _ a' l' =>
    let s' = (acc s a') in
    (foldr2 S A acc s' l') 
  end.

Define ormap :=
  fun(l : <list2 bool>).
  (foldr2 bool bool or ff l).

Define eqnatEq3 : Forall(n:nat)(u:{(eqnat n Z) = tt}). { n = Z } :=
  foralli(n: nat)(u:{(eqnat n Z) = tt}).
  unjoin u with
  | foralli(p4 : { n = Z }).
    p4
  end.

Define letFunc :=
  fun (x : bool).
  let x = (or x x) in
  one.

Define letProof1
  : Forall(x:bool)(u: { (letFunc x) = two }). { Z = one }
:=
  foralli(x:bool)(u: { (letFunc x) = two }).
  unjoin u contra { Z = one }.

Define letIdentity :=
  fun(x : bool).
  let y = (or ff x) in
  y.

Define letIdProof
  : Forall(x:bool)(u: { (letIdentity x) = tt }). { x = tt }
:=
  foralli(x:bool)(u: { (letIdentity x) = tt }).
  unjoin u with
  | foralli(u : { x = tt }).
    u
  end.

Define matchAbbrev :=
  fun(x : nat)(y : bool).
  match x with
  | Z =>
    tt
  | S n' =>
    abbrev z = (and y tt) in
    z
  end.

Define matchAbbrevProof
  : Forall(x : nat)(y: bool)(u1 : { (matchAbbrev x y) = tt })
          (x' : nat)(u2 : { x = (S x')}). { y = tt }
:=
  foralli(x : nat)(y: bool)(u1 : { (matchAbbrev x y) = tt })
         (x' : nat)(u2 : { x = (S x')}).
  lemma u2 in
  unjoin u1 with
  | foralli(p0 : { (and y tt) = tt }).
    unjoin p0 with
    | foralli(u : {y = tt}).
      u
    end
  end.

Define testMult :=
  fun(x : nat).
  (mult x one).

Define funnyId :=
  fun(x : nat).
  match x with
  | Z =>
    x
  | S x' =>
    x
  end.

Define funnyIdProof
  : Forall(x x': nat)(u : { x = (S x') })(u' : { (funnyId x) = two } ). { x = two }
:=
  foralli(x x': nat)(u : { x = (S x') })(u' : { (funnyId x) = two } ).
  lemma u in
  unjoin u' with
  | foralli(u : { x = two }).
    u
  end.

Define badSub :=
  fun(x : nat).
  x.

Define badSubTotal 
  : Forall(x:nat). Exists(y: nat). { (badSub x) = y }
:=
  foralli(x:nat).
  existsi x
          { (badSub x) = * } 
          join (badSub x) x.

Total badSub badSubTotal.

Define badSubProof 
  : Forall(x : nat)(x' : nat)(u : { x = (S x') }). { (badSub x) = x }
:=
  foralli(x : nat)(x' : nat)(u : { x = (S x') }).
  case (badSub x) by u' ign with
  | Z =>
    lemma u in
    unjoin u' contra { (badSub x) = x }
  | S z =>
    lemma u in
    unjoin u' with
    | foralli(u'' : { x = (S z) }).
      hypjoin (badSub x) x by
        : { x = (S z) } u''
        : { (badSub x) = (S z) } u' 
      end
    end
  end.  

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

Define lt_Z2 : Forall(a:nat).{ (lt a Z) = ff } :=
  foralli(a : nat).
  case (lt a Z) by v ign with
  | ff =>
    v
  | tt =>
    unjoin v contra { (lt a Z) = ff }
  end.

 
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


%- well... it helped with the first case at least.
and only a case split on the vector was necessary here.
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
  foralli(A: type).
  induction (n : nat) return
    Forall(v: <vec A n>)(m:nat)(u: { (lt m n) = tt } )(a: A).
    { (vec_get v m) = (vec_get (vecc a v) (S m)) }
  with
    | Z =>
      foralli(v: <vec A n>)(m:nat)(u: { (lt m n) = tt } )(a: A).
      lemma n_eq in
      unjoin u contra { (vec_get v m) = (vec_get (vecc a v) (S m)) }
    | S n' =>
      foralli(v: <vec A n>)(m:nat)(u: { (lt m n) = tt } )(a: A).
      lemma n_eq in
      unjoin u with
      | foralli(p2 : { m = Z }).
        hypjoin (vec_get v m) (vec_get (vecc a v) (S m)) by
          : { m = Z } p2
        end
      | foralli(m0 : nat)(p3 : { m = (S m0) })(u : { (lt m0 n') = tt }).
        [n_IH n' 
      end
  end.  
  -%

Define null_terminated_nth_tail_implies_lt2 :
  Forall(n:nat)(c:<vec ulit n>)
				(i:nat)
				(u:{ (null_terminated (vec_nth_tail c i)) = tt })
    .{ (lt i n) = tt }
  :=
	foralli(n:nat)(c:<vec ulit n>)
				 (i:nat)
				 (u:{ (null_terminated (vec_nth_tail c i)) = tt })
	.
	case (lt i n) by q1 _ with
    | ff =>
			lemma q1 in
      unjoin u contra { (lt i n) = tt }
	| tt => q1
	end.

Classify eqnatNeq2. 