
Include "../lib/nat.g"
Include "../lib/bool.g"
Include "../lib/minus.g"
Include "../lib/vec.g"
Include "../lib/minmax.g"

  
Inductive list2 : Fun(A:type).type :=
  | nil2 : Fun(A:type).<list2 A>
  | cons2 : Fun(A:type)(a:A)(l:<list2 A>). <list2 A>.

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
%-
Define list_setmember2 
	: Forall(A:type)(a:A)
			  (eqA:Fun(^#owned x y: A).bool)
			  (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
        (u:{ (eqA a a) = tt })
        (l'' l':<list A>).
    { (member a (append l' (cons a l'')) eqA) = tt }
:=
  foralli(A:type)(a:A)(eqA:Fun(^ #owned x y: A).bool)
         (eqA_total:Forall(a b: A).Exists(z:bool).{ (eqA a b) = z })
         (u: {(eqA a a) = tt})(l'' l':<list A>).
  abbrev eqA = terminates eqA by eqA_total in
  case (member A a (append A l' (cons A a l'')) eqA) by v ign with
  | ff =>
    lemma u in
    unjoin v with
    | foralli(p0 : { (append l' (cons a l'')) = nil }).
      unjoin p0 with
      
      | (l'0 : type)(l'1 : l'0)(l'2 : <list l'0>)(p0 : { l' = (cons l'1 l'2) })
        (u : { (append_h (inspect mk_append_i) l'1 (foldr (clone_owned (inspect mk_append_i)) append_h (cons a l'') l'2)) = nil }) =>


      %-
      %%
      %% INTERESTING POINT - PARTIAL APPLICATION USED TO CREATE A FUNCTION
      %% DOES NOT HANDLE WELL. NUEVAL 
      %%
      %%
      | foralli(l'0 : type)(l'1 : l'0)(l'2 : <list l'0>)
               (p0 : { l' = (cons l'1 l'2) })
               (u : { (fun(^ #owned cookie)(^ #owned x)(l) :  !. match cookie by cookie_eq cookie_Eq return <list A> with mk_append_i => (cons (inc_owned x) l) end mk_append_i l'1 (fun foldr(^ #owned cookie)(fcn)(b)(^ #owned l) :  !. match l by l_eq l_Eq return B with nil => b | cons a' l' => (fcn cookie a' (foldr (clone_owned cookie) fcn b l')) end (clone_owned mk_append_i) fun(^ #owned cookie)(^ #owned x)(l) :  !. match cookie by cookie_eq cookie_Eq return <list A> with mk_append_i => (cons (inc_owned x) l) end (cons a l'') l'2)) = nil })
      -%

      end

    | foralli(c0 : type)(c1 : c0)(c2 : <list c0>)
             (p0 : { (append l' (cons a l'')) = (cons c1 c2) })
             (u : { (or (eqA (clone_owned a) c1) (member a c2 eqA)) = ff }).
      truei
    end
    
  | tt =>
    v
  end
-%


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



%
% MOAR PROOOFS
%
%  

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
  

%- this doesn't work because we are not (yet) able to use inequalities as lemmas.

Define neqEqnat2 : Forall(n m : nat)(u:{n != m}).{ (eqnat n m) = ff } :=
  foralli(n m : nat)(u:{n != m}).
  case (eqnat n m) by v ign with
  | ff =>
    v
  | tt =>
    lemma u in
    unjoin v contra { (eqnat n m) = ff } 
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
%-
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
      | foralli(p0 : { (lt b a) = ff })(u : { (eqnat b a) = tt }).
        hypjoin (lt (minus a b) a) tt by
          : { b = a } [eqnatEq b a u]
          : { (minus b b) = Z } [x_minus_x b]
          : { b = (S b') } b_eq
        end
      | foralli(p1 : { (lt b a) = tt }).

        % yeah -- this doesn't seem to help. I blame the lack
        % of theorems in the minus library.
        lemma
          : { (lt b' a) = tt }
             [ltlt_trans b' b a b'_lt_b p1]
          
          : { (le b' a) = tt }   
            [lt_implies_le b' a ##]

          : { (lt (S (minus a (S b'))) a) = tt }
            hypjoin (lt (minus a b) a) tt by
              : { (minus a b') = (S (minus a (S b'))) } [minusS2 b' a ##]
              : { b = (S b') } ##
              : { (lt (minus a b') a) = tt } [b_IH b' b'_le_a z_lt_b']
        in
        -%
      end %u1
  end %ind
-%

Define vec_append_assoc2 : Forall(A:type)(n1 : nat)(l1 : <vec A n1>)
                      (n2 n3 : nat)(l2 : <vec A n2>)(l3 : <vec A n3>).
                      { (vec_append (vec_append l1 l2) l3) =
                        (vec_append l1 (vec_append l2 l3)) } :=
  foralli(A:type).
  induction(n1:nat)(l1:<vec A n1>) return 
    Forall(n2 n3 : nat)(l2 : <vec A n2>)(l3 : <vec A n3>).
    { (vec_append (vec_append l1 l2) l3) = (vec_append l1 (vec_append l2 l3)) } 
  with
   | vecn A' => 
     foralli(n2 n3 : nat)(l2 : <vec A n2>)(l3 : <vec A n3>). 
     hypjoin (vec_append (vec_append l1 l2) l3) (vec_append l1 (vec_append l2 l3)) by
       : { l1 = (vecn A') } l1_eq
     end
   | vecc A' n1' x' l1' => 
     foralli(n2 n3 : nat)(l2 : <vec A n2>)(l3 : <vec A n3>).
     hypjoin (vec_append (vec_append l1 l2) l3) (vec_append l1 (vec_append l2 l3)) by
      : { (vec_append (vec_append l1' l2) l3) = (vec_append l1' (vec_append l2 l3)) }
        [l1_IH n1' l1' n2 n3 l2 l3]
      : { l1 = (vecc x' l1') }
        l1_eq
     end
  end.

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


      %-
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
      -%
  end.  
  -%

Classify eqnatNeq2. 