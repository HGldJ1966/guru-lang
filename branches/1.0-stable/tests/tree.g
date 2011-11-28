Set "print_parsed".

Inductive nat : type :=
  Z : nat
| S : Fun(x:nat).nat.

Define plus :=
  fun plus(n m : nat) : nat.
    match n return nat with
      Z => m
    | S n' => (S (plus n' m))
    end.
        
Define plusZ : Forall(n:nat). { (plus n Z) = n } :=
  induction(n:nat) by x1 x2 IH return { (plus n Z) = n } with
    Z => trans cong (plus * Z) x1
         trans join (plus Z Z) Z
               symm x1
  | S n' => trans cong (plus * Z) x1
            trans join (plus (S n') Z) (S (plus n' Z))
            trans cong (S *) [IH n']
                  symm x1
  end.    

Define plusS : Forall(n m : nat). { (plus n (S m)) = (S (plus n m))} :=
	induction (n:nat) by x1 x2 IH return Forall(m:nat).{ (plus n (S m)) = (S (plus n m))} with
		Z => foralli(m : nat).
		     trans cong (plus * (S m)) x1
		     trans join (plus Z (S m)) (S m)
		     trans join (S m) (S (plus Z m))
		     cong (S (plus * m)) symm x1
		| S n' => foralli(m : nat). 
			trans cong (plus * (S m)) x1
			trans join (plus (S n') (S m)) (S (plus n' (S m)))
			trans cong (S *) [IH n' m]
			trans join (S (S (plus n' m))) (S (plus (S n') m))
			cong (S (plus * m)) symm x1
	end.   

Define plus_comm : Forall (n m :nat). { (plus n m) = (plus m n) } :=
	induction (n : nat) by x1 x2 IH return Forall(m : nat).{ (plus n m) = (plus m n) } with
		Z => foralli(m : nat).
			trans cong (plus * m) x1
			trans join (plus Z m) m
			trans cong * symm [plusZ m]
			cong (plus m *) symm x1
		|S n' => foralli(m : nat).
			trans cong (plus * m) x1
			trans join (plus (S n') m) (S (plus n' m))
			trans cong (S *)  [IH n' m]
			trans cong * symm [plusS m n']
			cong (plus m *) symm x1
	end. 	
	  
Define plus_assoc : Forall(x y z:nat). { (plus (plus x y) z) = (plus x (plus y z)) } :=
  induction(x:nat) by x1 x2 IH return 
                   Forall(y z : nat). 
                     { (plus (plus x y) z) = (plus x (plus y z)) }
  with
    Z => foralli(y z : nat). 
         trans cong (plus (plus * y) z) x1
         trans join (plus (plus Z y) z) (plus y z)
         trans symm join (plus Z (plus y z)) (plus y z)
               cong (plus * (plus y z)) symm x1
  | S x' => foralli(y z : nat). 
            trans cong (plus (plus * y) z) x1
            trans join (plus (plus (S x') y) z) (S (plus (plus x' y) z))
            trans cong (S *) [IH x' y z]
            trans symm join (plus (S x') (plus y z)) (S (plus x' (plus y z)))
                  cong (plus * (plus y z)) symm x1
end.  


Define plus_total : Forall ( y  x : nat). Exists(z:nat).{(plus x y) = z} :=
	foralli(y:nat).induction (x : nat) by x1 x2 IH return Exists(z:nat).{(plus x y) = z} with
	Z => 	
		existsi y {(plus x y) = *}
		trans cong (plus * y) x1
		join (plus Z y) y
	| S x' =>  
		existse [IH x'] foralli(z':nat)(u:{(plus x' y) = z'}). 
		existsi (S z') {(plus x y) = *}  
			% plus x y = (S z')
			 trans cong (plus * y) x1
				trans join (plus (S x') y) (S (plus x' y))
				cong (S *) u			
	end. 

Define mult : Fun(n m : nat). nat :=
   rec(mult : Fun(n m : nat).nat).
   fun (n m : nat).
   	match m by x y return nat with
		Z => Z
		| S m' => (plus (mult n m') n)  
   	end.
	
Define mult_by_one : Forall ( n : nat). { (mult n (S Z)) = n} :=
	induction( n:nat) by x1 x2 IH return { (mult n (S Z)) = n} with
	Z => trans cong (mult * (S Z)) x1
	     trans join (mult Z (S Z)) (plus (mult Z Z) Z)
	     trans join (plus (mult Z Z) Z) (plus Z Z)
	     trans join (plus Z Z) Z
	     symm x1
	| S n' => trans cong (mult * (S Z)) x1
		trans join (mult (S n') (S Z)) (plus (mult (S n') Z) (S n'))
		trans join (plus (mult (S n') Z) (S n')) (plus Z (S n'))
		trans join (plus Z (S n')) (S n')
		symm x1
	end. 

Define  multiple_by_one2 : Forall(n:nat). { (mult (S Z) n) = n } :=
	induction (n:nat) by x1 x2 IH return { (mult (S Z) n) = n } with
	Z => trans cong (mult (S Z) *) x1
	     trans join (mult (S Z) Z) Z
	     symm x1
	| S n' =>  trans cong (mult (S Z) *) x1
		trans join (mult (S Z) (S n')) (plus (mult (S Z) n') (S Z))
		trans cong (plus * (S Z)) [IH n']
		trans [plusS n' Z]
		trans cong (S *) [plusZ n']
		symm x1
	end.

Define	zero_times_anything : Forall (n:nat).{ (mult Z n) = Z } :=
	induction (n:nat) by x1 x2 IH return { (mult Z n) = Z } with
	Z => trans cong (mult Z *) x1
	     join (mult Z Z) Z
	| S n' => trans cong (mult Z *) x1
		  trans join (mult Z (S n')) (plus (mult Z n') Z)
		  trans cong (plus * Z) [IH n']
		  join	(plus Z Z) Z
	end.

	
	
Define mult_total : Forall (x y :nat).Exists(z:nat).{(mult x y) = z} :=
	foralli(x:nat).induction (y:nat) by x1 x2 IH return Exists(z:nat).{(mult x y) = z}	with
	Z => 	existsi Z {(mult x y) = *}
		trans cong (mult x *) x1
		join (mult x Z) Z
	|S y' =>  
		existse [IH y'] foralli(z':nat)(u:{(mult x y') = z'}).
		existse [plus_total x z'] foralli(z:nat)(u':{(plus z' x) = z}).
			existsi z
			{(mult x y) = *} 
			trans cong (mult x *) x1
			trans join (mult x (S y')) (plus (mult x y') x)
			trans cong (plus * x) u
			u'
	end.

Define mult_dist : Forall(z x y :nat).{(mult x (plus y z)) = (plus (mult x y) (mult x z))} :=
	induction (z:nat) by x1 x2 IH return Forall(x y:nat).{(mult x (plus y z)) = (plus (mult x y) (mult x z))} with
	Z => foralli(x y : nat).
		 trans cong (mult x (plus y *)) x1
		 trans cong (mult x *) [plusZ y]
		 trans join (mult x y) (plus Z (mult x y))
		 trans join (plus Z (mult x y)) (plus (mult x Z) (mult x y))
		 trans cong (plus (mult x *) (mult x y)) symm x1
		 existse [mult_total x z] foralli(a:nat)(u:{(mult x z) = a}).
		 existse [mult_total x y] foralli(b:nat)(u':{(mult x y) = b}).
		 trans cong (plus * (mult x y)) u
		 trans cong (plus a *) u'
		 trans [plus_comm a b]
		 trans cong (plus b *) symm u
		 cong (plus * (mult x z)) symm u'
		 
	| S z' => foralli(x y : nat).
		trans cong (mult x (plus y *)) x1
		trans cong (mult x *) [plusS y z']
		existse [plus_total z' y] foralli(a:nat)(u:{(plus y z')=a}).
		trans cong (mult x (S *)) u
		trans join (mult x (S a)) (plus (mult x a) x)
		trans cong (plus (mult x *) x) symm u
		trans cong (plus * x) [IH z' x y]
		existse [mult_total x z'] foralli(b:nat)(u':{(mult x z') = b}).
		existse [mult_total x y] foralli(c:nat)(u'':{(mult x y) = c}).
		trans cong (plus (plus * (mult x z')) x) u''
		trans cong (plus (plus c *) x) u'
		trans [plus_assoc c b x]
		trans cong (plus c (plus * x)) symm u'
		trans join (plus c (plus (mult x z') x)) (plus c (mult x (S z')))
		trans cong (plus c (mult x *)) symm x1
		cong (plus * (mult x z)) symm u''
	end.

Define mult_dist_2 : Forall(x y z:nat).{(mult (plus y z) x) = (plus (mult y x) (mult z x))} :=
	induction (x:nat) by x1 x2 IH return Forall(y z:nat).{(mult (plus y z) x) = (plus (mult y x) (mult z x))} with
	Z => foralli(y z : nat).	
			trans cong (mult (plus y z) *) x1
			trans join (mult (plus y z) Z) Z
			trans join Z (plus Z Z)
			trans join (plus Z Z) (plus (mult y Z) Z)
			trans join (plus (mult y Z) Z) (plus (mult y Z) (mult z Z))
			cong (plus (mult y *) (mult z *)) symm x1			
	| S x' => foralli(y z : nat).
		trans cong (mult (plus y z) *) x1
		trans join (mult (plus y z) (S x')) (plus (mult (plus y z) x') (plus y z))
		trans cong (plus * (plus y z)) [IH x' y z]
		existse [mult_total y x'] foralli(a:nat)(a':{(mult y x') = a}).
		trans cong (plus (plus * (mult z x')) (plus y z)) a'
		existse [mult_total z x'] foralli(b:nat)(b':{(mult z x') = b}).
		trans cong (plus (plus a *) (plus y z)) b'
		existse [plus_total b a] foralli(c:nat)(c':{(plus a b) = c}).
		trans cong (plus * (plus y z)) c'
		trans symm [plus_assoc c y z]
		trans cong (plus (plus * y) z) symm c'
		trans cong (plus (plus * y) z) symm [plus_comm b a]
		trans cong (plus * z) [plus_assoc b a y]
		trans cong (plus (plus b (plus * y)) z) symm a'
		trans join (plus (plus b (plus (mult y x') y)) z) (plus (plus b (mult y (S x'))) z)
		trans cong (plus (plus b (mult y *)) z) symm x1
		existse [mult_total y x] foralli(d:nat)(d':{(mult y x) = d}).
		trans cong (plus (plus b *) z) d'
		trans cong (plus * z) [plus_comm b d]
		trans [plus_assoc d b z]
		trans cong (plus d (plus * z)) symm b'
		trans join (plus d (plus (mult z x') z)) (plus d (mult z (S x')))
		trans cong (plus d (mult z *)) symm x1
		cong (plus * (mult z x)) symm d'
	end.
			 
Define mult_comm : Forall(m n :nat).{(mult n m) = (mult m n)} :=
	induction (m:nat) by x1 x2 IH return Forall(n:nat).{(mult n m) = (mult m n)} with
	Z => foralli(n : nat). 
		trans cong (mult n *) x1
		trans join (mult n Z) Z
		trans symm [zero_times_anything n]
		cong (mult * n) symm x1
	| S m' => foralli(n : nat).
		trans cong (mult n *) x1
		trans join (mult n (S m')) (plus (mult n m') n)
		trans cong (plus (mult n m') *) symm [multiple_by_one2 n]  
		trans cong (plus * (mult (S Z) n)) [IH m' n]
		trans symm [mult_dist_2 n m' (S Z)]
		trans cong (mult * n) [plusS m' Z]
		trans cong (mult (S *) n) [plusZ m']
		cong (mult * n) symm x1
	end.	

Define mult_assoc : Forall(m n p: nat).{(mult (mult m n) p) = (mult m (mult n p))} :=
	foralli(m n:nat).induction(p:nat) by x1 x2 IH return {(mult (mult m n) p) = (mult m (mult n p))} with
	Z => trans cong (mult (mult m n) *) x1
	     trans join (mult (mult m n) Z) Z
	     trans join Z (mult m Z)
	     trans join (mult m Z) (mult m (mult n Z))
	     cong (mult m (mult n *)) symm x1
	| S p' => trans cong (mult (mult m n) *) x1
		existse [mult_total m n] foralli(a:nat)(a':{(mult m n) = a}).
		trans cong (mult * (S p')) a'
		trans join (mult a (S p')) (plus (mult a p') a)
		trans cong (plus (mult * p') a) symm a'
		trans cong (plus * a) [IH p']
		trans cong (plus (mult m (mult n p')) *) symm a'
		existse [mult_total n p'] foralli(b:nat)(b':{(mult n p') = b}).
		trans cong (plus (mult m *) (mult m n)) b'
		trans symm [mult_dist n m b]
		trans cong (mult m (plus * n)) symm b'
		trans join (mult m (plus (mult n p') n)) (mult m (mult n (S p')))
		cong (mult m (mult n *)) symm x1
	end.
	
Define pow : Fun(base exp : nat). nat :=
   rec(pow : Fun(base exp : nat).nat).
   fun (base exp : nat).
   	match exp by x y return nat with
		Z => (S Z)
		| S exp' => (mult base (pow base exp'))
	end.  

Define first_power : Forall ( x : nat).{ (pow x (S Z)) = x} :=
	induction (x :nat) by x1 x2 IH return 	{ (pow x (S Z)) = x} with
	Z => trans cong (pow * (S Z)) x1
		trans join (pow Z (S Z)) (mult Z (pow Z Z))
		trans join (mult Z (pow Z Z)) (mult Z (S Z))
		trans [mult_comm (S Z) Z]	
		trans join (mult (S Z) Z) Z
		symm x1
	|S x' => trans cong (pow * (S Z)) x1
		trans join (pow (S x') (S Z)) (mult (S x') (pow (S x') Z))
		trans join (mult (S x') (pow (S x') Z)) (mult (S x') (S Z))
		trans [mult_by_one (S x')]
		symm x1
	end.
		
Define one : nat := (S Z).	
Define two : nat := (S (S Z)).	

Define pow_total : Forall(b e : nat).Exists(z:nat).{(pow b e) = z} :=
	foralli(b:nat).induction(e:nat) by x1 x2 IH return Exists(z:nat).{(pow b e) = z} with
	Z => existsi one {(pow b e) = *}
		trans cong (pow b *) x1
		join (pow b Z) one
	| S e' => existse [IH e'] foralli(z':nat)(u:{(pow b e') = z'}).
		existse [mult_total b z'] foralli(z:nat)(u':{(mult b z') = z}).
		existsi z {(pow b e) = *}
		trans cong (pow b *) x1
		trans join (pow b (S e')) (mult b (pow b e'))
		trans cong (mult b *) u
		u'
	end.

Define pow_mult : Forall(y b x:nat). { (mult (pow b x) (pow b y)) = (pow b (plus x y))} :=
	foralli(y b :nat).induction (x:nat) by x1 x2 IH return { (mult (pow b x) (pow b y)) = (pow b (plus x y))} with
	Z =>  trans cong (mult (pow b *) (pow b y)) x1
	      trans join (mult (pow b Z) (pow b y)) (mult one (pow b y))
	      existse [pow_total b y] foralli(a:nat)(a':{(pow b y) = a}).
	      trans cong (mult one *) a'
	      trans [multiple_by_one2 a]
	      trans symm a'
	      trans join (pow b y) (pow b (plus Z y))
	      cong (pow b (plus * y)) symm x1
	| S x' => trans cong (mult (pow b *) (pow b y)) x1
		trans join (mult (pow b (S x')) (pow b y)) (mult (mult b (pow b x')) (pow b y))
		existse [pow_total b x'] foralli(f:nat)(f':{(pow b x') = f}).
		existse [pow_total b y] foralli(g:nat)(g':{(pow b y) = g}).
		trans cong (mult (mult b *) (pow b y)) f'
		trans cong (mult (mult b f) *) g'
		trans [mult_assoc b f g]
		trans cong (mult b (mult * g)) symm f'
		trans cong (mult b (mult (pow b x') *)) symm g'
		trans cong (mult b *) [IH x']
		trans join (mult b (pow b (plus x' y))) (pow b (S (plus x' y)))
		trans join (pow b (S (plus x' y))) (pow b (plus (S x') y))
		cong (pow b (plus * y)) symm x1
	end.

	
Define 2_pow_add : Forall (e : nat).{(plus (pow two e) (pow two e)) = (pow two (S e))} :=
	induction (e : nat) by x1 x2 IH return {(plus (pow two e) (pow two e)) = (pow two (S e))} with
	Z => trans cong (plus (pow two *) (pow two *)) x1
		trans join (plus (pow two Z) (pow two Z)) (plus (S Z) (S Z)) 
		trans join (plus (S Z) (S Z)) two
		trans symm [first_power two]
		cong (pow two (S *)) symm x1
	| S e' => trans cong (plus (pow two *) (pow two *)) x1
		trans join (plus (pow two (S e')) (pow two (S e'))) (plus (mult two (pow two e')) (mult two (pow two e')))
		existse [pow_total two e'] foralli(a:nat)(a':{(pow two e') = a}).
		trans cong (plus (mult two *) (mult two *)) a'
		trans symm [mult_dist a two a]
		trans cong  (mult two (plus * *)) symm a'
		trans cong  (mult two *) [IH e']
		trans cong (mult * (pow two (S e'))) symm [first_power two]
		trans [pow_mult (S e') two one]
		trans cong (pow two *) symm [plus_comm (S e') (S Z)]
		trans cong (pow two (plus * (S Z))) symm x1
		trans cong (pow two *) [plusS e Z]
		cong (pow two (S *)) [plusZ e]
	end.
	
Inductive tree : Fun(A:type)(h:nat).type :=
	leaf : Fun ( A : type).<tree A Z>
	| node : Fun ( A : type)(h:nat)(a: A)
		(left: <tree A h>)
		(right: <tree A h>).
		<tree A (S h)>.

Define tree_leaves : Fun(A : type)(h : nat)(t : <tree A h>).nat :=
	rec(tree_leaves : Fun(A : type)(h : nat)(t : <tree A h>).nat).
	fun(A : type)(h : nat)(t : <tree A h>).
		match t by x y return nat with
		leaf A' => (S Z)
		|  node A' h' a' l' r' => (plus (tree_leaves A' h' l') (tree_leaves A' h' r'))
	end.



Define tree_leaf_lemma : Forall (A : type)(h : nat)(t : <tree A h>). {(tree_leaves ! h t) = (pow (S (S Z)) h)} :=
	foralli(A : type).induction (h : nat)( t : <tree A h>) by x1 x2 IH return {(tree_leaves ! h t) = (pow (S (S Z)) h)} with
	leaf A' => trans cong (tree_leaves ! h *) x1
		trans join (tree_leaves ! h (leaf !)) (S Z)
		trans join (S Z) (pow (S (S Z)) Z)
		cong (pow (S (S Z)) *) symm inj <tree ** *> x2
	| node A' h' a' l' r' => 
		trans cong (tree_leaves ! * t) inj <tree ** *> x2
		trans cong (tree_leaves ! (S h') *) x1
		trans join (tree_leaves ! (S h') (node ! h' a' l' r')) (plus (tree_leaves ! h' l') (tree_leaves ! h' r'))
        	trans cong (plus * (tree_leaves ! h' r')) [IH h' cast l' by cong <tree * h'> symm inj <tree * **> x2 ]
		trans cong (plus (pow two h') *) [IH h' cast r' by cong <tree * h'> symm inj <tree * **> x2 ]
		trans [2_pow_add h']
		cong (pow two *) symm inj <tree ** *> x2
	end.
	

Define P : Fun(n:nat).nat :=
	fun(n : nat).
	match n by x y return nat with
		Z => abort nat
		| S n' => n'
	end.
	
	
Define PS_lemma : Forall(n:nat).{ (P (S n)) = n } :=
	induction (n:nat) by x1 x2 IH return { (P (S n)) = n } with
	Z => trans cong (P (S *)) x1
		trans join (P (S Z)) Z
		symm x1
	| S n' => trans cong (P (S *)) x1
		trans join (P (S (S n'))) (S n')
		symm x1
	end.

Define PS_lemma2 : Forall(n:nat)(a:{n != Z}).{ (S (P n)) = n } :=
	induction(n:nat) by x1 x2 IH return Forall(a:{n != Z}).{ (S (P n)) = n } with
	Z => foralli(a:{n != Z}).
		contra trans symm x1 a
			{ (S (P n)) = (P (S n)) }
	| S n' => foralli(a:{n != Z}).
			trans cong (S (P *)) x1
			trans join (S (P (S n'))) (S n')
			symm x1
	end.			
	
Define P_add_lemma : Forall(x:nat)(y:nat)(a:{x != Z})(b:{y != Z}). {(plus (P x) (P y)) = (P (P (plus x y)))} := 	
	foralli(x:nat).induction(y:nat) by x1 x2 IH return Forall(a:{x != Z})(b:{y != Z}). {(plus (P x) (P y)) = (P (P (plus x y)))} with
	Z => foralli(a:{x != Z}).
		foralli(b:{y != Z}).
			contra trans symm x1 b
				 {(plus (P x) (P y)) = (P (P (plus x y)))}
	| S y' => foralli(a:{x != Z}).
		foralli(b:{y != Z}). 
		trans cong (plus (P x) (P *)) x1
		cong (plus (P x) *) [PS_lemma y']
		
	end.
	

Define tree_size : Fun(A : type)(h : nat)(t : <tree A h>).nat :=
	rec(tree_size : Fun(A : type)(h : nat)(t : <tree A h>).nat).
	fun(A : type)(h : nat)(t : <tree A h>).
		match t by x y return nat with
		leaf A' => one
		|  node A' h' a' left' right' => (plus one (plus (tree_size A' h' left') (tree_size A' h' right')))
	end.
	
Define tree_size_lemma : Forall (A : type)(h : nat)(t : <tree A h>). {(tree_size ! h t) = (P (pow (S (S Z)) (S h)))} :=
	foralli(A : type).induction (h : nat)( t : <tree A h>) by x1 x2 IH return {(tree_size ! h t) = (P (pow (S (S Z)) (S h)))} with
	leaf A' => trans cong (tree_size ! h *) x1
		trans join (tree_size ! h (leaf !)) one
		trans symm [PS_lemma one]
		trans cong (P *) symm [first_power two]
		cong (P (pow (S (S Z)) (S *))) symm inj <tree ** *> x2
	| node A' h' a' l' r' => symm x1
	
	end.