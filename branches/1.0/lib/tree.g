Include "pow.g".

Inductive tree : Fun(A:type)(h:nat).type :=
	leaf : Fun ( A : type).<tree A Z>
	| node : Fun ( A : type)(h:nat)(a: A)
		(left: <tree A h>)
		(right: <tree A h>).
		<tree A (S h)>.

Define tree_leaves : Fun(A : type)(h : nat)(t : <tree A h>).nat :=
	fun tree_leaves(A : type)(h : nat)(t : <tree A h>) : nat.
		match t by x y return nat with
		leaf A' => (S Z)
		|  node A' h' a' l' r' => (plus (tree_leaves A' h' l') (tree_leaves A' h' r'))
	end.

Define tree_leaf_lemma : Forall (A : type)(h : nat)(t : <tree A h>). {(tree_leaves ! h t) = (pow two h)} :=
	foralli(A : type).induction (h : nat)( t : <tree A h>) by x1 x2 IH return {(tree_leaves ! h t) = (pow two h)} with
	leaf A' => trans cong (tree_leaves ! h *) x1
		trans join (tree_leaves ! h (leaf !)) one
		trans join one (pow two Z)
		cong (pow two *) symm inj <tree ** *> x2
	| node A' h' a' l' r' => 
		trans cong (tree_leaves ! * t) inj <tree ** *> x2
		trans cong (tree_leaves ! (S h') *) x1
		trans join (tree_leaves ! (S h') (node ! h' a' l' r')) (plus (tree_leaves ! h' l') (tree_leaves ! h' r'))
        	trans cong (plus * (tree_leaves ! h' r')) [IH h' cast l' by cong <tree * h'> symm inj <tree * **> x2 ]
		trans cong (plus (pow two h') *) [IH h' cast r' by cong <tree * h'> symm inj <tree * **> x2 ]
		trans [2_pow_add h']
		cong (pow two *) symm inj <tree ** *> x2
	end.
	
Define tree_size : Fun(A : type)(h : nat)(t : <tree A h>).nat :=
	fun tree_size(A : type)(h : nat)(t : <tree A h>) : nat.
		match t by x y return nat with
		leaf A' => one
		|  node A' h' a' left' right' => (plus one (plus (tree_size A' h' left') (tree_size A' h' right')))
	end.


Define tree_size_helper : Forall(x:nat)(u:{x != Z}).{(P (plus x x)) != Z} :=
	induction(x:nat) by x1 x2 IH return Forall(u:{x != Z}).{(P (plus x x)) != Z} with
	Z =>	foralli(u:{x != Z}).
		 contra trans symm x1 u
		 	{(P (plus x x)) != Z}
	|S x' => foralli(u:{x != Z}).
		trans cong (P (plus * *)) x1
		trans join (P (plus (S x') (S x'))) (P (S (plus x' (S x'))))
		existse [plus_total (S x') x'] foralli(z:nat)(v:{ (plus x' (S x')) = z}).
		trans cong (P (S *)) v 
		trans [PS_lemma z]
		trans symm v
		trans [plusS x' x']
		existse [plus_total x' x'] foralli(q:nat)(r:{(plus x' x') = q}).
		trans cong (S *) r
		[S_not_zero q]
	end.

		
Define tree_size_lemma : Forall (A : type)(h : nat)(t : <tree A h>). {(tree_size ! h t) = (P (pow two (S h)))} :=
	foralli(A : type).induction (h : nat)( t : <tree A h>) by x1 x2 IH return {(tree_size ! h t) = (P (pow two (S h)))} with
	leaf A' => trans cong (tree_size ! h *) x1
		trans join (tree_size ! h (leaf !)) one
		trans symm [PS_lemma one]
		trans cong (P *) symm [first_power two]
		cong (P (pow two (S *))) symm inj <tree ** *> x2
	| node A' h' a' l' r' => 
		trans cong (tree_size ! * t) inj <tree ** *> x2
		trans cong (tree_size ! (S h') *) x1
		trans join (tree_size ! (S h') (node ! h' a' l' r')) (plus one (plus (tree_size ! h' l') (tree_size ! h' r')))
		trans cong (plus one (plus * (tree_size ! h' r'))) [IH h' cast l' by cong <tree * h'> symm inj <tree * **> x2]
		trans cong (plus one (plus (P (pow (S (S Z))(S h'))) *)) [IH h' cast r' by cong <tree * h'> symm inj <tree * **> x2]
		existse [pow_total two (S h')] foralli(z:nat)(u:{(pow two (S h')) = z}).
		trans cong (plus one (plus (P *) (P *))) u
		trans cong (plus one *) [P_add z trans symm u [pow_not_zero two (S h') clash two Z]]
		trans join (plus one (P (P (plus z z)))) (S (P (P (plus z z))))
		existse [plus_total z z] foralli(q:nat)(r:{(plus z z) = q}).
		trans cong (S (P (P *))) r
		existse [P_total q trans symm r [plus_not_zero z z trans symm u [pow_not_zero two (S h') clash two Z]]] foralli(y:nat)(i:{(P q) = y}).
		trans cong (S (P *)) i
		trans [PS_lemma2 y trans symm i trans cong (P *) symm r [tree_size_helper z trans symm u [pow_not_zero two (S h') clash two Z]]]
		trans symm i
		trans cong (P *) symm r
		trans cong (P (plus * *)) symm u 
		trans cong (P *) [2_pow_add (S h')]
		cong (P (pow two (S *))) symm inj <tree ** *> x2
		
	end.
	