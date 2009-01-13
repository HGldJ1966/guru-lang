Include "../lib/nat.g".
Include "../lib/minmax.g". 
%Set "print_parsed".


Inductive bst: Fun(A:type)(lb ub : nat).type :=
  leaf : Fun(A:type)(lb : nat)(ub : nat)(u:{(le lb ub) = tt}).<bst A lb ub>
| node : Fun(A:type)(lbl ubl : nat)(lbr ubr : nat)(key:nat)
            (u1 : { (le ubl key) = tt})
            (u2 : { (le key lbr) = tt})
            (data:A)(L : <bst A lbl ubl>)(R : <bst A lbr ubr>).
            <bst A lbl ubr>.

Define bst_prop1 : Forall(A:type)(lb ub: nat)(t: <bst A lb ub>). { (le lb ub) = tt} :=
	foralli(A:type).induction(lb ub : nat)(t:<bst A lb ub>) by x1 x2 IH return { (le lb ub) = tt} with
 	leaf A' lb' ub' u' => trans cong (le * ub) inj <bst ** * **> x2
			trans cong (le lb' *) inj <bst ** ** *> x2
			u'
	| node A' lbl' ubl' lbr' ubr' key' u1' u2' data' L' R' => 
			trans cong (le * ub) inj <bst ** * **> x2
			trans cong (le lbl' *) inj <bst ** ** *> x2
			[le_trans lbl' key' ubr' 
				[le_trans lbl' ubl' key' [IH lbl' ubl' cast L' by cong <bst * lbl' ubl'> symm inj <bst * ** **> x2] u1']
				[le_trans key' lbr' ubr' 
					u2' [IH lbr' ubr' cast R' by cong <bst * lbr' ubr'> symm inj <bst * ** **> x2] ]
			]
			
			
	end.	    
	    
Define bst_insert : Fun(A:type)(lb ub : nat)(t : <bst A lb ub>)(key:nat)(data:A).<bst A (min lb key) (max ub key)> :=
	fun bst_insert(A:type)(lb ub : nat)(t : <bst A lb ub>)(key:nat)(data:A) : <bst A (min lb key) (max ub key)> .
	match t by x1 y1 return <bst A (min lb key) (max ub key)> with
	leaf A' lb' ub' u' => (node 
			A
			(min lb key) (min lb key)
			(max ub key) (max ub key)
			key
			trans cong (le * key) symm [min_comm key lb] [min_le_lemma key lb]
			trans cong (le key *) symm [max_comm key ub] [max_le_lemma key ub]
			data
			(leaf A (min lb key) (min lb key)  [mins_lemma lb lb key [x_le_x lb]] )
			(leaf A (max ub key) (max ub key)  [maxs_lemma ub ub key [x_le_x ub]] ))
	| node A' lbl' ubl' lbr' ubr' key' u1' u2' data' L' R' => 
		match (eqnat key key') by x2 y2 return <bst A (min lb key) (max ub key)> with
		tt => (node A 
				(min lb key) ubl' 
				lbr'  (max ub key)
				key' u1' u2' data 
				cast L' by trans cong <bst * lbl' ubl'> symm inj <bst * ** **> y1 
					trans cong <bst A * ubl'> symm inj <bst ** * **> y1
					cong <bst A * ubl'>
					symm [min_le lb key
						trans cong (le * key) inj <bst ** * **> y1
						[le_trans lbl' ubl' key [bst_prop1 A' lbl' ubl' L'] trans cong (le ubl' *) [eqnatDef key key' x2] u1']]
				
				 cast R' by  trans cong <bst * lbr' ubr'> symm inj <bst * ** **> y1 
				 	trans cong <bst A lbr' *> symm inj <bst ** ** *> y1
					cong <bst A lbr' *>
						trans symm [max_le key ub
							trans cong (le key *) inj <bst ** ** *> y1
							[le_trans key lbr' ubr' trans cong (le * lbr') [eqnatDef key key' x2] u2' [bst_prop1 A' lbr' ubr' R']]]
						[max_comm key ub]
				 )
		|ff => match (lt key key') by x3 y3 return <bst A (min lb key) (max ub key)> with
			tt => (node A
				(min lb key) (max key ubl')
				lbr' (max ub key)
				key' 
				
				[le_max_lemma key ubl' key' [lt_implies_le key key' x3] u1']
				u2' cast data' by symm inj <bst * ** **> y1
				
				cast (bst_insert A lbl' ubl' 
					cast L' by cong <bst * lbl' ubl'> symm inj <bst * ** **> y1
					 key data) 
					 by trans cong <bst A (min * key) (max ubl' key)> symm inj <bst ** * **> y1
						cong <bst A (min lb key) *> [max_comm ubl' key]
					
				
				cast R' by trans cong <bst * lbr' ubr'> symm inj <bst * ** **> y1 
					cong <bst A lbr' *>
						%-proof of ubr' = (max ub key) -%
						trans symm [max_le key ubr' 
							[le_trans key lbr' ubr' 
								[le_trans key key' lbr' [lt_implies_le key key' x3] u2']
								[bst_prop1 A' lbr' ubr' R']]]
						trans [max_comm key ubr']
						cong (max * key) symm inj <bst ** ** *> y1	
					
				)
			| ff => (node A
					(min lb key) ubl'
					(min lbr' key) (max ub key)
					key'
					u1' 
					[le_min_lemma key' lbr' key u2' [lt_ff_implies_le key key' x3]]
					cast data' by symm inj <bst * ** **> y1
					
					cast L' by trans cong <bst * lbl' ubl'> symm inj <bst * ** **> y1
					cong <bst A * ubl'>
						%- proof of lbl' = (min lb key) -%
						trans symm [min_le lbl' key
							[le_trans lbl' key' key
								[le_trans lbl' ubl' key' [bst_prop1 A' lbl' ubl' L'] u1']
								[lt_ff_implies_le key key' x3]
							]]
						cong (min * key) symm inj <bst ** * **> y1 
					cast (bst_insert A lbr' ubr' cast R' by cong <bst * lbr' ubr'> symm inj <bst * ** **> y1 key data)
					by cong <bst A (min lbr' key) (max * key)> symm inj <bst ** ** *> y1
					
					) 
			end
		end
	end.
	

Define bst_search : Fun(A:type)(lb ub : nat)(t : <bst A lb ub>)(key:nat).A :=
	fun bst_search(A:type)(lb ub : nat)(t : <bst A lb ub>)(key:nat) : A.
	match t by x1 y1 return A with
	leaf A' lb' ub' u' => abort A
	| node A' lbl' ubl' lbr' ubr' key' u1' u2' data' L' R' =>
		match (eqnat key key') by x2 y2 return A with
		tt => cast data' by symm inj <bst * ** **> y1
		| ff => match (lt key key') by x3 y3 return A with
			tt => (bst_search A lbl' ubl' cast L' by cong <bst * lbl' ubl'> symm inj <bst * ** **> y1 key)
			| ff => (bst_search A lbr' ubr' cast R' by cong <bst * lbr' ubr'> symm inj <bst * ** **> y1 key)
			end
		end
	end.  




Inductive dsd : Fun(A:type)(olb:nat)(ub:nat).type :=
  mkdsd : Fun(A:type)(key:nat)(data:A)(olb ub : nat)(t:<bst A key ub>)(u:{(le olb key) = tt})(v:{(le key ub) = tt}).<dsd A olb ub>.
  	

Define dsdKey : Fun(A:type)(olb:nat)(ub:nat)(d:<dsd A olb ub>).nat :=
	fun dsdKey(A:type)(olb:nat)(ub:nat)(d:<dsd A olb ub>) : nat.
	match d by x1 x2 return nat with
	mkdsd A' key data olb ub t u v => key
	end.
	
Define dsdData : Fun(A:type)(olb:nat)(ub:nat)(d:<dsd A olb ub>).A :=
	fun dsdData(A:type)(olb:nat)(ub:nat)(d:<dsd A olb ub>) : A.
	match d by x1 x2 return A with
	mkdsd A' key data olb ub t u v => cast data by symm inj <dsd * ** **> x2
	end.

Define dsdTree : Fun(A:type)(olb:nat)(ub:nat)(d:<dsd A olb ub>).<bst A (dsdKey A olb ub d) ub> :=
	fun dsdTree(A:type)(olb:nat)(ub:nat)(d:<dsd A olb ub>) : <bst A (dsdKey A olb ub d) ub>.
	match d by x1 x2 return <bst A (dsdKey A olb ub d) ub> with
	mkdsd A' key data olb' ub' t u v => cast t by trans cong  <bst * key ub'> symm inj <dsd * ** ** > x2
					trans cong <bst A key *> symm inj <dsd ** ** *> x2
					 cong <bst A * ub>
						trans join key (dsdKey A olb ub (mkdsd A' key data olb' ub' t u v))
						cong (dsdKey ! olb ub *) symm x1	
	end.

Define dsdLbProof : Forall(A:type)(olb:nat)(ub:nat)(d:<dsd A olb ub>).{ (le olb (dsdKey ! olb ub d) ) = tt} :=
	foralli(A:type).induction(olb:nat)(ub:nat)(d:<dsd A olb ub>) by x1 x2 IH return { (le olb (dsdKey ! olb ub d) ) = tt} with
	mkdsd A' key data olb' ub' t u v => trans cong (le * (dsdKey ! olb ub d)) inj <dsd ** * **> x2
					trans cong (le olb' (dsdKey ! olb ub *)) x1
					trans join (le olb' (dsdKey ! olb ub (mkdsd ! key data olb' ub' t u v))) (le olb' key)
					u
	end.

Define dsdUbProof : Forall(A:type)(olb:nat)(ub:nat)(d:<dsd A olb ub>).{ (le (dsdKey ! olb ub d) ub ) = tt} :=
	foralli(A:type).induction(olb:nat)(ub:nat)(d:<dsd A olb ub>) by x1 x2 IH return { (le (dsdKey ! olb ub d) ub ) = tt} with
	mkdsd A' key data olb' ub' t u v => trans cong (le (dsdKey ! olb ub d) *) inj <dsd ** ** *> x2
					trans cong (le (dsdKey ! olb ub *) ub') x1
					trans join (le (dsdKey ! olb ub (mkdsd ! key data olb' ub' t u v)) ub') (le key ub')
					v
	end.
	
Define relax_lb : Fun(A:type)(lb ub : nat)(t: <bst A lb ub>)(nlb : nat)(u:{(le nlb lb) = tt}).<bst A nlb ub> :=
	fun relax_lb(A:type)(lb ub : nat)(t: <bst A lb ub>)(nlb : nat)(u:{(le nlb lb) = tt}): <bst A nlb ub>.
	match t by x1 x2 return <bst A nlb ub> with
	leaf A' lb' ub' u'=> (leaf A nlb ub 
		[le_trans nlb lb ub u [bst_prop1 A lb ub t]])
	| node A' lbl' ubl' lbr' ubr' key' u1' u2' data' L' R' => 
		cast (node A
			nlb ubl'
			lbr' ubr'
			key'
			u1'
			u2'
			cast data' by symm inj <bst * ** **> x2
			cast (relax_lb A' lbl' ubl' L' nlb 
			   trans cong (le nlb *) symm inj <bst ** * **> x2 u
			   ) by  cong <bst * nlb ubl'> symm inj <bst * ** **> x2
			cast R' by cong <bst * lbr' ubr'> symm inj <bst * ** **> x2)
		by cong <bst A nlb *> symm inj <bst ** ** *> x2
	end.
	
	
	
Define	delete_smallest : Fun(A : type)(lb ub :nat)(t : <bst A lb ub>).<dsd A lb ub> :=
	fun delete_smallest(A : type)(lb ub :nat)(t : <bst A lb ub>) : <dsd A lb ub> .
	match t by x1 x2 return <dsd A lb ub> with
	leaf A' lb' ub' u' => abort <dsd A lb ub>
	| node A' lbl' ubl' lbr' ubr' key' u1' u2' data' L' R' => 
		match L' by y1 y2 return <dsd A lb ub> with	
		leaf A'' lb'' ub'' u'=> 
			match R' by z1 z2 return <dsd A lb ub> with
			leaf A'' lb'' ub'' u'=> (mkdsd A key' cast data' by symm inj <bst * ** **> x2 lb ub 
							(leaf A key' ub trans cong (le key' *) inj <bst ** ** *> x2 [le_trans key' lbr' ubr' u2' [bst_prop1 A' lbr' ubr' R']]  )
						
						[le_trans lb ubl' key'
							trans cong (le * ubl')  inj <bst ** * **> x2
							[bst_prop1 A' lbl' ubl' L']
							u1']
						trans cong (le key' *) inj <bst ** ** *> x2 [le_trans key' lbr' ubr' u2' [bst_prop1 A' lbr' ubr' R']] 
						)
						
									
			| node A''' lbl''' ubl''' lbr''' ubr''' key''' u1''' u2''' data''' L''' R''' => 
				(mkdsd A key' cast data' by symm inj <bst * ** **> x2 lb ub
					cast (relax_lb A' lbr' ubr' R' key' u2') by trans cong <bst * key' ubr'> symm inj <bst * ** **> x2 cong <bst A key' *> symm inj <bst ** ** *> x2
					[le_trans lb ubl' key' 
						trans cong (le * ubl')  inj <bst ** * **> x2 
						[bst_prop1 A' lbl' ubl' L'] u1']
					[le_trans key' lbr' ub u2' 
						trans cong (le lbr' *)  inj <bst ** ** *> x2
						[bst_prop1 A' lbr' ubr' R']]
				)
			
			
			end		

		| node A'' lbl'' ubl'' lbr'' ubr'' key'' u1'' u2'' data'' L'' R'' => 
			let tmp = (delete_smallest A' lbl' ubl' L') by xyz   in
			let nlb = (dsdKey A' lbl' ubl' tmp) by xyz2 in
			
				(mkdsd A nlb 
					cast (dsdData A' lbl' ubl' tmp) by symm inj <bst * ** **> x2 
				
				lb ub 
					cast (node A' nlb ubl' lbr' ub key' u1' u2'  data'
						cast (dsdTree A' lbl' ubl' tmp) by  cong <bst A' * ubl'> symm xyz2
						
						cast R' by cong <bst A' lbr' *> symm inj <bst ** ** *> x2
						) by cong <bst * nlb ub>  symm inj <bst * ** **> x2
						
						trans cong (le lb *) xyz2
						trans cong (le * (dsdKey ! lbl' ubl' tmp)) 
							 inj <bst ** * **> x2
							
						[dsdLbProof A' lbl' ubl' tmp]
						 
						trans cong (le nlb *) inj <bst ** ** *> x2
						[le_trans nlb lbr' ubr'
							[le_trans nlb key' lbr'
								[le_trans nlb ubl' key' trans cong (le * ubl') xyz2 [dsdUbProof A' lbl' ubl' tmp] 
								u1'] 
							u2']
							[bst_prop1 A' lbr' ubr' R']]
				)
				
		end
	end.
	
Define relax_ub : Fun(A:type)(lb ub : nat)(t: <bst A lb ub>)(nub : nat)(u:{(le ub nub) = tt}).<bst A lb nub> :=
	fun relax_ub(A:type)(lb ub : nat)(t: <bst A lb ub>)(nub : nat)(u:{(le ub nub) = tt}) : <bst A lb nub>.
	match t by x1 x2 return <bst A lb nub> with
	leaf A' lb' ub' u'=>(leaf A lb nub  [le_trans lb ub nub [bst_prop1 A lb ub t] u])
	| node A' lbl' ubl' lbr' ubr' key' u1' u2' data' L' R' => 
		 cast (node A
			lbl' ubl'
			lbr' nub
			key'
			u1'
			u2'
			cast data' by symm inj <bst * ** **> x2
			cast L' by cong <bst * lbl' ubl'> symm inj <bst * ** **> x2
			cast (relax_ub A' lbr' ubr' R' nub 
			   trans cong (le * nub) symm inj <bst ** ** *> x2 u
			   ) by  cong <bst * lbr' nub> symm inj <bst * ** **> x2)
				by cong <bst A * nub> symm inj <bst ** * **> x2
		
	end.	    
	    
Define delete_root : Fun(A:type)(lb ub : nat)(t: <bst A lb ub>).<bst A lb ub> :=
	fun delete_root(A:type)(lb ub : nat)(t: <bst A lb ub>) : <bst A lb ub>.
	match t by x1 x2 return <bst A lb ub> with
	leaf A' lb' ub' u' => abort <bst A lb ub>
	| node A' lbl' ubl' lbr' ubr' key' u1' u2' data' L' R' => 
		match L' by y1 y2 return <bst A lb ub> with
		
		leaf A'' lb'' ub'' u'' => cast (relax_lb A' lbr' ubr' R' lb
					trans cong (le * lbr') inj <bst ** * **> x2 
					[le_trans lbl' ubl' lbr' 
						[bst_prop1 A' lbl' ubl' L']
						[le_trans ubl' key' lbr' u1' u2']]
					
				) by trans cong <bst * lb ubr'> symm inj <bst * ** **> x2
					cong <bst A lb *> symm inj <bst ** ** *> x2
			
		| node A'' lbl'' ubl'' lbr'' ubr'' key'' u1'' u2'' data'' L'' R'' =>
			match R' by z1 z2 return <bst A lb ub> with
			leaf A'' lb'' ub'' u'' => cast (relax_ub A' lbl' ubl' L' ub
						trans cong (le ubl' *) inj <bst ** ** *> x2
						[le_trans ubl' lbr' ubr' [le_trans ubl' key' lbr' u1' u2']
									[bst_prop1 A' lbr' ubr' R']]) by
						trans cong <bst * lbl' ub> symm inj <bst * ** **> x2
						 cong <bst A * ub> symm inj <bst ** * **> x2
									
			| node A''' lbl''' ubl''' lbr''' ubr''' key''' u1''' u2''' data''' L''' R''' => 
				let tmp = (delete_smallest A' lbr' ubr' R') by xyz   in
				let nkey = (dsdKey A' lbr' ubr'  tmp) by xyz2 in
				let ndata = (dsdData A' lbr' ubr'  tmp) by xyz3 in
				let tree = (dsdTree A' lbr' ubr'  tmp) by xyz3 in
				
				cast (node A' lbl' ubl' nkey ubr' nkey  
				
					[le_trans ubl' key' nkey u1'
						[le_trans key' lbr' nkey u2'
							trans cong (le lbr' *) xyz2 [dsdLbProof A' lbr' ubr' tmp]]]
					[x_le_x nkey]
				 	ndata L' 
				 	cast tree by cong <bst A' * ubr'> symm xyz2)
				by trans cong  <bst * lbl' ubr'> symm inj <bst * ** **> x2
					trans cong <bst A * ubr'> symm inj <bst ** * **> x2
					 cong <bst A lb *> symm inj <bst ** ** *> x2
			
			end
		end
		
	end.
	
	
Define bst_remove : Fun(A:type)(lb ub : nat)(t : <bst A lb ub>)(key:nat).<bst A lb ub> :=
	fun bst_remove(A:type)(lb ub : nat)(t : <bst A lb ub>)(key:nat) : <bst A lb ub>.
	match t by x1 y1 return <bst A lb ub> with
	leaf A' lb' ub' u' => abort <bst A lb ub>
	| node A' lbl' ubl' lbr' ubr' key' u1' u2' data' L' R' =>
		match (eqnat key key') by x2 y2 return <bst A lb ub> with
		tt => (delete_root A lb ub t)
		| ff => match (lt key key') by x3 y3 return <bst A lb ub> with
			tt =>  cast (node A' lbl' ubl' lbr' ubr' key' u1' u2' data' (bst_remove A' lbl' ubl' L' key) R') by trans cong  <bst * lbl' ubr'> symm inj <bst * ** **> y1
					trans cong <bst A * ubr'> symm inj <bst ** * **> y1
					 cong <bst A lb *> symm inj <bst ** ** *> y1 
			| ff => cast (node A' lbl' ubl' lbr' ubr' key' u1' u2' data' L' (bst_remove A' lbr' ubr' R' key) ) by trans cong  <bst * lbl' ubr'> symm inj <bst * ** **> y1
					trans cong <bst A * ubr'> symm inj <bst ** * **> y1
					 cong <bst A lb *> symm inj <bst ** ** *> y1 
			end
		end
	end.  
	

	
Inductive bstList : Fun(lb ub: nat).type :=
	bstNil : Fun(lb ub: nat)(p:{(le lb ub) = tt}).<bstList lb ub>
	| bstCons : Fun(lb h ub :nat)(olb oub : nat)(l : <bstList olb oub>)(p1:{ (le oub lb) = tt})(p2 : { (le lb h) = tt})(p3 : {(le h ub) = tt}).<bstList olb ub>.

Define bstList_head : Fun(lb ub:nat)(l:<bstList lb ub>).nat :=
	fun(lb ub:nat)(l:<bstList lb ub>).
	match l by x1 x2 return nat with
	bstNil lb' ub' p' => abort nat
	| bstCons lb' h' ub' olb' oub' l' p1' p2' p3' => h'
	end.
	
Define bstList_head_orZ : Fun(lb ub:nat)(l:<bstList lb ub>).nat :=
	fun(lb ub:nat)(l:<bstList lb ub>).
	match l by x1 x2 return nat with
	bstNil lb' ub' p' => Z
	| bstCons lb' h' ub' olb' oub' l' p1' p2' p3' => h'
	end.
			
Define bstList_relaxub :=
	fun bstList_relaxub(lb ub:nat)(l:<bstList lb ub>)(nub:nat)(p:{(le ub nub) = tt}) : <bstList lb nub>.
	match l by x1 x2 return <bstList lb nub> with
	bstNil lb' ub' p' => cast (bstNil lb' nub 
		[le_trans lb' ub' nub p'
		trans cong (le * nub) symm inj <bstList ** *> x2 p]) by cong <bstList * nub> symm inj <bstList * **> x2
	| bstCons lb' h' ub' olb' oub' l' p1' p2' p3' => 
		cast (bstCons lb' h' nub olb' oub' l' p1' 
			p2' [le_trans h' ub' nub p3' trans cong  (le * nub) symm inj <bstList ** *> x2 p  ]  ) by cong <bstList * nub> symm inj <bstList * **> x2
	end.


	
Define bst_inorder_helper :=
	fun bst_inorder_helper(alb aub : nat)(above:<bstList alb aub>)(A:type)(lb ub:nat)(t:<bst A lb ub>)(p:{ (le aub lb) = tt}) : <bstList alb ub>.
	match t by x1 x2 return	<bstList alb ub> with
		leaf A' lb' ub' u' => (bstList_relaxub alb aub above ub [le_trans aub lb ub p  [bst_prop1 A lb ub t]])
		| node A' lbl' ubl' lbr' ubr' key' u1' u2' data' L' R' => 
			let left = (bst_inorder_helper alb aub above A' lbl' ubl' L' trans cong (le aub *) symm inj <bst ** * **> x2 p) by xyz in
			let left_key = (bstCons ubl' key' lbr' alb ubl' left [x_le_x ubl'] u1' u2') by xyz in
			cast (bst_inorder_helper alb lbr' left_key A' lbr' ubr' R' [x_le_x lbr']) by cong <bstList alb *> symm inj <bst ** ** *> x2
	end.
	
Define bst_inorder : Fun(A:type)(lb ub:nat)(t:<bst A lb ub>).<bstList lb ub> :=
	fun(A:type)(lb ub:nat)(t:<bst A lb ub>).(bst_inorder_helper lb lb (bstNil lb lb [x_le_x lb]) A lb ub t [x_le_x lb]).	
	
Inductive slist : Fun(h:nat).type :=
	snil : <slist Z>
	| scons : Fun(h:nat)(o:nat)(l:<slist o>)(p:{ (le o h) = tt}).<slist h>.
	

Define bstList_to_slist : Fun(lb ub:nat)(l:<bstList lb ub>).<slist (bstList_head_orZ lb ub l)> :=
	fun bts(lb ub:nat)(l:<bstList lb ub>) : <slist (bstList_head_orZ lb ub l)>.
	match l by x1 x2 return <slist (bstList_head_orZ lb ub l)> with
	bstNil lb' ub' p' => cast snil by cong <slist *> symm trans cong (bstList_head_orZ lb ub *) x1 join (bstList_head_orZ lb ub (bstNil lb' ub' !)) Z
	| bstCons lb' h' ub' olb' oub' l' p1' p2' p3' => 
		cast (scons h' (bstList_head_orZ olb' oub' l') (bts olb' oub' l') 
			[induction(olb1' oub1':nat)(l1':<bstList olb1' oub1'>) by y1 y2 IH2 return Forall(a1:{olb1'=olb'})(a2:{oub1'=oub'})(a3:{l1'=l'}).{ (le (bstList_head_orZ olb' oub' l') h') = tt } with
				bstNil lb'' ub'' p'' => foralli(a1:{olb1'=olb'})(a2:{oub1'=oub'})(a3:{l1'=l'}). 
					trans cong (le (bstList_head_orZ olb' oub' *) h') trans symm a3 y1
					trans join (le (bstList_head_orZ olb' oub' (bstNil lb'' ub'' !)) h') (le Z h')
					[Z_le h']
				| bstCons lb'' h'' ub'' olb'' oub'' l'' p1'' p2'' p3'' => foralli(a1:{olb1'=olb'})(a2:{oub1'=oub'})(a3:{l1'=l'}).
					trans cong (le (bstList_head_orZ olb' oub' *) h') trans symm a3 y1
					trans join (le (bstList_head_orZ olb' oub' (bstCons lb'' h'' ub'' olb'' oub'' l'' ! ! !)) h') (le h'' h')
					[le_trans h'' ub'' h' p3''  trans cong (le * h') 
						trans symm inj <bstList ** *> y2  a2 
						[le_trans oub' lb' h' p1' p2']
						
						]
			end olb' oub' l' join olb' olb' join oub' oub' join l' l']
		
		) by cong <slist *> symm trans cong (bstList_head_orZ lb ub *) x1 join (bstList_head_orZ lb ub (bstCons lb' h' ub' olb' oub' l' ! ! !)) h'
	end.
	
Define exLEAF := (leaf bool Z Z [Z_le Z]).	
Define exTree1 := cast (bst_insert bool Z Z exLEAF two tt) by trans cong <bst bool * (max Z two)> join (min Z two) Z  cong <bst bool Z *> join (max Z two) two.
Define exTree3 := cast (bst_insert bool Z two exTree1 one tt) by trans cong <bst bool * (max two one)> join (min Z one) Z  cong <bst bool Z *> join (max two one) two.
Define exTree4 := cast (bst_insert bool Z two exTree3 three ff) by trans cong <bst bool * (max two 
three)> join (min Z three) Z  cong <bst bool Z *> join (max two three) three.

%Set "print_parsed".

Define io :=  (bstList_to_slist Z three (bst_inorder bool Z three exTree4)).
