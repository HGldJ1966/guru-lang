Include "../lib/nat.g".
Include "../lib/minmax.g".
Include "../lib/pair.g".
Include "nlist.g".
Set "print_parsed".


Inductive slist : Fun(h:nat).type :=
	snil : <slist Z>
	| scons : Fun(h:nat)(o:nat)(l:<slist o>)(p:{ (le o h) = tt}).<slist h>.

 
Inductive msort_t : type :=
	mkmsort_t : Fun(m:nat)(l:<slist m>).msort_t.


Define gethead : Fun(mst:msort_t).nat :=
	fun gethead(mst:msort_t) : nat.
	match mst by x1 x2 return nat with
		mkmsort_t m' l' => m'
	end.
	
	
Define getlist : Fun(mst:msort_t).<slist (gethead mst)> :=
	fun getlist(mst:msort_t) : <slist (gethead mst)>.
	match mst by x1 x2 return <slist (gethead mst)> with
		mkmsort_t m' l' => cast l' by cong <slist *> 
			symm trans cong (gethead *) x1
			join (gethead (mkmsort_t m' l')) m'
	end.	


Define merge : Fun(h1:nat)(l:<slist h1>)(h2:nat)(m:<slist h2>).<slist (max h1 h2)> :=
	fun merge(h1:nat)(l:<slist h1>)(h2:nat)(m:<slist h2>) : <slist (max h1 h2)>.
	match l by x1 y1 return <slist (max h1 h2)> with
		snil => cast m by cong <slist *> 
			trans join h2 (max Z h2)			
			cong (max * h2)
				symm inj <slist *> y1
		| scons h1' o1' l' p1' =>
			match m by x2 y2 return <slist (max h1 h2)> with
				snil => cast l by cong <slist *>
					trans join h1 (max Z h1)
					trans [max_comm Z h1]
					cong (max h1 *)
						symm inj <slist *> y2
				| scons h2' o2' m' p2' => 
					match (le h1' h2') by x3 y3 return <slist (max h1 h2)> with
						ff => cast (scons h1' (max o1' h2) (merge o1' l' h2 m) 
								[le_max_lemma o1' h2 h1' p1' 
								trans cong (le * h1') inj <slist *> y2 
								[le_ff_implies_le h1' h2' x3]]) 
							by cong <slist *>
							symm trans [max_comm h1 h2] 
								trans cong (max * h1) inj <slist *> y2 
								trans cong (max h2' *) inj <slist *> y1
								[max_le h2' h1' [le_ff_implies_le h1' h2' x3]]
						| tt => cast (scons h2' (max o2' h1) (merge o2' m' h1 l) 
								[le_max_lemma o2' h1 h2' p2' 
								trans cong (le * h2') inj <slist *> y1 x3]) 
							by cong <slist *>
							symm trans cong (max h1 *) inj <slist *> y2 
							trans cong (max * h2') inj <slist *> y1 [max_le h1' h2' x3]
						
					end				
			end
	end.


Define msort : Fun(l:nlist).msort_t :=	
	fun msort(l:nlist) : msort_t.
	match l return msort_t with
		nnil => (mkmsort_t Z snil)
		| ncons n' l' => 
		match l' return msort_t with
			nnil => (mkmsort_t n' (scons n' Z snil [Z_le n']))
			| ncons n'' l'' =>				
				let q = (split_list l) by xyz in
				let left = (msort (fst nlist nlist q)) by xyz in
				let right = (msort (snd nlist nlist q)) by xyz in
				(mkmsort_t (max (gethead left)(gethead right)) 
				  	(merge (gethead left) (getlist left) (gethead right) (getlist right)))
		end
	end.


Define mylist0 := (scons (S Z) Z snil join (le Z (S Z)) tt).
Define mylist1 := (ncons (S (S (S Z))) (ncons (S (S Z)) (ncons (S Z) nnil))).
Define mylist2 := (ncons (S Z) (ncons (S (S Z)) (ncons (S (S (S Z))) nnil))).
Define mylist3 := (msort mylist2).
