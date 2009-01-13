Inductive nlist : type :=
  nnil : nlist
| ncons : Fun(n:nat)(l: nlist). nlist.


Define split_list_helper : Fun(l:nlist) (b:bool). <pair nlist nlist> :=
	fun split_list_helper(l:nlist)(b:bool) : <pair nlist nlist>.
		match l by x y return <pair nlist nlist> with		
			nnil => (mkpair nlist nlist nnil nnil)
			| ncons n' l' => 
				match b return <pair nlist nlist> with
					ff => let q = (split_list_helper l' tt) by xyz in
						(mkpair nlist nlist (fst nlist nlist q) (ncons n' (snd nlist nlist q)))
					| tt => let q = (split_list_helper l' ff) by xyz in
						(mkpair nlist nlist (ncons n' (fst nlist nlist q)) (snd nlist nlist q))
				end	
		end.


Define split_list : Fun(l:nlist). <pair nlist nlist> :=
	fun(l:nlist).(split_list_helper l tt).

%-

Define merge : Fun(l:nlist)(m:nlist).nlist :=
	fun merge(l:nlist)(m:nlist) : nlist.
	match l by x y return nlist with
		nnil => m
		| ncons n1' l' =>
			match m return nlist with
				nnil => l
				| ncons n2' m' => 
					match (le n1' n2') by x y return nlist with
						tt => (ncons n2' (merge l m'))
						| ff => (ncons n1' (merge l' m))
					end				
			end
	end.


Define msort : Fun(l:nlist).nlist :=
	fun msort(l:nlist) : nlist.
	match l return nlist with
	  nnil => nnil
	| ncons n' l' => match l' return nlist with
	                   nnil => (ncons n' nnil)
	                 | ncons n'' l'' =>  
				let q = (split_list l) by xyz in
				  (merge (msort (fst nlist nlist q)) (msort (snd nlist nlist q)))
			 end
	end.
	

Define mylist := (ncons (S (S (S Z))) (ncons (S (S Z)) (ncons (S Z) nnil))).
Define mylist2 := (split_list mylist).
Define mylist2a := (msort (fst nlist nlist mylist2)).
Define mylist2b := (msort (snd nlist nlist mylist2)).
Define mylist3 := (merge mylist2a mylist2b).
Define mylist4 := (msort mylist).

-%		
