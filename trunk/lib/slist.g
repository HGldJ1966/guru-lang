Include "nat.g".

Inductive slist : Fun(h:nat).type :=
	snil : <slist Z>
	| scons : Fun(h:nat)(o:nat)(l:<slist o>)(p:{ (le o h) = tt}).<slist h>.
	
	
