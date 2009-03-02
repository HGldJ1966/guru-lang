Include "plus.g". % for some lemmas relating min and plus below.

Define min : Fun(a b:nat).nat :=
	fun min(a b :nat) : nat.
	match a by u u return nat with
	Z => Z
	| S a' => match b by u u return nat with
		Z => Z
		| S b' => (S (min a' b'))
		end
	end.
	
Define max : Fun(a b:nat).nat :=
	fun max(a b :nat) : nat.
	match a by u u return nat with
	Z => b
	| S a' => match b by u u return nat with
		Z => a
		| S b' => (S (max a' b'))
		end
	end.  
	  	  

	
Define min_total : Forall(a b : nat).Exists(c:nat).{(min a b) = c} :=
	induction(a : nat) by x1 x2 IH return Forall(b:nat).Exists(c:nat).{ (min a b) = c} with	
	Z => foralli(b:nat).
		existsi Z {(min a b) = *}
		trans cong (min * b) x1
		join (min Z b) Z
	| S a' => foralli(b:nat).
		[induction(d:nat) by y1 y2 IH2 return Forall(u:{d = b}).Exists(c:nat).{ (min a d) = c} with
			Z => foralli(u:{d=b}).
				existsi Z {(min a d) = *}
				trans cong (min a *) y1
				trans cong (min * Z) x1
				join (min (S a') Z) Z
			| S d' => foralli(u:{d=b}).
				existse [IH a' d'] foralli(q:nat)(q':{(min a' d') = q}).
				existsi (S q) {(min a d) = *}
				trans cong (min * d) x1
				trans cong (min (S a') *) y1
				trans join (min (S a') (S d')) (S (min a' d'))
				cong (S *) q'
			end b join b b]	
	end.

Total min min_total.

Define max_total : Forall(a b : nat).Exists(c:nat).{(max a b) = c} :=
	induction(a : nat) by x1 x2 IH return Forall(b:nat).Exists(c:nat).{ (max a b) = c} with	
	Z => foralli(b:nat).
		existsi b {(max a b) = *}
		trans cong (max * b) x1
		join (max Z b) b
	| S a' => foralli(b:nat).
		[induction(d:nat) by y1 y2 IH2 return Forall(u:{d = b}).Exists(c:nat).{ (max a d) = c} with
			Z => foralli(u:{d=b}).
				existsi (S a') {(max a d) = *}
				trans cong (max a *) y1
				trans cong (max * Z) x1
				join (max (S a') Z) (S a')
			| S d' => foralli(u:{d=b}).
				existse [IH a' d'] foralli(q:nat)(q':{(max a' d') = q}).
				existsi (S q) {(max a d) = *}
				trans cong (max * d) x1
				trans cong (max (S a') *) y1
				trans join (max (S a') (S d')) (S (max a' d'))
				cong (S *) q'
			end b join b b]	
	end.	
	
Total max max_total.

Define min_le_lemma : Forall(a b:nat).{ (le (min a b) a) = tt } :=
	induction(a:nat) by x1 x2 IH return Forall(b:nat).{ (le (min a b) a) = tt } with
	Z => foralli(b:nat).
		trans cong (le (min * b) *) x1
		trans cong (le * Z) join (min Z b) Z
		join (le Z Z) tt
	| S a' => foralli(b:nat).
		[induction(d:nat) by y1 y2 IH2 return Forall(u:{d = b}).{ (le (min a d) a) = tt }  with
			Z => foralli(u:{d=b}).
				trans cong (le (min a *) a) y1
				trans cong (le (min * Z) *) x1
				trans join (le (min (S a') Z) (S a')) (le Z (S a'))
				join (le Z (S a')) tt
			|S d' =>  foralli(u:{d=b}).
				existse [min_total a' d'] foralli(f:nat)(f':{(min a' d') = f}).
				trans cong (le (min * d) *) x1
				trans cong (le (min (S a') * ) (S a')) y1
				trans join (le (min (S a') (S d')) (S a')) (le (S (min a' d')) (S a'))
				trans cong (le (S *) (S a')) f'
				trans join (le (S f) (S a')) (le f a')
				trans cong (le * a') symm f'
				[IH a' d']
			end b join b b]
	end.
	
Define max_comm : Forall(a b:nat).{ (max a b) = (max b a) } :=
	induction(a:nat) by x1 x2 IH return Forall(b:nat).{ (max a b) = (max b a) } with
	Z => foralli(b:nat).
		[induction(d:nat) by y1 y2 IH2 return Forall(u:{d = b}).{ (max a d) = (max d a) }  with
		Z => foralli(u:{d=b}).
			trans cong (max * d) x1
			trans cong (max Z *) y1
			trans cong (max Z *) symm x1
			cong (max * a) symm y1
		| S d'=> foralli(u:{d=b}).
			trans cong (max * d) x1
			trans cong (max Z *) y1
			trans join (max Z (S d')) (S d')
			trans join (S d') (max (S d') Z)
			trans cong (max * Z) symm y1
			cong (max d *) symm x1
		end b join b b]
	| S a' => foralli(b:nat).
		[induction(d:nat) by y1 y2 IH2 return Forall(u:{d = b}).{ (max a d) = (max d a) }  with
		Z => foralli(u:{d=b}).
			trans cong (max a *) y1
			trans cong (max * Z) x1
			trans join (max (S a') Z) (max Z (S a'))
			trans cong (max Z *) symm x1
			cong (max * a) symm y1
		| S d' => foralli(u:{d=b}). 
			trans cong (max a *) y1
			trans cong (max * (S d')) x1
			trans join (max (S a') (S d')) (S (max a' d'))
			trans cong (S *) [IH a' d']
			trans join (S (max d' a')) (max (S d') (S a'))
			trans cong (max (S d') *) symm x1
			cong (max * a) symm y1
		end b join b b]
	end.
		

Define max_le_lemma : Forall(a b:nat).{ (le a (max a b)) = tt } :=
	induction(a:nat) by x1 x2 IH return Forall(b:nat).{ (le a (max a b)) = tt } with
	Z => foralli(b:nat).
		[induction(d:nat) by y1 y2 IH2 return Forall(u:{d = b}).{  (le a (max a d)) = tt  }  with
		Z => foralli(u:{d=b}).
			trans cong (le * (max * d)) x1
			trans cong (le Z (max Z *)) y1
			trans join (le Z (max Z Z)) (le Z Z)
			join (le Z Z) tt
		|S d' => foralli(u:{d=b}).
			trans cong (le * (max * d)) x1
			trans cong (le Z (max Z *)) y1
			trans join (le Z (max Z (S d'))) (le Z (S d'))
			join (le Z (S d')) tt
		end b join b b] 
	| S a' => foralli(b:nat).
		[induction(d:nat) by y1 y2 IH2 return Forall(u:{d = b}).{  (le a (max a d)) = tt  }  with
			Z => foralli(u:{d=b}).
				trans cong (le * (max * d)) x1
				trans cong (le (S a') (max (S a') *)) y1
				trans join (le (S a') (max (S a') Z)) (le (S a') (S a'))
				trans join (le (S a') (S a')) (le a' a')
				[x_le_x a']
			|S d' =>  foralli(u:{d=b}).
				existse [max_total a' d'] foralli(f:nat)(f':{(max a' d') = f}).
				trans cong (le * (max * d)) x1
				trans cong (le (S a') (max (S a') *)) y1
				trans join (le (S a') (max (S a') (S d'))) (le (S a') (S (max a' d')))
				trans cong (le (S a') (S *)) f'
				trans join (le (S a') (S f)) (le a' f)
				trans cong (le a' *) symm f'
				[IH a' d']
			end b join b b]
	end.	
	
Define max_le_lemma2 : Forall(a b:nat).{ (le b (max a b)) = tt } :=
  foralli(a b:nat).
    trans cong (le b *) [max_comm a b]
          [max_le_lemma b a].

Define min_comm : Forall(a b:nat).{ (min a b) = (min b a) } :=
	induction(a:nat) by x1 x2 IH return Forall(b:nat).{ (min a b) = (min b a) } with
	Z => foralli(b:nat).
		[induction(d:nat) by y1 y2 IH2 return Forall(u:{d = b}).{ (min a d) = (min d a) }  with
		Z => foralli(u:{d=b}).
			trans cong (min * d) x1
			trans cong (min Z *) y1
			trans cong (min Z *) symm x1
			cong (min * a) symm y1
		| S d'=> foralli(u:{d=b}).
			trans cong (min * d) x1
			trans cong (min Z *) y1
			trans join (min Z (S d')) Z
			trans join Z (min (S d') Z)
			trans cong (min * Z) symm y1
			cong (min d *) symm x1
		end b join b b]
	| S a' => foralli(b:nat).
		[induction(d:nat) by y1 y2 IH2 return Forall(u:{d = b}).{ (min a d) = (min d a) }  with
		Z => foralli(u:{d=b}).
			trans cong (min a *) y1
			trans cong (min * Z) x1
			trans join (min (S a') Z) (min Z (S a'))
			trans cong (min Z *) symm x1
			cong (min * a) symm y1
		| S d' => foralli(u:{d=b}). 
			trans cong (min a *) y1
			trans cong (min * (S d')) x1
			trans join (min (S a') (S d')) (S (min a' d'))
			trans cong (S *) [IH a' d']
			trans join (S (min d' a')) (min (S d') (S a'))
			trans cong (min (S d') *) symm x1
			cong (min * a) symm y1
		end b join b b]
	end.
	
Define min_le_lemma2 : Forall(a b:nat).{ (le (min a b) b) = tt } :=
  foralli(a b:nat).
    trans cong (le * b) [min_comm a b]
          [min_le_lemma b a].

Define min_le : Forall(a b:nat)(u:{(le a b) = tt}).{ (min a b) = a } :=
	induction(a:nat) by x1 x2 IH return Forall(  b:nat)(u:{(le a b) = tt}).{ (min a b) = a } with	
	Z => foralli( b:nat)(u:{(le a b) = tt}).
		trans cong (min * b) x1
		trans join (min Z b) Z
		symm x1
	| S a' => foralli( b:nat)(u:{(le a b) = tt}).
		[induction(c:nat) by y1 y2 IH2 return Forall(r:{c=b}).{ (min a c) = a } with
			Z => foralli(r:{c=b}).
				contra trans symm u trans cong (le * b) x1 trans cong (le (S a') *) symm r trans cong (le (S a') *) y1
				trans join (le (S a') Z) ff clash ff tt
				{ (min a c) = a }
			|S c' => foralli(r:{c=b}).
				 trans cong (min * c) x1
				 trans cong (min (S a') *) y1
				 trans join (min (S a') (S c')) (S (min a' c'))
				 trans cong (S *) [IH a' c' trans join (le a' c') (le (S a') (S c')) trans cong (le * (S c')) symm x1 trans cong (le a *) symm y1  trans cong (le a *) r u]
				 symm x1
		end b join b b]
	end.
	
Define max_le : Forall(a b :nat)(u:{(le a b) = tt}).{ (max a b) = b } :=
	induction(a:nat) by x1 x2 IH return Forall(b :nat)(u:{(le a b) = tt}).{ (max a b) = b } with
	Z=> foralli(b :nat)(u:{(le a b) = tt}).
		trans cong (max * b) x1
		 join (max Z b) b
	| S a'=> foralli(b :nat)(u:{(le a b) = tt}).
		[induction(c:nat) by y1 y2 IH2 return Forall(r:{c=b}).{ (max a c) = c} with
			Z=> foralli(r:{c=b}).
				contra trans symm u trans cong (le * b) x1 trans cong (le (S a') *) symm r trans cong (le (S a') *) y1
				trans join (le (S a') Z) ff clash ff tt
				{ (max a c) = c }
			| S c'=> foralli(r:{c=b}).
				trans cong (max * c) x1
				trans cong (max (S a') *) y1
				trans join (max (S a') (S c')) (S (max a' c'))
				trans cong (S *) [IH a' c' trans join  (le a' c') (le (S a') (S c')) trans cong (le * (S c')) symm x1 trans cong (le a *) symm y1  trans cong (le a *) r u]
				symm y1
				
		end b join b b]
	end.

Define max_easy : Forall(a b :nat).{(le a (max b a)) = tt} :=
	induction(a:nat) by x1 x2 IH return Forall(b:nat).{(le a (max b a)) = tt} with
	Z=> induction(b:nat) by y1 y2 IH2 return {(le a (max b a)) = tt} with
		Z=> trans cong (le * (max b *)) x1
			trans cong (le Z (max * Z)) y1
			join (le Z (max Z Z)) tt
		| S b'=> trans cong (le * (max b *)) x1
			trans cong (le Z (max * Z)) y1
			join (le Z (max (S b') Z)) tt
		end
	|S a' => induction(b:nat) by y1 y2 IH2 return {(le a (max b a)) = tt} with
		Z=> trans cong (le * (max b *)) x1
			trans cong (le (S a') (max * (S a'))) y1
			trans join (le (S a') (max Z (S a'))) (le (S a') (S a'))
			[x_le_x (S a')]
		| S b'=> trans cong (le * (max b *)) x1
			trans cong (le (S a') (max * (S a'))) y1
			trans join (le (S a') (max (S b') (S a'))) (le (S a') (S (max b' a')))
			existse [max_total b' a'] foralli(c:nat)(c':{(max b' a') = c}).
			trans cong (le (S a') (S *)) c'
			trans join (le (S a') (S c)) (le a' c)
			trans cong (le a' *) symm c'
			[IH a' b']
		end
	
	end.			
			
Define max_mono1 : Forall(a b c:nat)(u:{(le a b) = tt}). { (le (max a c) (max b c)) = tt } :=
	induction(a:nat) by x1 x2 IH return Forall (b c:nat)(u:{(le a b) = tt}). { (le (max a c) (max b c)) = tt } with
	Z => induction(b:nat) by y1 y2 IH2 return Forall(c:nat)(u:{(le a b) = tt}). { (le (max a c) (max b c)) = tt } with
		Z => foralli(c:nat)(u:{(le a b) = tt}).
			trans cong (le (max * c) (max b c)) x1
			trans cong (le (max Z c) (max * c)) y1
			trans join (le (max Z c) (max Z c)) (le c c)
			[x_le_x c]
		| S b'=> induction(c:nat) by z1 z2 IH3 return Forall(u:{(le a b) = tt}).{ (le (max a c) (max b c)) = tt } with
			Z=> 	foralli(u:{(le a b) = tt}).
				trans cong (le (max a *) (max b *)) z1
				trans cong (le (max * Z) (max b Z)) x1
				trans cong (le (max Z Z) (max * Z)) y1
				join (le (max Z Z) (max (S b') Z)) tt
			
			|S c'=> foralli(u:{(le a b) = tt}).
				trans cong (le (max a *) (max b *)) z1
				trans cong (le (max * (S c')) (max b (S c'))) x1
				trans cong (le (max Z (S c')) (max * (S c'))) y1
				trans join (le (max Z (S c')) (max (S b') (S c'))) (le (S c') (S (max b' c')))
				trans join (le (S c') (S (max b' c'))) (le c' (max b' c'))
				[max_easy c' b']
			end
			
		end 
	
	| S a' => induction(b:nat) by y1 y2 IH2 return Forall(c:nat)(u:{(le a b) = tt}). { (le (max a c) (max b c)) = tt } with
		Z=> foralli(c:nat)(u:{(le a b) = tt}). 
			contra trans symm u trans cong (le * b) x1 trans cong (le (S a') *) y1 trans join (le (S a') Z) ff clash ff tt
				{ (le (max a c) (max b c)) = tt } 
		| S b'=>induction(c:nat) by z1 z2 IH3 return Forall(u:{(le a b) = tt}).{ (le (max a c) (max b c)) = tt } with
			Z=> foralli(u:{(le a b) = tt}).
				trans cong (le (max a *) (max b *)) z1
				trans cong (le (max * Z) (max b Z)) x1
				trans cong (le (max (S a') Z) (max * Z)) y1
				trans join (le (max (S a') Z) (max (S b') Z)) (le (S a') (S b'))
				trans cong (le * (S b')) symm x1
				trans cong (le a *) symm y1
				u 
			|S c'=>foralli(u:{(le a b) = tt}).
				trans cong (le (max a *) (max b *)) z1
				trans cong (le (max * (S c')) (max b (S c'))) x1
				trans cong (le (max (S a') (S c')) (max * (S c'))) y1
				trans join (le (max (S a') (S c')) (max (S b') (S c'))) (le (S (max a' c')) (S (max b' c')))
				existse [max_total a' c'] foralli(d:nat)(d':{(max a' c') = d}).
				existse [max_total b' c'] foralli(e:nat)(e':{(max b' c') = e}).
				trans cong (le (S *) (S (max b' c'))) d'
				trans cong (le (S d) (S *)) e'
				trans join (le (S d) (S e)) (le d e)
				trans cong (le * e) symm d'
				trans cong (le (max a' c') *) symm e'
				[IH a' b' c' trans join (le a' b') (le (S a') (S b')) trans cong (le * (S b')) symm x1 trans cong (le a *) symm y1 u]
			end
		
		end
	
	end.
	
Define max_mono2 : Forall(a b c:nat)(u:{(le b c) = tt}). { (le (max a b) (max a c)) = tt } :=
  foralli(a b c:nat)(u:{(le b c) = tt}). 
    trans cong (le * (max a c)) [max_comm a b]
    trans cong (le (max b a) *) [max_comm a c]
          [max_mono1 b c a u].

Define max_self : Forall(x:nat). { (max x x) = x } :=
  induction(x:nat) return { (max x x) = x } with
    Z => hypjoin (max x x) x by x_eq end
  | S x' => hypjoin (max x x) x by x_eq [x_IH x'] end
  end.

Define max_bound : Forall(a b c:nat)(u1:{(le a c) = tt})(u2:{(le b c) = tt}). {(le (max a b) c) = tt} :=
  foralli(a b c:nat)(u1:{(le a c) = tt})(u2:{(le b c) = tt}).
    trans cong (le (max a b) *) symm [max_self c]
          [le_trans (max a b) (max c b) (max c c)
             [max_mono1 a c b u1]
             [max_mono2 c b c u2]].

Define min_mono1 : Forall(a b c:nat)(u:{(le a b) = tt}). { (le (min a c) (min b c)) = tt } :=
	induction(a:nat) by x1 x2 IH return Forall (b c:nat)(u:{(le a b) = tt}). { (le (min a c) (min b c)) = tt } with
	Z => foralli(b c:nat)(u:{(le a b) = tt}).
		trans cong (le (min * c) (min b c)) x1
		trans join (le (min Z c) (min b c)) (le Z (min b c))
		existse [min_total b c] foralli(d:nat)(d':{(min b c) = d}).
		trans cong (le Z *) d'
		[Z_le d]
		
	
	| S a' => induction(b:nat) by y1 y2 IH2 return Forall(c:nat)(u:{(le a b) = tt}). { (le (min a c) (min b c)) = tt } with
		Z=> foralli(c:nat)(u:{(le a b) = tt}). 
			contra trans symm u trans cong (le * b) x1 trans cong (le (S a') *) y1 trans join (le (S a') Z) ff clash ff tt
				{ (le (min a c) (min b c)) = tt } 
		| S b'=>induction(c:nat) by z1 z2 IH3 return Forall(u:{(le a b) = tt}).{ (le (min a c) (min b c)) = tt } with
			Z=> foralli(u:{(le a b) = tt}).
				trans cong (le (min a *) (min b *)) z1
				trans cong (le (min * Z) (min b Z)) x1
				trans cong (le (min (S a') Z) (min * Z)) y1
				trans join (le (min (S a') Z) (min (S b') Z)) (le Z Z)
				[x_le_x Z]
			|S c'=>foralli(u:{(le a b) = tt}).
				trans cong (le (min a *) (min b *)) z1
				trans cong (le (min * (S c')) (min b (S c'))) x1
				trans cong (le (min (S a') (S c')) (min * (S c'))) y1
				trans join (le (min (S a') (S c')) (min (S b') (S c'))) (le (S (min a' c')) (S (min b' c')))
				existse [min_total a' c'] foralli(d:nat)(d':{(min a' c') = d}).
				existse [min_total b' c'] foralli(e:nat)(e':{(min b' c') = e}).
				trans cong (le (S *) (S (min b' c'))) d'
				trans cong (le (S d) (S *)) e'
				trans join (le (S d) (S e)) (le d e)
				trans cong (le * e) symm d'
				trans cong (le (min a' c') *) symm e'
				[IH a' b' c' trans join (le a' b') (le (S a') (S b')) trans cong (le * (S b')) symm x1 trans cong (le a *) symm y1 u]
			end
		
		end
	
	end.	
	
Define min_mono2 : Forall(a b c:nat)(u:{(le b c) = tt}). { (le (min a b) (min a c)) = tt } :=
  foralli(a b c:nat)(u:{(le b c) = tt}). 
    trans cong (le * (min a c)) [min_comm a b]
    trans cong (le (min b a) *) [min_comm a c]
          [min_mono1 b c a u].

Define min_self : Forall(x:nat). { (min x x) = x } :=
  induction(x:nat) return { (min x x) = x } with
    Z => hypjoin (min x x) x by x_eq end
  | S x' => hypjoin (min x x) x by x_eq [x_IH x'] end
  end.

Define min_bound : Forall(a b c:nat)(u1:{(le a b) = tt})(u2:{(le a c) = tt}). {(le a (min b c)) = tt} :=
  foralli(a b c:nat)(u1:{(le a b) = tt})(u2:{(le a c) = tt}).
    trans cong (le * (min b c)) symm [min_self a]
          [le_trans (min a a) (min b a) (min b c)
             [min_mono1 a b a u1]
             [min_mono2 b a c u2]].


Define le_min_lemma : Forall(a b c:nat)(u:{ (le a b) = tt })(v:{(le a c) = tt}).{ (le a (min b c)) =tt} :=
	induction(a:nat) by x1 x2 IH return Forall(b c:nat)(u:{ (le a b) = tt })(v:{(le a c) = tt}).{ (le a (min b c)) =tt} with
	Z => foralli(b c:nat)(u:{ (le a b) = tt })(v:{(le a c) = tt}).
		trans cong (le * (min b c)) x1
		existse [min_total b c] foralli(z:nat)(z':{(min b c) = z}).
		trans cong (le Z *) z'
		[Z_le z]
	
	|S a' => induction(b:nat) by y1 y2 IH2 return Forall(c:nat)(u:{ (le a b) = tt })(v:{(le a c) = tt}).{ (le a (min b c)) =tt} with
		Z=> foralli( c:nat)(u:{ (le a b) = tt })(v:{(le a c) = tt}).
			contra trans symm u trans cong (le * b) x1 trans cong (le (S a') *) y1 trans join (le (S a') Z) ff clash ff tt
				{ (le a (min b c)) =tt}
		| S b'=> induction(c:nat) by z1 z2 IH3 return Forall(u:{ (le a b) = tt })(v:{(le a c) = tt}).{ (le a (min b c)) =tt} with
			Z=> foralli(u:{ (le a b) = tt })(v:{(le a c) = tt}).
				contra trans symm v trans cong (le * c) x1 trans cong (le (S a') *) z1 trans join (le (S a') Z) ff clash ff tt
				{ (le a (min b c)) =tt}
			| S c'=>  foralli(u:{ (le a b) = tt })(v:{(le a c) = tt}).
				trans cong (le * (min b c)) x1
				trans cong (le (S a') (min * c)) y1
				trans cong (le (S a') (min (S b') *)) z1
				trans join (le (S a') (min (S b') (S c'))) (le (S a') (S (min b' c')))
				existse [min_total b' c'] foralli(q:nat)(q':{(min b' c') = q}).
				trans cong (le (S a') (S *)) q'
				trans join (le (S a') (S q)) (le a' q)
				trans cong (le a' *) symm q'
				[IH a' b' c' 
				trans join  (le a' b') (le (S a') (S b')) trans cong (le * (S b')) symm x1 trans cong (le a *) symm y1 u 
				trans join  (le a' c') (le (S a') (S c')) trans cong (le * (S c')) symm x1 trans cong (le a *) symm z1 v 
				]
			end
		
		end
	end.
	
Define le_max_lemma : Forall(a b c:nat)(u:{ (le a c) = tt})(v:{(le b c) = tt}).{(le (max a b) c) = tt} :=
	induction(a:nat) by x1 x2 IH return Forall(b c:nat)(u:{ (le a c) = tt})(v:{(le b c) = tt}).{(le (max a b) c) = tt} with
	Z => foralli(b c:nat)(u:{ (le a c) = tt})(v:{(le b c) = tt}).
		trans cong (le (max * b) c) x1
		trans join (le (max Z b) c) (le b c)
		v
	| S a' =>foralli(b c:nat)(u:{ (le a c) = tt})(v:{(le b c) = tt}).
		[induction(d:nat) by y1 y2 IH2 return Forall(q:{d=b}).{(le (max a d) c) = tt} with
			Z=> foralli(q:{d=b}).
				trans cong (le (max a *) c) y1
				trans cong (le * c) [max_comm a Z]
				trans cong (le * c) join (max Z a) a
				u
			| S d' => foralli(q:{d=b}).
				[induction(e:nat) by z1 z2 IH3 return Forall(r:{e=c}).{(le (max a d) c) = tt} with
					Z=> foralli(r:{e=c}).
						contra trans symm u trans cong (le a *) trans symm r z1 trans cong (le * Z) x1
						trans join (le (S a') Z) ff clash ff tt 
							{(le (max a d) c) = tt}
					|S e' =>foralli(r:{e=c}).
						existse [max_total a' d'] foralli(f:nat)(f':{(max a' d') = f}).
						trans cong (le (max a *) c) q
						trans cong (le (max * b) c) x1
						trans cong (le (max (S a') *) c) trans symm q y1
						trans join (le (max (S a') (S d')) c) (le (S (max a' d')) c)
						trans cong (le (S *) c) f'
						trans cong (le (S f) *) trans symm r z1
						trans join (le (S f) (S e')) (le f e')
						trans cong (le * e') symm f'
						[IH a' d' e'
							symm trans symm u trans cong (le * c) x1 trans cong (le (S a') *) trans symm r z1
								 join (le (S a') (S e')) (le a' e')
							symm trans symm v trans cong (le * c) trans symm q y1 trans cong (le (S d') *) trans symm r z1
								join (le (S d') (S e')) (le d' e')
						]
				end c join c c]
		end b join b b]
	end.

Define min_plus : Forall(x y z:nat).
                  { (min (plus x y) (plus x z)) = (plus x (min y z))} :=
  induction(x:nat) by ux vx IH 
    return Forall(y z:nat).{ (min (plus x y) (plus x z)) = (plus x (min y z))}
    with
    Z => foralli(y z:nat).
           trans cong (min (plus * y) (plus * z))
                   ux
           trans join (min (plus Z y) (plus Z z))
                      (plus Z (min y z))
                 cong (plus * (min y z)) symm ux
  | S x' => foralli(y z:nat).
              trans cong (min (plus * y) (plus * z)) ux
              trans join (min (plus (S x') y) (plus (S x') z))
                         (S (min (plus x' y) (plus x' z)))
              trans cong (S *) [IH x' y z]
              trans join (S (plus x' (min y z)))
                         (plus (S x') (min y z))
                    cong (plus * (min y z)) symm ux
  end.
  
Define max_plus : Forall(x y z:nat).
                  { (max (plus x y) (plus x z)) = (plus x (max y z))} :=
  induction(x:nat) by ux vx IH 
    return Forall(y z:nat).{ (max (plus x y) (plus x z)) = (plus x (max y z))}
    with
    Z => foralli(y z:nat).
           trans cong (max (plus * y) (plus * z))
                   ux
           trans join (max (plus Z y) (plus Z z))
                      (plus Z (max y z))
                 cong (plus * (max y z)) symm ux
  | S x' => foralli(y z:nat).
              trans cong (max (plus * y) (plus * z)) ux
              trans join (max (plus (S x') y) (plus (S x') z))
                         (S (max (plus x' y) (plus x' z)))
              trans cong (S *) [IH x' y z]
              trans join (S (plus x' (max y z)))
                         (plus (S x') (max y z))
                    cong (plus * (max y z)) symm ux
  end.
  
