Include trusted "../lib/vec.g".
Include trusted "../lib/minus.g".

Set "print_parsed".

Define vec_nth_tail :=
  fun vec_nth_tail(A:type)(spec n:nat)(l:<vec A n>)(m:nat)(u:{ (lt m n) = tt })
    : <vec A (minus n m)>.
  match m with
    Z => cast l by cong <vec A *> hypjoin n (minus n m) by m_eq end
  | S m' =>
    match l with
      vecn _ => abort <vec A (minus n m)>
    | vecc _ n' a l' =>
        abbrev n_eq = inj <vec ** *> l_Eq in
        abbrev p1 = symm
                      trans symm u
                      trans cong (lt * n) m_eq
                      trans cong (lt (S m') *) n_eq
                            [S_lt_S m' n']
        in
        let l'' = (vec_nth_tail A n' l' m' p1) in
        % l'' : <vec A (minus n' m')>
        % want: <vec A (minus n' m')> = <vec A (minus n m)>
        abbrev p2 = hypjoin (minus n' m') (minus n m) by n_eq m_eq end in
        cast l'' by cong <vec A *> p2
    end
  end.

Define trusted vec_nth_tail_total :
	Forall(A:type)(n:nat)(l:<vec A n>)(m:nat)(u:{ (lt m n) = tt }).
		Exists(l':<vec A (minus n m)>).{ (vec_nth_tail l m) = l' }
	:= truei.
	
Total vec_nth_tail vec_nth_tail_total.

Set "debug_refine_cases".

Define refine_error :
	Forall (n:nat)
         (vt:<vec bool n>)
				 (i:nat)
	       (i_lt:{ (lt i n) = tt })
         (u:{ vt = (mkvec ff n) })
        .{ (vec_nth_tail vt i) = (mkvec ff (minus n i)) }
  :=
	foralli(n:nat)
         (vt:<vec bool n>)
				 (i:nat)
	       (i_lt:{ (lt i n) = tt })
  .
  abbrev tail = (vec_nth_tail bool n vt i i_lt) in
  case tail with
    vecn _ =>
      truei
  | vecc _ n' b vt' =>
      truei
  end
  .
