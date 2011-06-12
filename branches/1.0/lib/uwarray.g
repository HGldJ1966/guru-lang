%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% word-indexed arrays of untracked data
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Include trusted "word.g".
Include trusted "unique_owned.g".
Include trusted "comparator.g".

%Set "print_parsed".

Define primitive type_family_abbrev uwarray := fun(A:type)(n:word).<vec A (word_to_nat n)> <<END
#define gdelete_uwarray(x)
END.

Define primitive uwarray_new
 : Fun(spec A:type)(n:word)(#untracked a:A).#unique <uwarray A n> := 
  fun(spec A:type)(n:word)(a:A). (mkvec A a (word_to_nat n)) <<END
void *guwarray_new(unsigned int n, int a) {
  void **h = (void **)guru_malloc(sizeof(int)*n);
  // fprintf(stdout,"gmk_uwarray(%x).\n", h);
  unsigned int c;
  for (c = 0; c < n; c++)
    h[c] = a; 
  return h;
}
END.

Define primitive uwarray_get
   : Fun(spec A:type)(spec n:word)(! #unique_owned l:<uwarray A n>)
        (i:word)(u:{(ltword i n) = tt}). #untracked A := 
  fun(spec A:type)(spec n:word)(l:<uwarray A n>)(i:word)(u:{(ltword i n) = tt}).
  abbrev p = hypjoin (lt (to_nat i) (to_nat n)) tt by u end in
    (vec_get A (word_to_nat n) l (word_to_nat i) p) <<END
inline void* guwarray_get(void **l, unsigned int i) { return l[i]; }
END.

Define primitive uwarray_set 
  : Fun(spec A:type)(spec n:word)(#unique l:<uwarray A n>)
       (i:word)(#untracked a:A)
       (u:{(ltword i n) = tt}). #unique <uwarray A n> :=
  fun(spec A:type)(spec n:word)(l:<uwarray A n>)
     (i:word)(a:A)
     (u:{(ltword i n) = tt}).
  abbrev p = hypjoin (lt (to_nat i) (to_nat n)) tt by u end in
   (vec_update A (word_to_nat n) l (word_to_nat i) a p) <<END
void *guwarray_set(void *l, unsigned int c, void *d) {
  ((void **)l)[c] = d;
  return l;
}
END.

Define primitive uwarray_free : Fun(spec A:type)(spec n:word)(^ #unique l:<uwarray A n>).void :=
  fun(spec A:type)(spec n:word)(l:<uwarray A n>).voidi <<END
void guwarray_free(void *l) {
  // fprintf(stdout,"guwarray_free(%x).\n", l);
  carraway_free(l);
}
END.


%=============================================================================
% lemmas
%=============================================================================

Define uwarray_new_total := foralli(A:type)(n:word)(a:A).
	existsi (mkvec A a (word_to_nat n)) { (uwarray_new A n a) = * }
	join (uwarray_new A n a) (mkvec A a (word_to_nat n))

Total uwarray_new uwarray_new_total

Define uwarray_get_total :
  Forall(A:type)(n:word)(l:<uwarray A n>)
        (i:word)
        (u:{(ltword i n) = tt}).
  Exists(a:A).{ (uwarray_get l i) = a }
  :=
  foralli(A:type)(n:word)(l:<uwarray A n>)
        (i:word)
        (u:{(ltword i n) = tt}).
  abbrev n' = (word_to_nat n) in
  abbrev i' = (word_to_nat i) in
  abbrev u' = trans symm [ltword_to_lt i n] u in
  existse [vec_get_tot A n' l i' u']
  foralli(a:A)(a_pf:{ (vec_get l i') = a }).
  existsi a { (uwarray_get l i) = * }
	hypjoin (uwarray_get l i) a by a_pf end
  .

Total uwarray_get uwarray_get_total.

Define uwarray_set_total :
  Forall(A:type)(n:word)(l:<uwarray A n>)
        (i:word)(a:A)
        (u:{(ltword i n) = tt}).
  Exists(r:<uwarray A n>).{ (uwarray_set l i a) = r }
  :=
  foralli(A:type)(n:word)(l:<uwarray A n>)
        (i:word)(a:A)
        (u:{(ltword i n) = tt}).
  abbrev n' = (word_to_nat n) in
  abbrev i' = (word_to_nat i) in
  abbrev u' = trans symm [ltword_to_lt i n] u in
  existse [vec_update_tot A n' l i' a u']
  foralli(r:<vec A n'>)(r_pf:{ (vec_update l i' a) = r }).
  existsi r { (uwarray_set l i a) = * }
	hypjoin (uwarray_set l i a) r by r_pf end
	.

Total uwarray_set uwarray_set_total.

% lemma to avoid evaluating to_nat
Define uwarray_get_to_vec_get :
  Forall(A:type)(n:word)(l:<uwarray A n>)(i:word)(u:{(ltword i n) = tt})
    .{ (uwarray_get l i) = (vec_get l (to_nat i)) }
  := 
  foralli(A:type)(n:word)(l:<uwarray A n>)(i:word)(u:{(ltword i n) = tt})
  .
  join (uwarray_get l i) (vec_get l (to_nat i))
  .

Define uwarray_set_get :
  Forall(A:type)(n:word)(l:<uwarray A n>)
        (m:word)(a:A)
        (u1:{ (ltword m n) = tt })
    .{ (uwarray_get (uwarray_set l m a) m) = a }
  :=
  foralli(A:type)(n:word)(l:<uwarray A n>)
        (m:word)(a:A)
        (u1:{ (ltword m n) = tt })
  .
  abbrev u1' = hypjoin (lt (to_nat m) (to_nat n)) tt by u1 end in
  abbrev p = [vec_update_get A (word_to_nat n) l (word_to_nat m) a u1'] in
  hypjoin (uwarray_get (uwarray_set l m a) m) a by p end
  .

Define uwarray_set_get_distinct :
  Forall(A:type)(n:word)(l:<uwarray A n>)
        (m m':word)(a:A)
        (u1:{ (ltword m n) = tt })
        (u2:{ (ltword m' n) = tt })
        (u3:{ m != m' })
    .{ (uwarray_get (uwarray_set l m' a) m) = (uwarray_get l m) }
  :=
  foralli(A:type)(n:word)(l:<uwarray A n>)
				(m m':word)(a:A)
				(u1:{ (ltword m n) = tt })
				(u2:{ (ltword m' n) = tt })
				(u3:{ m != m' })
  .
  abbrev u1' = hypjoin (lt (to_nat m) (to_nat n)) tt by u1 end in
  abbrev u2' = hypjoin (lt (to_nat m') (to_nat n)) tt by u2 end in
  abbrev u3' = [word_neq_to_nat_neq m m' u3] in
  abbrev p = [vec_update_get_distinct A (word_to_nat n) l
					  	(word_to_nat m) (word_to_nat m') a u1' u2' u3'] in
	hypjoin (uwarray_get (uwarray_set l m' a) m) (uwarray_get l m) by p end
  .
