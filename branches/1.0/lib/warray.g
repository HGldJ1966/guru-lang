%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% word-indexed arrays of refcounted data
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Include trusted "word.g".
Include trusted "unique_owned.g".
Include trusted "comparator.g".
Include trusted "option.g".

%Set "print_parsed".

Define primitive type_family_abbrev warray := fun(A:type)(n:word).<vec A (to_nat wordlen n)> <<END
#define gdelete_warray(x)
END.

Define primitive warray_new
 : Fun(spec A:type)(n:word)(^ #owned a:A).#unique <warray A n> := 
  fun(A:type)(n:word)(a:A). (mkvec A a (to_nat wordlen n)) <<END
void *gwarray_new(int n, void *a) {
  void **h = (void **)guru_malloc(sizeof(void *)*n);
  // fprintf(stdout,"gmk_warray(%x).\n", h);
  int c;
  for (c = 0; c < n; c++)
    h[c] = ginc(a); 
  return h;
}
END.

Define primitive warray_get
   : Fun(spec A:type)(spec n:word)(! #unique_owned l:<warray A n>)
        (i:word)
        (u:{(ltword i n) = tt}). #<owned l> A := 
  fun(A:type)(spec n:word)(l:<warray A n>)(i:word)(u:{(ltword i n) = tt}). 
  abbrev p = hypjoin (lt (to_nat i) (to_nat n)) tt by u end in
  (vec_get A (to_nat wordlen n) l (to_nat wordlen i) p) <<END
inline void* gwarray_get(void **l, int i) { return l[i]; }
END.

Define primitive warray_set 
  : Fun(A:type)(i:word)(a:A)(spec n:word)(#unique l:<warray A n>)
       (u:{(ltword i n) = tt}). #unique <warray A n> :=
  fun(A:type)(i:word)(a:A)(spec n:word)(l:<warray A n>)(u:{(ltword i n) = tt}).
  abbrev p = hypjoin (lt (to_nat i) (to_nat n)) tt by u end in
   (vec_update A (to_nat wordlen n) l (to_nat wordlen i) a p) <<END
void *gwarray_set(int A, int c, void *d, void *l) {
  gdec(A,((void **)l)[c]);
  ((void **)l)[c] = d;
  return l;
}
END.

Define primitive warray_free : Fun(A:type)(n:word)(^ #unique l:<warray A n>).void :=
  fun(A:type)(n:word)(l:<warray A n>).voidi <<END
void gwarray_free(int A, int n, void *l) {
  int c;
  // fprintf(stdout,"gwarray_free(%x).\n", l);
  for (c = 0; c < n; c++) 
    gdec(A,((void **)l)[c]);
  carraway_free(l);
}
END.

Define warray_all_set :
  Forall(A:type)(i:word)(a:A)(n:word)(l:<warray A n>)
        (f:Fun(a:A).bool)
        (u1 : { (ltword i n) = tt})
        (u2 : { (vec_all f l) = tt})
        (u3 : { (f a) = tt}).
  { (vec_all f (warray_set i a l u1)) = tt } :=
  foralli(A:type)(i:word)(a:A)(n:word)(l:<warray A n>)
        (f:Fun(a:A).bool)
        (u1 : { (ltword i n) = tt})
        (u2 : { (vec_all f l) = tt})
        (u3 : { (f a) = tt}).
  abbrev u1' = trans symm [ltword_to_lt i n] u1 in
  
  abbrev p1 = join (vec_update l (word_to_nat i) a u1') (warray_set i a l u1) in
  abbrev p2 = [vec_all_update A (word_to_nat n) (word_to_nat i) l a f u1' u2 u3] in

  trans symm cong (vec_all f *) p1 p2.
        
Define warray_all_get :
  Forall(A:type)(n:word)(l:<warray A n>)
        (i:word)
        (f:Fun(a:A).bool)
        (u1 : { (ltword i n) = tt})
        (u2 : { (vec_all f l) = tt}).
  { (f (warray_get l i)) = tt } :=
  foralli(A:type)(n:word)(l:<warray A n>)
        (i:word)
        (f:Fun(a:A).bool)
        (u1 : { (ltword i n) = tt})
        (u2 : { (vec_all f l) = tt}).
  abbrev u1' = trans symm [ltword_to_lt i n] u1 in

  abbrev p1 = join (vec_get l (word_to_nat i)) (warray_get l i) in      
  abbrev p2 = [vec_all_get A (word_to_nat n) (word_to_nat i) l f u1' u2] in

  trans symm cong (f *) p1 p2.
