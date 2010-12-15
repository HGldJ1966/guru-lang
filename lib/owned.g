%Set "print_parsed".

Include "unowned.g".

ResourceType owned affine.

Define primitive consume_owned : Fun(spec A:type)(^#owned a:A).void :=
  fun(A:type)(a:A).voidi <<END
#define gconsume_owned(a) a
END.

Define primitive inspect : Fun(spec A:type)(!#unowned x:A).#<owned x> A 
  := fun(A:type)(x:A).x <<END
  #define ginspect(x) x
END.

Define inspect_tot : Forall(A:type)(x:A).Exists(out:A).
  {(inspect x) = out} := 
  foralli(A:type)(x:A).
    existsi x { (inspect x) = * } join (inspect x) x.

Total inspect inspect_tot.

Define primitive inc_owned : Fun(spec A:type)(!#owned y:A).#unowned A
  := fun(A:type)(y:A).y <<END
  inline void *ginc_owned(void *y) {
    inc(y);
    return y;
  }
END.


Define inc_owned_tot : Forall(A:type)(x:A).Exists(out:A).
  {(inc_owned x) = out} := 
  foralli(A:type)(x:A).
    existsi x { (inc_owned x) = * } join (inc_owned x) x.

Total inc_owned inc_owned_tot.

Define primitive owned_to_unowned : Fun(spec A:type)(^#owned y:A).#unowned A
  := fun(A:type)(y:A).y <<END
  inline void *gowned_to_unowned(void *y) {
    inc(y);
    return y;
  }
END.

Define primitive clone_owned : Fun(spec A:type)(! #owned y:A).#<owned y> A
  := fun(A:type)(y:A).y <<END
  #define gclone_owned(y) y
END.

Init ginit_unowned_owned(#unowned x)(#owned y).#owned <<END
  #define ginit_unowned_owned(A,x,y) y
END.

Init ginit_owned_owned(#owned x)(#owned y).#owned <<END
  #define ginit_unowned_owned(A,x,y) y
END.

Init ginit_owned_unowned(#owned x)(#unowned y).#<owned x> <<END
  #define ginit_owned_unowned(A,x,y) y
END.
