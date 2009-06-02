%Set "print_parsed".

Include "unowned.g".

ResourceType owned with 
  Define primitive consume_owned : Fun(A:type)(^#owned x:A).void
  := fun(A:type)(x:A).voidi <<END
  #define gconsume_owned(A,x) 
END.

Define primitive inspect : Fun(spec A:type)(!#unowned x:A).#<owned x> A 
  := fun(A:type)(x:A).x <<END
  #define ginspect(x) x
END.

Define primitive inc_owned : Fun(spec A:type)(!#owned y:A).#unowned A
  := fun(A:type)(y:A).y <<END
  void *ginc_owned(void *y) {
    inc(y);
    return y;
  }
END.

Define primitive owned_to_unowned : Fun(spec A:type)(^#owned y:A).#unowned A
  := fun(A:type)(y:A).y <<END
  void *gowned_to_unowned(void *y) {
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