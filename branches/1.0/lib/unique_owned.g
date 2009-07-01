Include "unique.g".

ResourceType unique_owned with
  Define primitive consume_unique_owned : Fun(A:type)(^#unique_owned x:A).void
  := fun(A:type)(x:A).voidi <<END
#define gconsume_unique_owned(A,x) 
END.

Init ginit_unique_owned_unique(#unique_owned x)(#unique y).#unique_owned <<END
  #define ginit_unique_owned_unique(A,x,y) y
END.

Init ginit_unique_owned_owned(#unique_owned x)(#owned y).#owned <<END
  #define ginit_unique_owned_owned(A,x,y) y
END.

Init ginit_unique_owned_unowned(#unique_owned x)(#unowned y).#<owned x> <<END
  #define ginit_unique_owned_unowned(A,x,y) y
END.

Define primitive inspect_unique : Fun(A:type)(!#unique a:A).#<unique_owned a> A :=
  fun(A:type)(a:A).a <<END
#define ginspect_unique(A,a) a
END.

