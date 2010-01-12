Include "unique.g".

ResourceType unique_owned affine.

Define primitive consume_unique_owned : Fun(spec A:type)(^#unique_owned a:A).void :=
  fun(A:type)(a:A).voidi <<END
#define gconsume_unique_owned(a) a
END.

ResourceType unique_owned_point affine.

Define primitive consume_unique_owned_point : Fun(spec A:type)(^#unique_owned a:A).void :=
  fun(A:type)(a:A).voidi <<END
#define gconsume_unique_owned_point(a) a
END.

Init ginit_unique_owned_unique(#unique_owned x)(#unique y).#<unique_owned x> <<END
  #define ginit_unique_owned_unique(A,x,y) y
END.

Init ginit_unique_owned_unique_point(#unique_owned x)(#unique_point y).#<unique_owned_point x> <<END
  #define ginit_unique_owned_unique_point(A,x,y) y
END.

Init ginit_unique_owned_owned(#unique_owned x)(#owned y).#owned <<END
  #define ginit_unique_owned_owned(A,x,y) y
END.

Init ginit_unique_owned_unowned(#unique_owned x)(#unowned y).#<owned x> <<END
  #define ginit_unique_owned_unowned(A,x,y) y
END.

Define primitive inspect_unique : Fun(spec A:type)(!#unique a:A).#<unique_owned a> A :=
  fun(spec A:type)(a:A).a <<END
#define ginspect_unique(a) a
END.

Define primitive inspect_unique_point : Fun(spec A:type)(!#unique_point a:A).#<unique_owned_point a> A :=
  fun(spec A:type)(a:A).a <<END
#define ginspect_unique_point(a) a
END.

Define primitive clone_unique_owned : Fun(spec A:type)(!#unique_owned a:A).#<unique_owned a> A :=
  fun(A:type)(a:A).a <<END
#define gclone_unique_owned(a) a
END.

