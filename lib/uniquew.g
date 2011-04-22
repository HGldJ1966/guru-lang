% uniquew is a resource type for write-access to a data structure.
% You can get a uniquew from a unique.  The original unique becomes
% pinned by the uniquew.  This allows you to traverse a unique
% data structure for writing, without actually deleting and rebuilding
% nodes.n

Include "unique.g".

ResourceType uniquew with
  Define primitive consume_uniquew : Fun(A:type)(^#uniquew x:A).void
    := fun(A:type)(x:A).voidi <<END
  inline void gconsume_uniquew(int A, void *x) { }
END.

ResourceType pinned_unique with
  Define primitive consume_pinned_unique : Fun(A:type)(^#pinned_unique x:A).void
    := fun(A:type)(x:A).voidi <<END
  inline void gconsume_pinned_unique(int A, void *x) {
    gconsume_unique(A,x);
  }
END.

Init ginit_uniquew_unique(#uniquew x)(#unique y).#<uniquew x> <<END
  #define ginit_uniquew_unique(A,x,y) y
END.

Init ginit_unique_uniquew(#unique x)(#uniquew y).#uniquew <<END
  #define ginit_unique_uniquew(A,x,y) y
END.

Init ginit_unique_pinned_unique(#unique x)(#pinned_unique y).#pinned_unique <<END
  #define ginit_unique_pinned_unique(A,x,y) y
END.

Inductive get_uniquew_t : Fun(A:type).type :=
  mk_get_uniquew_t : Fun(A:type)(#pinned_unique aa : A)(#<uniquew aa> a : A).<get_uniquew_t A>.

Define primitive get_uniquew : Fun(A:type)(^ #unique a : A).#unique <get_uniquew_t A> :=
  fun(A:type)(a:A).(mk_get_uniquew_t A a a) <<END
  void *gget_uniquew(int A, void *a) {
    return gmk_get_uniquew_t(A,a,a);
  }
END.

Define primitive unpin_unique : Fun(A:type)(#pinned_unique aa : A).#unique A  <<END
  inline void *gunpin_unique(int A, void *aa) {
    return aa;
  }
END.

