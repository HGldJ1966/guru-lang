Include "uniquew.g".
Include "unique_owned.g".

Inductive ref : Fun(A:type).type :=
  mk_ref : Fun(A:type)(#unowned a:A).#unique <ref A>.

Define primitive read_ref : Fun(spec A:type)(^ #unique_owned r:<ref A>).#unowned A :=
  fun(A:type)(r:<ref A>).
    match r with
      mk_ref _ a => cast a by inj <ref *> symm r_Eq
    end <<END

  inline void *gread_ref(void *r) {
    return select_ref_mk_ref_a(r);
  }
END.
  
Define primitive write_ref : Fun(A:type)(#unowned a:A)(! #pinned_unique aa:<ref A>)(#<uniquew aa> r:<ref A>).#<uniquew aa> <ref A> :=
  fun(A:type)(a:A)(aa:<ref A>)(r:<ref A>).
    (mk_ref A a) <<END

  inline void *gwrite_ref(int A, void *a, void *aa, void *r) {
    void **tmp = &select_ref_mk_ref_a(r);
    gdec(A,*tmp);
    *tmp = a;
    ginc(a);
    return r;
  }
END.
  