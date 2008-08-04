
%-
Define trusted sbst_not_free 
  : Forall(nextid:var)(t1:trm)(n:var)(t2:trm)
          (u1 : { (free_in n t2) = ff }).
       { (sbst nextid t1 n t2) = (acanon nextid t2)} := truei.

Define sbst_nextid :=
   fun(nextid:nat)(t1:trm)(n:nat)(owned t2:trm).
     let G = (ctxtc n t1 inc ctxtn) in
     match (msbst nextid G t2) with 
       mk_msbst_t nextid' s => dec G dec s nextid'
     end.

Define csbst := fun(nextid:nat)(owned G:ctxt)(owned t2:trm).
                 match (msbst nextid G t2) with 
                   mk_msbst_t nextid' s => dec nextid' s
                 end.
Define csbst_nextid :=
   fun(nextid:nat)(owned G:ctxt)(owned t2:trm).
     match (msbst nextid G t2) with 
       mk_msbst_t nextid' s => dec s nextid'
     end.


Define trusted acanon_csbst 
 : Forall(nextid:nat)(sG:ctxt)(t:trm).
      { (csbst nextid sG t) = (acanon nextid (csbst nextid sG t)) } :=
 truei.

Define trusted csbst_nextid_le
 : Forall(nextid:nat)(G:ctxt)(t:trm)(nextid':nat)
         (u:{(csbst_nextid nextid G t) = nextid'}).
    {(le nextid nextid') = tt} :=
 truei.

Define trusted acanon_idem
 : Forall(nextid nextid':nat)(t:trm)
         (u1:{(bndtrm nextid t) = tt})
         (u2:{(le nextid nextid') = tt}).
     { (acanon nextid' (acanon nextid t)) = (acanon nextid' t)} :=
  truei.

Define trusted cong_acanon_le 
 : Forall(nextid nextid':nat)(t1 t2:trm)
         (u1:{(le nextid nextid') = tt})
         (u2:{(bndtrm nextid t1) = tt})
         (u3:{(bndtrm nextid t2) = tt})
         (u4:{(acanon nextid t1) = (acanon nextid t2)}).
    { (acanon nextid' t1) = (acanon nextid' t2) } :=
  truei.
-%