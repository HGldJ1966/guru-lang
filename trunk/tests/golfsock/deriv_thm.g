Include "deriv.g".

Define trusted deriv_wk
  : Forall(G1 G2:ctxt)(n:var)(Tn t T:trm).
    abbrev G = (append ctxte G1 (ctxtc n Tn G2)) in
    Forall(u1:@<diffids G>)
          (d:<deriv (append ctxte G1 G2) t T>).
      Exists(d2:<deriv G t T>). True :=
  truei.

Define trusted deriv_wk1
  : Forall(G1 G2:ctxt)(e:ctxte)(t T:trm).
    abbrev G = (append ctxte G1 (cons ctxte e G2)) in
    Forall(u1:@<diffids G>)
          (d:<deriv (append ctxte G1 G2) t T>).
      Exists(d2:<deriv G t T>). True :=
  truei.

Define trusted deriv_perm
 : Forall(G:ctxt)(t T:trm)(G1 G2:ctxt)(n:var)(T':trm)
         (d : <deriv G t T>)
         (u : { G = (append G1 (ctxtc n T' G2)) }).
    Exists(d' : <deriv (ctxtc n T' (append ctxte G1 G2)) t T>). True :=
   truei.

Define cong_diffids : Forall(G G':ctxt)
                            (u1:@<diffids G>)
                            (u2: { G = G'}).
                        @<diffids G'> :=
  foralli(G G':ctxt)
         (u1:@<diffids G>)
         (u2: { G = G'}).
   foralli(G1 G2:ctxt)
          (n:var)(T:trm)
          (u:{ G' = (append G1 (ctxtc n T G2)) }).
     trans cong (lookup n *) symm u2
       [u1 G1 G2 n T trans u2 u].

Define trusted idsbnd1_vle : Forall(n n':var)(G:ctxt)
                            (u1:@<idsbnd1 n G>)
                            (u2: { (vle n n') = tt}).
                        @<idsbnd1 n' G> := truei.

Define trusted cong_idsbnd1 : Forall(n:var)(G G':ctxt)
                            (u1:@<idsbnd1 n G>)
                            (u2: { G = G'}).
                        @<idsbnd1 n G'> := truei.

Define trusted diffids_wk
  : Forall(G:ctxt)(n:var)(T:trm)
          (u1:@<diffids G>)
          (u2:@<idsbnd1 n G>).
     @<diffids (ctxtc n T G)> := truei.          

Define trusted msbst_vle
   : Forall(nextid:var)(G:mctxt)(t:trm)(nextid':var)(r:trm)
           (u3:{(msbst nextid G t) = (mk_msbst_t nextid' r)}).
        { (vle nextid nextid') = tt } := truei.

Define trusted dapp_simple
  : Forall(n:var)(dom ran:trm)(G:ctxt)(t1 t2:trm)
          (u : { (free_in n ran) = ff})
          (d1 : <deriv G t1 (pi n dom ran)>)
          (d2 : <deriv G t2 dom>).
     Exists(d: <deriv G (app t1 t2) ran>). True := truei.

Define trusted acanon_rename_pi 
  : Forall(nextid n1 n2:var)
          (dom ran1 ran2:trm).
      { (acanon nextid (pi n1 dom ran1)) = (acanon nextid (pi n2 dom ran2))} :=
  truei.

