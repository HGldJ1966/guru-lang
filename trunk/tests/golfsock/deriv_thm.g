Include "deriv.g".

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

Define trusted lookup_perm
 : Forall(G:ctxt)(m:var)(T:trm)(G0 G1 G2:ctxt)(n:var)(T':trm)
         (u1 : { (lookup n G1) = nothing })
         (u2 : { G = (append G0 (append G1 (ctxtc n T' G2))) })
         (u3 : { (lookup m G) = (something T)}).
   { (lookup m (append G0 (ctxtc n T' (append G1 G2)))) = (something T) } := truei.

%Set "comment_vars".

Define deriv_perm_h
 : Forall(G:ctxt)(t T:trm)(G0 G1 G2:ctxt)(n:var)(T':trm)
         (u1 : { (lookup n G1) = nothing })               %- this assumption u1 could be more
                                                             general, but this is all we need. -%
         % G0 can shadow other variables.
         (u2 : { G = (append G0 (append G1 (ctxtc n T' G2))) })
         (d : <deriv G t T>).
    Exists(d' : <deriv (append ctxte G0 (ctxtc n T' (append ctxte G1 G2))) t T>). True :=
 induction(G:ctxt)(t T:trm)(G0 G1 G2:ctxt)(n:var)(T':trm)
          (u1 : { (lookup n G1) = nothing })
          (G_eq : { G = (append G0 (append G1 (ctxtc n T' G2))) })
          (d : <deriv G t T>)
 return Exists(d' : <deriv (append ctxte G0 (ctxtc n T' (append ctxte G1 G2))) t T>). True
 with
   dsym ign1 m ign2 u2 b d1 =>
    abbrev G' = (append ctxte G0 (ctxtc n T' (append ctxte G1 G2))) in
    existse [d_IH G T (sym (tpknd b)) G0 G1 G2 n T' u1 G_eq d1]
    foralli(d1' : <deriv G' T (sym (tpknd b))>)
           (ign : True).
    existsi
      cast (dsym G' m T
             [lookup_perm G m T G0 G1 G2 n T' u1 G_eq u2] b d1')
      by cong <deriv G' * T> 
          symm inj <deriv ** * **> d_Eq
    True truei 
 | dknd ign1 m ign2 u2 u3 => 
    abbrev G' = (append ctxte G0 (ctxtc n T' (append ctxte G1 G2))) in
    existsi
      cast (dknd G' m T
             [lookup_perm G m T G0 G1 G2 n T' u1 G_eq u2] u3)
      by cong <deriv G' * T> 
          symm inj <deriv ** * **> d_Eq
    True truei
 | dapp ign1 t1 t2 n1 T1 T2 m d1 d2 u2 u3 u4 => 
    abbrev G' = (append ctxte G0 (ctxtc n T' (append ctxte G1 G2))) in
    existse [d_IH G t1 (pi n1 T1 T2) G0 G1 G2 n T' u1 G_eq d1]
    foralli(d1' : <deriv G' t1 (pi n1 T1 T2)>)
           (ign : True).
    existse [d_IH G t2 T1 G0 G1 G2 n T' u1 G_eq d2]
    foralli(d2' : <deriv G' t2 T1>)
           (ign : True).
    existsi
     cast (dapp G' t1 t2 n1 T1 T2 m d1' d2' u2 u3 u4)
     by trans cong <deriv G' * (sbst m t2 n1 T2)>
                symm inj <deriv ** * **> d_Eq
              cong <deriv G' t *>
                symm inj <deriv ** ** *> d_Eq
    True truei
 | dlam ign1 t1 n1 T1 T2 d1 => 
    abbrev G' = (append ctxte G0 (ctxtc n T' (append ctxte G1 G2))) in
    abbrev iG = (append ctxte (ctxtc n1 T1 G0)
                  (append ctxte G1 (ctxtc n T' G2))) in
    abbrev iG' = (append ctxte (ctxtc n1 T1 G0)
                  (ctxtc n T' (append ctxte G1 G2))) in
    existse [d_IH iG t1 T2 (ctxtc n1 T1 G0) G1 G2 n T' u1 join iG iG 
              cast d1
              by cong <deriv * t1 T2>
                 hypjoin (ctxtc n1 T1 G)
                         (append (ctxtc n1 T1 G0) (append G1 (ctxtc n T' G2)))
                 by G_eq end]
    foralli(d1' : <deriv iG' t1 T2>)
           (ign : True).
    existsi
     cast (dlam G' t1 n1 T1 T2 
            cast d1'
            by cong <deriv * t1 T2>
                join (append (ctxtc n1 T1 G0) (ctxtc n T' (append G1 G2)))
                     (ctxtc n1 T1 (append G0 (ctxtc n T' (append G1 G2)))))
     by trans cong <deriv G' * (pi n1 T1 T2)>
                symm inj <deriv ** * **> d_Eq
              cong <deriv G' t *>
                symm inj <deriv ** ** *> d_Eq
    True truei
 | dpi ign1 n1 T1 T2 b d1 d2 => 
    abbrev G' = (append ctxte G0 (ctxtc n T' (append ctxte G1 G2))) in
    abbrev iG = (append ctxte (ctxtc n1 T1 G0)
                  (append ctxte G1 (ctxtc n T' G2))) in
    abbrev iG' = (append ctxte (ctxtc n1 T1 G0)
                  (ctxtc n T' (append ctxte G1 G2))) in
    existse [d_IH G T1 (sym tp) G0 G1 G2 n T' u1 G_eq d1]
    foralli(d1' : <deriv G' T1 (sym tp)>)
           (ign : True).
    existse [d_IH iG T2 (sym (tpknd b)) (ctxtc n1 T1 G0) G1 G2 n T' u1 join iG iG 
              cast d2
              by cong <deriv * T2 (sym (tpknd b))>
                 hypjoin (ctxtc n1 T1 G)
                         (append (ctxtc n1 T1 G0) (append G1 (ctxtc n T' G2)))
                 by G_eq end]
    foralli(d2' : <deriv iG' T2 (sym (tpknd b))>)
           (ign : True).
    existsi
     cast (dpi G' n1 T1 T2 b d1'
            cast d2'
            by cong <deriv * T2 (sym (tpknd b))>
                join (append (ctxtc n1 T1 G0) (ctxtc n T' (append G1 G2)))
                     (ctxtc n1 T1 (append G0 (ctxtc n T' (append G1 G2)))))
     by trans cong <deriv G' * (sym (tpknd b))>
                symm inj <deriv ** * **> d_Eq
              cong <deriv G' t *>
                symm inj <deriv ** ** *> d_Eq
    True truei
 | dconv ign1 ign2 T1 ign3 m d1 u2 u3 => 
    abbrev G' = (append ctxte G0 (ctxtc n T' (append ctxte G1 G2))) in
    existse [d_IH G t T1 G0 G1 G2 n T' u1 G_eq d1]
    foralli(d1' : <deriv G' t T1>)
           (ign : True).
    existsi (dconv G' t T1 T m d1' u2 u3) True truei
 end.

Define deriv_perm
 : Forall(G:ctxt)(t T:trm)(G1 G2:ctxt)(n:var)(T':trm)
         (u1 : { (lookup n G1) = nothing })
         (u2 : { G = (append G1 (ctxtc n T' G2)) })
         (d : <deriv G t T>).
    Exists(d' : <deriv (ctxtc n T' (append ctxte G1 G2)) t T>). True :=
 foralli(G:ctxt)(t T:trm)(G1 G2:ctxt)(n:var)(T':trm)
        (u1 : { (lookup n G1) = nothing })
        (u2 : { G = (append G1 (ctxtc n T' G2)) })
        (d : <deriv G t T>).
   abbrev nnG = (append ctxte G1 (ctxtc n T' G2)) in
   abbrev nG = (append ctxte ctxtn nnG) in
   abbrev G_eq = trans u2 join (append G1 (ctxtc n T' G2)) nG in
   existse
     [deriv_perm_h nG t T ctxtn G1 G2 n T' u1
        join nG nG cast d by cong <deriv * t T> G_eq]
   foralli(d' : <deriv (append ctxte ctxtn 
                          (ctxtc n T' (append ctxte G1 G2))) t T>)
          (ign : True).
    existsi cast d' by cong <deriv * t T> 
                         join (append ctxtn (ctxtc n T' (append G1 G2)))
                              (ctxtc n T' (append G1 G2))
    True truei.

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

Define trusted idsbnd1_lookup_nothing 
  : Forall(n:var)(G:ctxt)(u:@<idsbnd1 n G>).
     { (lookup n G) = nothing } := truei.

Define trusted lookup_nothing_append1 
  : Forall(n:var)(G1 G2:ctxt)(u : { (lookup n (append G1 G2)) = nothing }).
     { (lookup n G1) = nothing } := truei.