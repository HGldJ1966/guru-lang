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

Define trusted diffids_wk1
  : Forall(G1 G2:ctxt)(v:var)(T':trm).
    abbrev G = (append ctxte G1 G2) in
    abbrev G' = (append ctxte G1 (ctxtc v T' G2)) in
    Forall(u1:@<diffids G>)
          (u2:@<idsbnd1 v G>).
      @<diffids G'> := truei.

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

Define lookup_strengthen
  : Forall(n n':var)(T:trm)(G1 G2:ctxt)
          (u1 : { (vlt n n') = tt }) .
        { (lookup n (append G1 G2)) = (lookup n (append G1 (ctxtc n' T G2))) } := 
  foralli(n n':var)(T:trm)(G1 G2:ctxt)
         (u1 : { (vlt n n') = tt }).
    [induction(G1:ctxt) 
     return { (lookup n (append G1 G2)) = (lookup n (append G1 (ctxtc n' T G2))) } with
       nil _ => 
           hypjoin (lookup n (append G1 G2)) (lookup n (append G1 (ctxtc n' T G2)))
           by G1_eq [to_nat_neq wordlen n' n
                       [neqEqnat (v2n n') (v2n n)
                           symm
                           [lt_implies_neq (v2n n) (v2n n') 
                               hypjoin (lt (v2n n) (v2n n')) tt by u1 end]]] end
     | cons _ a' G1' => 
         case a' with
           mkpair _ _ m T' =>
           case (eqvar m n) by u2 ign with
             ff => 
             hypjoin (lookup n (append G1 G2)) (lookup n (append G1 (ctxtc n' T G2)))
             by a'_eq G1_eq u2 [G1_IH G1'] end
           | tt => 
             hypjoin (lookup n (append G1 G2)) (lookup n (append G1 (ctxtc n' T G2)))
             by a'_eq G1_eq u2 end
           end
         end
     end
     G1].
      
