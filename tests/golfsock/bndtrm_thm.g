Define bndtrm_tot : Forall(n:var)(t:trm).Exists(r:bool).{(bndtrm n t) = r} :=
  foralli(n:var).
  induction(t:trm) return Exists(r:bool).{(bndtrm n t) = r} with
    sym n' => abbrev ret = terminates (vlt n' n) by vlt_total in
              existsi ret
                {(bndtrm n t) = *} 
                hypjoin (bndtrm n t) ret by t_eq end
  | app t1 t2 => 
    existse [t_IH t1]
    foralli(r1:bool)(ur1:{(bndtrm n t1) = r1}).
    existse [t_IH t2]
    foralli(r2:bool)(ur2:{(bndtrm n t2) = r2}).
      abbrev ret = (and r1 r2) in
        existsi ret
         {(bndtrm n t) = *} 
         hypjoin (bndtrm n t) ret by t_eq ur1 ur2 end
  | lam n' t1 => 
    existse [t_IH t1]
    foralli(r1:bool)(ur1:{(bndtrm n t1) = r1}).
      abbrev ret = (and (vlt n' n) r1) in
        existsi ret
         {(bndtrm n t) = *} 
         hypjoin (bndtrm n t) ret by t_eq ur1 end
  | pi n' t1 t2 => 
    existse [t_IH t1]
    foralli(r1:bool)(ur1:{(bndtrm n t1) = r1}).
    existse [t_IH t2]
    foralli(r2:bool)(ur2:{(bndtrm n t2) = r2}).
      abbrev ret = (and (vlt n' n) (and r1 r2)) in
        existsi ret
         {(bndtrm n t) = *} 
         hypjoin (bndtrm n t) ret by t_eq ur1 ur2 end
  end.

Total bndtrm bndtrm_tot.

Define bndmctxt := fun(m:var).
  (all ctxte Unit unit 
    fun(u:Unit)(owned o:<pair var trm>).
      match o with
        mkpair ign1 ign2 n t => (bndtrm m t)
      end).

Define bndmctxtc
 : Forall(n1 n2:var)(t:trm)
         (u:{(bndtrm n1 t) = tt}).
     {(bndmctxt n1 (mctxtc n2 t mctxtn)) = tt} := 
 foralli(n1 n2:var)(t:trm)
        (u:{(bndtrm n1 t) = tt}).
 hypjoin (bndmctxt n1 (mctxtc n2 t mctxtn)) tt
 by u end.

%-
Define trusted bndctxt_le
 : Forall(n m:nat)(G:ctxt)
         (u1:{(le n m) = tt})
         (u2:{(bndctxt n G) = tt}).
    { (bndctxt m G) = tt} := truei.
-%

Define trusted bndtrm_msbst
   : Forall(nextid:var)(G:mctxt)(t:trm)(nextid':var)(r:trm)
           (u1:{(bndmctxt nextid G) = tt})
           (u2:{(bndtrm nextid t) = tt})
           (u3:{(msbst nextid G t) = (mk_msbst_t nextid' r)}).
        { (bndtrm nextid' r) = tt } := truei.

Define bndtrm_app1 : Forall(n:var)(t t1 t2:trm)
                           (u1:{ (bndtrm n t) = tt })
                           (u2: { t = (app t1 t2) }).
                      { (bndtrm n t1) = tt } :=
  foralli(n:var)(t t1 t2:trm)
         (u1:{ (bndtrm n t) = tt })
         (u2: { t = (app t1 t2) }).
    abbrev b1 = terminates (bndtrm n t1) by bndtrm_tot in
    abbrev b2 = terminates (bndtrm n t2) by bndtrm_tot in
      [andtt_e1 b1 b2 hypjoin (and b1 b2) tt by u1 u2 end].

Define bndtrm_app2 : Forall(n:var)(t t1 t2:trm)
                           (u1:{ (bndtrm n t) = tt })
                           (u2: { t = (app t1 t2) }).
                      { (bndtrm n t2) = tt } :=
  foralli(n:var)(t t1 t2:trm)
         (u1:{ (bndtrm n t) = tt })
         (u2: { t = (app t1 t2) }).
    abbrev b1 = terminates (bndtrm n t1) by bndtrm_tot in
    abbrev b2 = terminates (bndtrm n t2) by bndtrm_tot in
      [andtt_e2 b1 b2 hypjoin (and b1 b2) tt by u1 u2 end].

Define bndtrm_lam1 : Forall(n:var)(t:trm)(n1:var)(t1:trm)
                          (u1:{ (bndtrm n t) = tt })
                          (u2: { t = (lam n1 t1) }).
                      { (vlt n1 n) = tt } :=
  foralli(n:var)(t:trm)(n1:var)(t1:trm)
         (u1:{ (bndtrm n t) = tt })
         (u2: { t = (lam n1 t1) }).
   abbrev b1 = terminates (vlt n1 n) by vlt_total in
   abbrev b2 = terminates (bndtrm n t1) by bndtrm_tot in
    [andtt_e1 b1 b2 hypjoin (and b1 b2) tt by u1 u2 end].

Define bndtrm_lam2 : Forall(n:var)(t:trm)(n1:var)(t1:trm)
                          (u1:{ (bndtrm n t) = tt })
                          (u2: { t = (lam n1 t1) }).
                      { (bndtrm n t1) = tt } :=
  foralli(n:var)(t:trm)(n1:var)(t1:trm)
         (u1:{ (bndtrm n t) = tt })
         (u2: { t = (lam n1 t1) }).
   abbrev b1 = terminates (vlt n1 n) by vlt_total in
   abbrev b2 = terminates (bndtrm n t1) by bndtrm_tot in
    [andtt_e2 b1 b2 hypjoin (and b1 b2) tt by u1 u2 end].

Define bndtrm_pi1 : Forall(n:var)(t:trm)(n1:var)(t1 t2:trm)
                          (u1:{ (bndtrm n t) = tt })
                          (u2: { t = (pi n1 t1 t2) }).
                      { (vlt n1 n) = tt } :=
  foralli(n:var)(t:trm)(n1:var)(t1 t2:trm)
         (u1:{ (bndtrm n t) = tt })
         (u2: { t = (pi n1 t1 t2) }).
   abbrev b1 = (vlt n1 n) in
   abbrev b2 = (bndtrm n t1) in
   abbrev b3 = (bndtrm n t2) in
   abbrev b4 = (and b2 b3) in
    [andtt_e1 b1 b4 hypjoin (and b1 b4) tt by u1 u2 end].

Define bndtrm_pi2 : Forall(n:var)(t:trm)(n1:var)(t1 t2:trm)
                          (u1:{ (bndtrm n t) = tt })
                          (u2: { t = (pi n1 t1 t2) }).
                      { (bndtrm n t1) = tt } :=
  foralli(n:var)(t:trm)(n1:var)(t1 t2:trm)
         (u1:{ (bndtrm n t) = tt })
         (u2: { t = (pi n1 t1 t2) }).
   abbrev b1 = (vlt n1 n) in
   abbrev b2 = (bndtrm n t1) in
   abbrev b3 = (bndtrm n t2) in
   abbrev b4 = (and b2 b3) in
    [andtt_e1 b2 b3 [andtt_e2 b1 b4 hypjoin (and b1 b4) tt by u1 u2 end]].

Define bndtrm_pi3 : Forall(n:var)(t:trm)(n1:var)(t1 t2:trm)
                          (u1:{ (bndtrm n t) = tt })
                          (u2: { t = (pi n1 t1 t2) }).
                      { (bndtrm n t2) = tt } :=
  foralli(n:var)(t:trm)(n1:var)(t1 t2:trm)
         (u1:{ (bndtrm n t) = tt })
         (u2: { t = (pi n1 t1 t2) }).
   abbrev b1 = (vlt n1 n) in
   abbrev b2 = (bndtrm n t1) in
   abbrev b3 = (bndtrm n t2) in
   abbrev b4 = (and b2 b3) in
    [andtt_e2 b2 b3 [andtt_e2 b1 b4 hypjoin (and b1 b4) tt by u1 u2 end]].

Define bndtrm_vle
   : Forall(n m:var)(t:trm)
           (u1:{(vle n m) = tt})
           (u2:{(bndtrm n t) = tt}).
      { (bndtrm m t) = tt} := 
  foralli(n m:var).
    induction(t:trm) return Forall(u1:{(vle n m) = tt})
                                  (u2:{(bndtrm n t) = tt}).
                             { (bndtrm m t) = tt} with
      sym n' =>
        foralli(u1:{(vle n m) = tt})
               (u2:{(bndtrm n t) = tt}). 
          hypjoin (bndtrm m t) tt
          by t_eq
             [vltle_trans n' n m
               hypjoin (vlt n' n) tt
                 by u2 t_eq end
               u1]
          end
    | app t1 t2 => 
      foralli(u1:{(vle n m) = tt})
             (u2:{(bndtrm n t) = tt}). 
        hypjoin (bndtrm m t) tt
        by t_eq
           [t_IH t1 u1 [bndtrm_app1 n t t1 t2 u2 t_eq]]
           [t_IH t2 u1 [bndtrm_app2 n t t1 t2 u2 t_eq]]
        end
                   
    | lam n1 t1 => 
      foralli(u1:{(vle n m) = tt})
             (u2:{(bndtrm n t) = tt}). 
        hypjoin (bndtrm m t) tt
        by t_eq
           [vltle_trans n1 n m [bndtrm_lam1 n t n1 t1 u2 t_eq] u1]
           [t_IH t1 u1 [bndtrm_lam2 n t n1 t1 u2 t_eq]]
        end
      
    | pi n1 t1 t2 => 
      foralli(u1:{(vle n m) = tt})
             (u2:{(bndtrm n t) = tt}). 
        hypjoin (bndtrm m t) tt
        by t_eq
           [vltle_trans n1 n m [bndtrm_pi1 n t n1 t1 t2 u2 t_eq] u1]
           [t_IH t1 u1 [bndtrm_pi2 n t n1 t1 t2 u2 t_eq]]
           [t_IH t2 u1 [bndtrm_pi3 n t n1 t1 t2 u2 t_eq]]
        end
    end.

Define bndopttrm_vle :
  Forall(n m:var)(o:<option trm>)
        (u1:{(vle n m) = tt})
        (u2:{(bndopttrm n o) = tt}).
      { (bndopttrm m o) = tt} := 
  foralli(n m:var)(o:<option trm>)
         (u1:{(vle n m) = tt})
         (u2:{(bndopttrm n o) = tt}).
    case o with
      nothing ign => hypjoin (bndopttrm m o) tt by o_eq end
    | something ign t => 
      hypjoin (bndopttrm m o) tt 
      by o_eq [bndtrm_vle n m t u1 hypjoin (bndtrm n t) tt by u2 o_eq end]
      end
    end.  

%-
Define trusted bndtrm_csbst_nextid 
  : Forall(nextid:nat)(G:ctxt)(t:trm)
          (u1: {(bndtrm nextid t) = tt})
          (u2: {(bndctxt nextid G) = tt}).
     { (bndtrm (csbst_nextid nextid G t) (csbst nextid G t)) = tt } :=
truei.
-%