Include "trm.g".

Define ctxte := <pair var trm>.

Define ctxtevar := (fst var trm).
Define ctxtetrm := (snd var trm).

Define ctxt := <list ctxte>.

Define ctxtc := fun(x:var)(T:trm). (cons ctxte (mkpair var trm x T)).
Define ctxtn := (nil ctxte).

Define ctxtc_tot := foralli(n:var)(T:trm)(l:ctxt).
                    existsi (cons ctxte (mkpair var trm n T) l)
                      { (ctxtc n T l) = *}
                      join (ctxtc n T l) (cons (mkpair n T) l).

Total ctxtc ctxtc_tot.

Define lookup := 
  fun lookup(x:var)(owned G:ctxt):<option trm>.
    match G with
      nil A => (nothing trm)
    | cons A a G' =>
      abbrev e = cast a by symm inj <list *> G_Eq in
      let n = (ctxtevar e) in
      match (eqvar n x) with
        ff => (lookup x cast G' by symm G_Eq)
      | tt => (something trm (ctxtetrm e))
      end 
    end.

Define bndtrm := 
  fun bndtrm(n:var)(t:trm):bool.
    match t with
      sym n' => (vlt n' n)
    | app t1 t2 => (and (bndtrm n t1) (bndtrm n t2))
    | lam n' t1 => (and (vlt n' n) (bndtrm n t1))
    | pi n' t1 t2 => (and (vlt n' n) (and (bndtrm n t1) (bndtrm n t2)))
    end.

Define bndopttrm := 
  fun(n:var)(o:<option trm>).
    match o with
      nothing A => tt
    | something A a => (bndtrm n cast a by symm inj <option *> o_Eq)
    end.

%- unused:
% return true iff all pi-bound vars are weakly lower-bounded by n.
Define lbndvars := 
  fun lbndvars(n:nat)(t:trm):bool.
    match t with
      sym n' => tt
    | app t1 t2 => (and (lbndvars n t1) (lbndvars n t2))
    | lam n' t1 => (lbndvars n t1)
    | pi n' t1 t2 => (and (le n n') (and (lbndvars n t1) (lbndvars n t2)))
    end.
-%

Define mctxt := ctxt.

Inductive msbst_t : type :=
  mk_msbst_t : Fun(nextid':var)(t:trm). msbst_t.

Define mctxtn := ctxtn.

Define mctxtc := ctxtc.

Define mlookup := lookup.

%-
Define mctxtc :=
  fun mctxtc(n:nat)(t:trm)(owned G:mctxt):mctxt.
    match n with
      Z =>
      match G with
        nil ign => (cons <option trm> (something trm t) (nil <option trm>))
      | cons ign x G' =>
          (cons <option trm> (something trm t) inc G')
      end
    | S n' =>
      match G with
        nil ign =>
          (cons <option trm> (nothing trm) (mctxtc n' t G))
      | cons ign x G' =>
          (cons <option trm> inc x (mctxtc n' t G'))
      end
    end.

Define mlookup :=
  fun mlookup(owned n:nat)(owned G:mctxt):<option trm>.
    match n with
      Z => match G with
             nil ign => (nothing trm)
           | cons ign x G' => inc x
           end
    | S n' =>
      match G with
        nil ign => (nothing trm)
      | cons ign x G' => (mlookup n' G')
      end
    end.
-%

% simultaneous substitution with beta-reduction.
Define msbst : Fun(nextid:var)(owned G:mctxt)(owned t2:trm).msbst_t :=
  fun msbst(nextid:var)(owned G:mctxt)(owned t2:trm)
          : msbst_t.
    match t2 with
      sym n' => 
      (mk_msbst_t nextid
        match (mlookup n' G) by ign l_Eq with
          nothing A => inc t2
        | something A a => cast a by symm inj <option *> l_Eq
        end)
    | app t2a t2b =>
        match (msbst nextid G t2a) by ign e1 with
          mk_msbst_t nextid' s1 =>
          match (msbst nextid' G t2b) by ign e2 with
            mk_msbst_t nextid'' s2 =>
              abbrev ret = (mk_msbst_t nextid'' (app s1 s2)) in
              match inc s1 with
                sym n1 => ret
              | app s1a s1b => dec s1a dec s1b ret
              | lam n1 s1a =>
                dec s1
                let G' = (mctxtc n1 s2 inc G) in
                let r = 
                  match (msbst nextid'' G' s1a) by ign e3 with
                  mk_msbst_t nextid''' s3 =>
                    (mk_msbst_t nextid''' s3)
                  end in
                dec G' dec s1a r
              | pi n1 s1a s1b => dec s1a dec s1b ret
              end
          end
        end
    | lam n' t2' => %abort <msbst_t nextid>
        let G' = (mctxtc n' (sym nextid) inc G) in
        match (vS nextid) with
          mk_word_inc_t nextid' carry =>
            match carry with
              ff => 
              let r = 
                match (msbst nextid' G' t2') with
                 mk_msbst_t nextid'' s1 =>
                  (mk_msbst_t nextid'' (lam nextid s1))
                 end in
              dec G' r
            | tt => abort msbst_t
            end
        end
    | pi n' t2a t2b => 
      match (vS nextid) with
        mk_word_inc_t nextid' carry =>
          match carry with
            ff => 
            match (msbst nextid' G t2a) by ign e1 with
              mk_msbst_t nextid'' s1 =>
              let G' = (mctxtc n' (sym nextid) inc G) in
              let r = 
                match (msbst nextid'' G' t2b) with
                  mk_msbst_t nextid''' s2 =>
                    (mk_msbst_t nextid''' (pi nextid s1 s2))
                end in
              dec G' r
            end
          | tt => abort msbst_t
          end
        end
    end.

Define sbst := fun(nextid:var)(t1:trm)(n:var)(owned t2:trm).
                 let G = (mctxtc n t1 inc mctxtn) in
                 match (msbst nextid G t2) with 
                   mk_msbst_t nextid' s => dec G s
                 end.
Define acanon := fun(nextid:var)(owned t:trm).
                 match (msbst nextid mctxtn t) with 
                   mk_msbst_t nextid' s => s
                 end.

Define free_in :=
  fun free_in(n:var)(owned t:trm):bool.
    match t with
      sym n' => (eqvar n n')
    | app t1 t2 => (or (free_in n t1) (free_in n t2))
    | lam n1 t1 => match (eqvar n n1) with
                     ff => (free_in n t1)
                   | tt => ff
                   end
    | pi n1 t1 t2 => 
        (or (free_in n t1) 
            match (eqvar n n1) with
              ff => (free_in n t2)
            | tt => ff
            end)
    end.

% well-formedness of the context is enforced using predicates defined below.
Inductive deriv : Fun(G:ctxt)(t T:trm).type :=
  dsym : Fun(G:ctxt)(n:var)(T:trm)(u:{ (lookup n G) = (something T) })(b:bool)
            (d1 : <deriv G T (sym (tpknd b))>). 
            <deriv G (sym n) T>
| dknd : Fun(G:ctxt)(n:var)(T:trm)(u:{ (lookup n G) = (something T) })
            (u1 : { T = (sym knd)}). 
            <deriv G (sym n) T>
| dapp : Fun(G:ctxt)(t1 t2:trm)(n:var)(T1 T2:trm)(m:var)
            (d1 : <deriv G t1 (pi n T1 T2)>)
            (d2 : <deriv G t2 T1>)
            (u1 : { (bndtrm m t2) = tt})
            (u2 : { (bndtrm m T2) = tt})
            (u3 : { (vlt n m) = tt}).
            <deriv G (app t1 t2) (sbst m t2 n T2)>
| dlam : Fun(G:ctxt)(t:trm)(n:var)(T1 T2:trm)
            (d1 : <deriv (ctxtc n T1 G) t T2>).
            <deriv G (lam n t) (pi n T1 T2)>
| dpi : Fun(G:ctxt)(n:var)(T1 T2:trm)(b:bool)
           (d1 : <deriv G T1 (sym tp)>)
           (d2 : <deriv (ctxtc n T1 G) T2 (sym (tpknd b))>).
           <deriv G (pi n T1 T2) (sym (tpknd b))>
| dconv : Fun(G:ctxt)(t T1 T2:trm)(m:var)
           (d1 : <deriv G t T1>)
           (u1 : { (bndtrm m T2) = tt})
           (u2 : { (acanon m T1) = (acanon m T2)}).
           <deriv G t T2>.

Define predicate diffids := fun(G:ctxt).
    Forall(G1 G2:ctxt)
          (n:var)(T:trm)
          (u:{ G = (append G1 (ctxtc n T G2)) }).
          { (lookup n G) = (something T) }.

Define predicate idsbnd1 := 
  fun(n:var)(G:ctxt).
    Forall(m:var)(T:trm)(G1 G2:ctxt)
          (u:{ G = (append G1 (ctxtc m T G2)) }).
       { (vlt m n) = tt }.

Define predicate idsbnd2 := 
  fun(n:var)(G:ctxt).
    Forall(m:var)(T:trm)(G1 G2:ctxt)
          (u:{ G = (append G1 (ctxtc m T G2)) }).
       { (bndtrm n T) = tt }.

% all trms occurring in the gs_ctxt are types or kinds.
Define predicate decsderiv :=
  fun(G:ctxt).
    Forall(n:var)(T:trm)(G1 G2:ctxt)
          (u : { G = (append G1 (ctxtc n T G2)) })
          (u2 : { T != (sym knd)}).
      Exists(b:bool)(x:<deriv (append ctxte G1 G2) T
                          (sym (tpknd b))>).
        True.    

