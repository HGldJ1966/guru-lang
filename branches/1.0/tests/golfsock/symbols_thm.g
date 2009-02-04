Include "symbols.g".

Define symbols_lookup_dec :
  Forall(symbols:symbols_t)(s:string)(n:var)(T:trm)
        (u:{(trie_lookup symbols s) = (something (mkpair n T)) }).
    Exists(l1 l2:ctxt).
      { (gs_ctxt symbols) = (append l1 (ctxtc n T l2)) } :=
  foralli(symbols:symbols_t)(s:string)(n:var)(T:trm)
         (u:{(trie_lookup symbols s) = (something (mkpair n T)) }).
    existse [trie_lookup_interp symbols_e symbols s (mkpair var trm n T) u]
    foralli(L1 L2:<list <pair string symbols_e>>)
           (ut : { (trie_interp symbols) = 
                   (append L1 (cons (mkpair s (mkpair n T)) L2))}).
    abbrev hf = fun(u:Unit).(snd string symbols_e) in
    abbrev l1 = terminates 
                (map <pair string symbols_e> symbols_e
                   Unit unit hf L1)
                by trie_range_map_tot in
    abbrev l2 = terminates
                (map <pair string symbols_e> symbols_e
                   Unit unit hf L2)
                by trie_range_map_tot in
    abbrev ut = [trie_interp_range2 symbols_e symbols s (mkpair var trm n T) L1 L2
                   ut] in
    existsi l1
      Exists(l2:ctxt).
        { (gs_ctxt symbols) = (append * (ctxtc n T l2))}
    existsi l2 
        { (gs_ctxt symbols) = (append l1 (ctxtc n T *))}
    trans join (gs_ctxt symbols) (trie_range symbols)
    trans ut
          cong (append l1 *) join (cons (mkpair n T) l2) (ctxtc n T l2).

Define gs_ctxt_tot : Forall(symbols:symbols_t).Exists(G:ctxt).
                        { (gs_ctxt symbols) = G} := 
  foralli(symbols:symbols_t).
    abbrev G = terminates (trie_range ctxte symbols) by trie_range_tot in
    existsi G { (gs_ctxt symbols) = *}
      join (gs_ctxt symbols) G.


Define diffids_insert_next
 : Forall(n:var)(symbols symbols':symbols_t)
         (s:string)(t:trm)
         (n':var)
         (a:{(v2n n') = (S (v2n n))})
         (I1:@<diffids (gs_ctxt symbols)>)
         (I2:@<idsbnd1 n (gs_ctxt symbols)>)
         (u1:{ symbols' = (trie_insert s (mkpair n t) symbols)}).
     @<diffids (gs_ctxt symbols')> :=
  foralli(n:var)(symbols symbols':symbols_t)
         (s:string)(t:trm)
         (n':var)
         (a:{(v2n n') = (S (v2n n))})
         (I1:@<diffids (gs_ctxt symbols)>)
         (I2:@<idsbnd1 n (gs_ctxt symbols)>)
         (u1:{ symbols' = (trie_insert s (mkpair n t) symbols)}).

  %- begin proof of diffids -%
  foralli(l1' l2':<list symbols_e>)
         (n':var)
         (t':trm)
         (u2:{ (gs_ctxt symbols') = (append l1' (ctxtc n' t' l2')) }).
    abbrev e = (mkpair var trm n t) in
    existse [trie_insert_interp symbols_e symbols symbols' s e symm u1] 
    foralli(L1 L2 : <list <pair string symbols_e>>)
           (u3: { (trie_interp symbols') = (append L1 (cons (mkpair s (mkpair n t)) L2)) }).
      abbrev u3a = [trie_interp_range2 symbols_e symbols' s (mkpair var trm n t) 
                      L1 L2 u3] in
      abbrev l1 = (map <pair string symbols_e> symbols_e Unit unit fun(u:Unit). (snd string symbols_e) L1) in
      abbrev l2 = (map <pair string symbols_e> symbols_e Unit unit fun(u:Unit). (snd string symbols_e) L2) in
      abbrev len1 = (length symbols_e l1) in
      abbrev len1' = (length symbols_e l1') in
      case (lt len1' len1) by C1 ign with
        ff => 
        case (lt len1 len1') by C3 ign with
          ff => 
          abbrev C2 = hypjoin (eqnat len1 len1') tt
                      by C3 [lt_ff_implies_le len1' len1 C1] end in
          show C2 end
        | tt => truei
        end
      | tt => truei
      end.

Define trusted symbols_ok_insert_next
 : Forall(n:var)(symbols symbols':symbols_t)
         (s:string)(t:trm)
         (n':var)
         (a:{(v2n n') = (S (v2n n))})
         (symok:@<symbols_ok n symbols>)
         (u:{ symbols' = (trie_insert s (mkpair n t) symbols)}).
     @<symbols_ok n' symbols'> :=
  truei.

Define initial_symbols :=
  fun(u:Unit):unique symbols_t.
    (trie_insert symbols_e "type" 
        (mkpair var trm tp (sym knd))
        (trie_none symbols_e)).

Define first_id := match (word_inc tp) with
                   mk_word_inc_t n carry => n end.

%Set "debug_def_eq".

Define initial_symbols_ok 
  : @<symbols_ok first_id (initial_symbols unit)> := 
  abbrev G = (gs_ctxt (initial_symbols unit)) in
  abbrev V = (cons (mkpair tp (sym knd)) nil) in
  abbrev G_eq = join G V in
  abbrev P = 
    foralli(G1 G2:ctxt)
           (n:var)(T:trm)
           (u:{ G = (append G1 (ctxtc n T G2)) }).
    existse 
    [singleton_eq_append <pair word trm> (mkpair word trm tp (sym knd))
      (mkpair word trm n T) G1 G2
      trans symm G_eq 
          trans u
                cong (append G1 *) join (ctxtc n T G2) (cons (mkpair n T) G2)]
    foralli(u1:{G1 = nil})
           (u2:{ (mkpair tp (sym knd)) = (mkpair n T)})
           (u3:{G2 = nil}).
    andi symm inj (mkpair * **) u2
         symm inj (mkpair ** *) u2
   in
 andi foralli(G1 G2:ctxt)
             (n:var)(T:trm)
             (u:{ G = (append G1 (ctxtc n T G2)) }).
      existse [P G1 G2 n T u]
      foralli(n_eq:{ n = tp })
             (T_eq:{ T = (sym knd) }).
      trans cong (lookup * G) n_eq
      trans cong (lookup tp *) G_eq
      trans join (lookup tp V) (something (sym knd))
            cong (something *) symm T_eq 
 andi foralli(n:var)(T:trm)(G1 G2:ctxt)
             (u:{ G = (append G1 (ctxtc n T G2)) }).
      existse [P G1 G2 n T u]
      foralli(n_eq:{ n = tp })
             (T_eq:{ T = (sym knd) }).
      hypjoin (vlt n first_id) tt by n_eq end
 andi foralli(n:var)(T:trm)(G1 G2:ctxt)
             (u:{ G = (append G1 (ctxtc n T G2)) }).
      existse [P G1 G2 n T u]
      foralli(n_eq:{ n = tp })
             (T_eq:{ T = (sym knd) }).
      hypjoin (bndtrm first_id T) tt by T_eq end
 andi foralli(n:var)(T:trm)(G1 G2:ctxt)
             (u:{ G = (append G1 (ctxtc n T G2)) })
             (u2 : { T != (sym knd) }).
      existse [P G1 G2 n T u]
      foralli(n_eq:{ n = tp })
             (T_eq:{ T = (sym knd) }).
      contra
          trans symm T_eq u2
      Exists(b:bool)(x:<deriv (append ctxte G1 G2) T
                          (sym (tpknd b))>). True
 andi
      join (bndtrm first_id (sym tp)) tt
 truei
.

Define trusted symbols_ok_vle
  : Forall(n n':var)(symbols:symbols_t)
          (u1:@<symbols_ok n symbols>)
          (u2:{(vle n n') = tt}).
     @<symbols_ok n' symbols> := truei.

Define trusted symbols_ok_cong
  : Forall(n:var)(symbols symbols':symbols_t)(symok:@<symbols_ok n symbols>)
          (U : { (trie_interp symbols) = (trie_interp symbols')}).
     @<symbols_ok n symbols'> := truei.

Define symbols_ok_cont
  : Forall(n n':var)(symbols symbols':symbols_t)(symok:@<symbols_ok n symbols>)
          (u1:{ (trie_interp symbols) = (trie_interp symbols')})
          (u2:{ (vle n n') = tt}).
     @<symbols_ok n' symbols'> :=
  foralli(n n':var)(symbols symbols':symbols_t)(symok:@<symbols_ok n symbols>)
         (u1:{ (trie_interp symbols) = (trie_interp symbols')})
         (u2:{ (vle n n') = tt}).
   [symbols_ok_vle n n' symbols' 
      [symbols_ok_cong n symbols symbols'
          symok u1]
      u2].

Define gs_ctxt_interp
 : Forall(s1 s2:symbols_t)
         (u1:{ (trie_interp s1) = (trie_interp s2)}).
       { (gs_ctxt s1) = (gs_ctxt s2) } :=
 foralli(s1 s2:symbols_t)
        (u1:{ (trie_interp s1) = (trie_interp s2)}).
 hypjoin (gs_ctxt s1) (gs_ctxt s2)
 by [trie_interp_range1 symbols_e s1 s2 u1] end.