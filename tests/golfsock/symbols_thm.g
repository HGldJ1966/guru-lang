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
    abbrev l1 = (map <pair string symbols_e> symbols_e
                   Unit unit
                   fun(u:Unit).(snd string symbols_e) L1) in
    abbrev l2 = (map <pair string symbols_e> symbols_e
                   Unit unit
                   fun(u:Unit).(snd string symbols_e) L2) in
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

Define trusted gs_ctxt_tot : Forall(symbols:symbols_t).Exists(G:ctxt).
                              { (gs_ctxt symbols) = G} := truei.

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

Define trusted initial_symbols_ok 
  : @<symbols_ok first_id (initial_symbols unit)> := truei.

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