Include "../../lib/trie.g".
Include "deriv.g".

Define symbols_e := <pair var trm>.

Define symbolsevar := (fst var trm).
Define symbolsetp := (snd var trm).

Define symbols_t := <trie symbols_e>.

% return a list of the declarations for identifiers from the range of symbols.
Define gs_ctxt : Fun(unique_owned symbols:symbols_t).ctxt :=
  (trie_range symbols_e).

Total gs_ctxt 
  foralli(symbols:symbols_t). [trie_range_tot symbols_e symbols].

Define predicate symbols_ok :=
  fun(n:var)(symbols:symbols_t).
    Exists(I1 : @<diffids (gs_ctxt symbols)>)
          (I2 : @<idsbnd1 n (gs_ctxt symbols)>)
          (I3 : @<idsbnd2 n (gs_ctxt symbols)>)
          (I4 : @<decsderiv (gs_ctxt symbols)>)
          (I5 : { (bndtrm n (sym tp)) = tt}).
      True.

