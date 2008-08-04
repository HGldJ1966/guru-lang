                          (tcheck_tt nextid symbols T2 
                            (pi nextid' t1 t2) T2
                            cast
                              (dpi G inc nextid' t1 t2 eTistp
                                 d1
                                 cast nd2
                                 by trans cong <deriv (ctxtc nextid' t1 *) t2 T2>
                                           symm [symctxt_nothing symbolsi]
                                          cong <deriv (ctxtc nextid' t1 G)
                                                 t2 *>
                                           PT2)
                            by cong <deriv G (pi nextid' t1 t2) *>
                                symm PT2 
                            bpi)
                         end %- match or -%
                      end %- match K2 -%
                    end %- match k2 -% in




                           abbrev bpi = 
                             hypjoin (bndtrm nextid'' (pi nextid' t1 t2)) tt
                             by Pnextid'
                               [bndtrm_le nextid' nextid'' t1 
                                 [lt_implies_le nextid' nextid'' Pnextid'] bt1]
                               bt2 end in


                  abbrev sym'ok = [symbols_ok_cong nextid symbols symbols' 
                                     symok U1] in
                  abbrev Plt1 = foralli(nextid'':nat)
                                       (nle:{ (le (S nextid') nextid'') = tt}).
                                 [ltle_trans nextid' (S nextid') nextid''
                                   [lt_S nextid'] nle] in
                  abbrev Ple = 
                    foralli(nextid'':nat)
                           (nle:{ (le (S nextid') nextid'') = tt}).
                     [lt_implies_le nextid nextid''
                        [lelt_trans nextid nextid' nextid'' 
                           nle1 [Plt1 nextid'' nle]]] in

                  % { (trie_lookup symbols' s) = oprev }
                  abbrev lookup' = [trie_lookup_same_interp symbols_e 
                                      symbols symbols' s oprev
                                      symm oprev_eq1 U1] in

                  match (check stdin inssymbols (S inc nextid') 
                           [symbols_ok_insert_next nextid' 
                              symbols' inssymbols s t1 
                              [symbols_ok_wk nextid nextid' symbols' 
                                 sym'ok nle1]
                              inssymbols_eq]
                           create
                           expected 
                           [bndopttrm_le nextid (S nextid') expected
                             [le_trans nextid nextid' (S nextid')
                                nle1 [le_S nextid']] 
                             bndexpected]
                           str_pi) by ign cdom1_Eq with
                    mk_check ign1 ign2 ign3 ign4 stdin symbols'' nextid'' 
                         sT2 k2 K2 nle2 U2 =>

                    let stdin = (eat_char stdin where Crp) in
                    abbrev P = [Ple nextid'' nle1] in
                    abbrev Pnextid' = [Plt1 nextid'' nle1] in

                    let k = 
                    match k2 with
                      tcheck_ff ign1 ign2 ign3 =>

                        cast (tcheck_ff nextid'' symbols'' sT2)
                        by cong <tcheck_t nextid'' symbols'' * sT2>
                             symm inj <tcheck_t ** ** * **> k2_Eq
                    | tcheck_tt ign1 ign2 ign3 t2 d2 bt2 =>       
                      existse_term 
                        [deriv_perm 
                           terminates (gs_ctxt inssymbols) by gs_ctxt_tot
                           t2 T2 G1 G2 nextid' t1 d2
                           inssymctxt]
                      fun(spec nd2:<deriv 
                                      (ctxtc nextid' t1 (append ctxte G1 G2))
                                      t2 T2>)
                         (ign:True).

                      match K2 with
                        tcheck_nothing ign1 T2 bT2 =>
                         abbrev T2istp = (istp T2) in
                         abbrev T2isknd = (isknd T2) in
                         match (or T2istp T2isknd) by T2istpknd ign with
                           ff => dec stdin dec symbols'' dec t1 dec nextid'
                                 dec s dec nextid'' dec oprev
                                 let ret = (range_err t2 T2) in
                                   dec t2 dec T2 ret
                         | tt =>
                           abbrev PT2 = [istpkndEq T2 T2istpknd] in
                           abbrev bpi = 
                             hypjoin (bndtrm nextid'' (pi nextid' t1 t2)) tt
                             by Pnextid'
                               [bndtrm_le nextid' nextid'' t1 
                                 [lt_implies_le nextid' nextid'' Pnextid'] bt1]
                               bt2 end in

                           (tcheck_tt nextid symbols T2 
                            (pi nextid' t1 t2) T2
                            cast
                              (dpi G inc nextid' t1 t2 T2istp
                                 d1
                                 cast nd2
                                 by trans cong <deriv (ctxtc nextid' t1 *) t2 T2>
                                           symm [symctxt_nothing symbolsi]
                                          cong <deriv (ctxtc nextid' t1 G)
                                                 t2 *>
                                           PT2)
                            by cong <deriv G (pi nextid' t1 t2) *>
                                symm PT2 
                            bpi)
                         end %- match or -%
                      end %- match K2 -%
                    end %- match k2 -% in



%-
% create, no expected type
                    
                    abbrev T2istp = (istp T2) in
                    abbrev T2isknd = (isknd T2) in
                    match (or T2istp T2isknd) by T2istpknd ign with
                      ff => dec stdin dec symbols'' dec t1 dec nextid'
                            dec s dec nextid'' dec oprev
                            let ret = (range_err t2 T2) in
                              dec t2 dec T2 ret
                    | tt =>
  -%                    


%-
                      abbrev PT2 = [istpkndEq T2 T2istpknd] in
                      abbrev bpi = 
                            hypjoin (bndtrm nextid'' (pi nextid' t1 t2)) tt
                            by Pnextid'
                               [bndtrm_le nextid' nextid'' t1 
                                 [lt_implies_le nextid' nextid'' Pnextid'] bt1]
                               bt2 end in


                      cast
                      match oprev with 
                        nothing A => 
                        let remsymbols = (trie_remove symbols_e s symbols'') in
                        dec s
                        abbrev symbolsi = trans U
                                   [trie_insert_new symbols_e symbols'
                                     inssymbols s 
                                     (mkpair nat trm nextid' t1)
                                     trans lookup' oprev_eq
                                     symm inssymbols_eq
                                     L1 L2 inssymi] in
                        abbrev remsymbolsi =
                          [trie_remove_interp symbols_e symbols'' remsymbols
                             s (mkpair nat trm nextid' t1) 
                             symm remsymbols_eq L1 L2
                             trans symm U1
                               trans cong (trie_interp *)
                                      symm inj <check_t * ** ** **> cdom1_Eq 
                                 inssymi] in
                        (mk_subcheck1 stdin symbols remsymbols nextid nextid'' 
                          (pi nextid' t1 t2) T2
                          cast
                            (dpi G inc nextid' t1 t2 T2istp
                               d1
                               cast nd2
                               by trans cong <deriv (ctxtc nextid' t1 *) t2 T2>
                                         symm [symctxt_nothing symbolsi]
                                        cong <deriv (ctxtc nextid' t1 G)
                                               t2 *>
                                         PT2)
                          by cong <deriv G
                                     (pi nextid' t1 t2) *>
                                symm PT2 
                          bpi bT2 P 
                          trans symbolsi symm remsymbolsi)
                      | something A prev =>  
                        let rsymbols = (trie_insert symbols_e s prev symbols'') in
                        abbrev symrsymi = trans U
                                   [trie_restore_interp symbols_e symbols'
                                     inssymbols symbols'' rsymbols s prev 
                                     (mkpair nat trm nextid' t1)
                                     trans lookup' oprev_eq
                                     symm inssymbols_eq
                                     U1 symm rsymbols_eq ] in
                        existse_term 
                          [deriv_wk1 G1' G2 prev t2 T2 
                              diffidsGG
                              cast nd2
                              by cong <deriv * t2 T2>
                                   join (ctxtc nextid' t1 (append G1 G2))
                                        (append (ctxtc nextid' t1 G1) G2)]
                        fun(spec nd2:<deriv GG t2 T2>)
                           (ign:True).
                        abbrev nd2' = 
                          cast nd2 by trans cong <deriv * t2 T2>
                                              join GG GG'
                                      trans cong <deriv (ctxtc nextid' t1 *) 
                                                    t2 T2>
                                              symm [symctxt_something prev oprev_eq]
                                            cong <deriv (ctxtc nextid' t1
                                                     G)
                                                  t2 *>
                                            PT2 in
                        (mk_subcheck1 stdin symbols rsymbols nextid nextid'' 
                          (pi nextid' t1 t2) T2
                          cast
                            (dpi G nextid' t1 t2 T2istp
                               d1
                               nd2')
                          by cong <deriv G
                                     (pi nextid' t1 t2) *>
                                symm PT2 
                          bpi bT2 P 
                          symrsymi)
                      end
                      by trans cong <check_t nextid symbols * nothing>
                                 symm inj <check_t ** ** * **> cdom1_Eq
                               cong <check_t nextid symbols create *>
                                 symm inj <check_t ** ** ** *> cdom1_Eq
-%
