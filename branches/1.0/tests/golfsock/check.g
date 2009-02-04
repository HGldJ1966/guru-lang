
Include trusted "deriv_thm.g".

Include "symbols_thm.g".
%Include trusted "bndtrm_thm.g".
Include "bndtrm_thm.g".
Include "gs_io.g".
Include "checkh.g".

Inductive tcheck_t : Fun(nextid:var)(symbols:symbols_t)
                        (create:bool)(T:trm).type :=
  tcheck_ff : Fun(spec nextid:var)
                 (spec symbols:symbols_t)
                 (spec T:trm).
                 <tcheck_t nextid symbols ff T>
| tcheck_tt : Fun(spec nextid:var)
                 (spec symbols:symbols_t)
                 (spec T:trm)
                 (t:trm)
                 (spec d:<deriv (gs_ctxt symbols) t T>)
                 (bt : { (bndtrm nextid t) = tt}).
                 <tcheck_t nextid symbols tt T>.

Inductive Tcheck_t : Fun(nextid:var)
                        (expected:<option trm>)
                        (T:trm).type :=
  Tcheck_nothing : Fun(spec nextid:var)
                      (T:trm)
                      (bT:{(bndtrm nextid T) = tt}).
                     <Tcheck_t nextid (nothing trm) T>
| Tcheck_something : Fun(spec nextid:var)
                        (spec T eT:trm)
                        (spec nextid':var)
                        (nle:{(vle nextid nextid') = tt})
                        (u : { (acanon nextid' T) = (acanon nextid' eT)}).
                      <Tcheck_t nextid (something trm eT) T>.

Inductive check_t : Fun(nextid:var)(symbols:symbols_t)
                       (create:bool)(expected:<option trm>).type :=
  mk_check : Fun(spec nextid:var)(spec symbols:symbols_t)
                (spec create:bool)(spec expected:<option trm>)
                (unique pb_stdin:pb_stdin_t)
                (unique symbols':symbols_t)
                (nextid':var)
                (spec T:trm)
                (k:<tcheck_t nextid' symbols create T>)
                (K:<Tcheck_t nextid' expected T>)
                (nle : { (vle nextid nextid') = tt })
                (U : { (trie_interp symbols) = (trie_interp symbols')}).

                <check_t nextid symbols create expected>.

Define check : Fun(unique pb_stdin:pb_stdin_t)(unique symbols:symbols_t)
                  (nextid:var)
                  (spec symok:@<symbols_ok nextid symbols>)
                  (create:bool)
                  (expected:<option trm>)
                  (bndexpected:{(bndopttrm nextid expected) = tt})
                  (owned where:string).
                  unique <check_t nextid symbols create expected> :=
  fun check(unique pb_stdin:pb_stdin_t)
           (unique symbols:symbols_t)
           (nextid:var)
           (spec symok:@<symbols_ok nextid symbols>)
           (create:bool)
           (expected:<option trm>)
           (bndexpected:{(bndopttrm nextid expected) = tt})
           (owned where:string)
         :unique <check_t nextid symbols create expected>.
  abbrev G = (gs_ctxt symbols) in
  existse_term symok
  fun(I1 : @<diffids G>)
     (I2 : @<idsbnd1 nextid G>)
     (I3 : @<idsbnd2 nextid G>)
     (I4 : @<decsderiv G>)
     (I5 : { (bndtrm nextid (sym tp)) = tt})
     (ign : True).
    match (gs_char pb_stdin) with
      getc_none ign pb_stdin => 
         dec pb_stdin dec expected 
         let r = 
         (handle_error_sym_unique <check_t nextid symbols create expected>
           symbols
           (string_app "Unexpected end of input parsing a " inc where)) in
         dec symbols r
    | getc_char ign c pb_stdin =>
      match (eqchar c Clp) with
        ff => 

	%
	% parse a symbol 
	%

        match (gs_get_chars pb_stdin str_symbol 
                tt %- in_symbol -% ff %- disallow_empty -%) with
         mk_gs_get_chars pb_stdin s =>
         let s = (stringc c s) in
         match (trie_lookup symbols_e symbols s) by ls_eq ls_Eq with
           nothing ign => 

  	     % could not find the symbol in symbols.

             dec pb_stdin dec expected 
             let r =
             (handle_error_sym_unique <check_t nextid symbols create expected>
                symbols
                (string_app "Encountered an undeclared identifier while"
                (string_app (string_app " parsing a " inc where) 
                (string_appnl "1. the identifier: " s)))) in
             dec symbols r
         | something ign e =>

             % we found the symbol in symbols

             match e with
               mkpair ign1 ign2 n T =>
                 existse_term 
                    [symbols_lookup_dec symbols s n T
                       trans ls_eq
                             cong (something *) e_eq]
                 fun(spec l1 l2:ctxt)
                    (ud : {G = (append l1 (ctxtc n T l2)) }).
                 abbrev G' = (append ctxte l1 l2) in
                 abbrev G'' = (append ctxte l1 (ctxtc n T l2)) in
                 abbrev bndT = [I3 n T l1 l2 ud] in
                 abbrev bndn = hypjoin (bndtrm nextid (sym n)) tt
                               by [I2 n T l1 l2 ud] end in
                 let k = 
                 match create with
                   ff => cast (tcheck_ff nextid symbols T)
                         by cong <tcheck_t nextid symbols * T>
                              symm create_eq
                 | tt => 
                     % get the derivation for G |- n : T
                     match (eqtrm T knde) by nT ign with
                     ff =>
                       abbrev nTa = [neqtrm_neq T (sym knd) nT] in
                       existse_term [I4 n T l1 l2 ud nTa]
                         fun(spec b:bool)
                            (spec x:<deriv G' T (sym (tpknd b))>)
                            (ign : True).
                       existse_term
                         [deriv_wk l1 l2 n T T 
                           (sym (tpknd b))
                           [cong_diffids G G'' I1 hypjoin G G'' by ud end]
                           x]
                         fun(spec x':<deriv G'' T (sym (tpknd b))>)
                            (ign:True).
                     cast
                       (tcheck_tt nextid symbols T (sym n) 
                          (dsym G n T [I1 l1 l2 n T ud] b 
                            cast x'
                            by cong <deriv * T (sym (tpknd b))> 
                                 symm ud)
                          bndn)
                     by cong <tcheck_t nextid symbols * T>
                              symm create_eq
                     | tt => 
                       abbrev nTa = [eqtrm_eq T (sym knd) nT] in
                       cast
                       (tcheck_tt nextid symbols T (sym n) 
                          (dknd G n T [I1 l1 l2 n T ud] nTa)
                          bndn)
                     by cong <tcheck_t nextid symbols * T>
                              symm create_eq
                     end
                  end in

                  let K = 
                    match expected with
                      nothing ign =>
                      dec s
                      cast
                        (Tcheck_nothing nextid T bndT)
                      by cong <Tcheck_t nextid * T>
                           symm expected_eq
                    | something ign eT =>
                       match (aequiv nextid T eT) by ae ign with
                         ff =>
                         let r = 
                         (handle_error_sym
                           <Tcheck_t nextid expected T> 
                           symbols
                           (string_app "Expected type is not def. eq. to the"
                           (string_app " declared type of an identifier,"
                           (string_appnl (string_app "checking a " inc where)
                           (string_appnl (string_app "1. the expected type: "
                                           (trm_to_string eT))
                           (string_appnl (string_app "2. the declared type: "
                                           (trm_to_string T))
                           (string_appnl "3. the identifier: " s))))))) in
                         dec eT dec T r
                     | tt =>
                        dec s dec eT dec T
                        cast (Tcheck_something nextid T eT nextid
                               [x_vle_x nextid]
                               [aequiv_conv nextid T eT ae])
                        by cong <Tcheck_t nextid * T>
                             symm expected_eq
                     end %- match aequiv -%
                     end %- let K = match expected -% in
                 (mk_check nextid symbols create expected
                    pb_stdin symbols nextid T k K
                    [x_vle_x nextid] 
                    join (trie_interp symbols) (trie_interp symbols))
             end %- match e -% 
         end
        end
      | tt => 

        % check a compound expression (we just parsed a "(")

        match (gs_char pb_stdin) with
          getc_none ign pb_stdin => 
            dec pb_stdin dec expected 
            let r = 
            (handle_error_sym_unique <check_t nextid symbols create expected>
              symbols
              (string_app "Unexpected end of input parsing a " inc where)) in
            dec symbols r
        | getc_char ign c pb_stdin =>
          match (eqchar c Cbs) with
            ff => 
            match (eqchar c Cba) with
              ff => 

              % application case

              let pb_stdin = (pb_push pb_stdin c) in
              match (check pb_stdin symbols nextid symok create (nothing trm)
                       join (bndopttrm nextid nothing) tt str_app) with
                mk_check ign1 ign2 ign3 ign4 pb_stdin symbols' nextid' T1
                   k1 K1 nle1 U1 =>
                   
                   abbrev sym'ok = [symbols_ok_vle nextid nextid' symbols'
                                      [symbols_ok_cong nextid symbols symbols' 
                                        symok U1]
                                      nle1] in
                   match K1 with
                     Tcheck_nothing ign1 headT headbT =>
                     abbrev err = 
                       dec pb_stdin dec k1 
                       dec expected
                       let ret = 
                       (handle_error_sym_unique 
                         <check_t nextid symbols create expected>
                         symbols'
                         (string_app "The head of an application lacks a"
                         (string_app "pi-expression for its type."
                         (string_appnl "1. the head's type: " 
                           (trm_to_string headT))))) in 
                         dec headT dec symbols' ret in
                     match inc headT by headT_eq ign with 
                       sym n => err
                     | app h1 h2 => dec h1 dec h2 err
                     | lam n1 h1 => dec h1 err
                     | pi n1 dom ran => 
                       
                       % check the argument
                       dec headT
                       abbrev bdom = [bndtrm_pi2 nextid' 
                                       headT n1 dom ran headbT headT_eq] in
                       let dep_ran = (free_in n1 ran) by dep_ran_eq1 in
                       match (check pb_stdin symbols' nextid' sym'ok 
                                (or create dep_ran)
                                (something trm dom)
                                hypjoin (bndopttrm nextid' (something dom)) tt
                                  by bdom end
                                str_app) by ign carg with
                        mk_check ign1 ign2 ign3 ign4 pb_stdin
                         symbols'' nextid'' T2 k2 K2 nle2 U2 =>
                         
                         let pb_stdin = (eat_char pb_stdin where Crp) in

                         match K2 with
                           Tcheck_nothing ign1 ign2 ign3 => nothing
                         | Tcheck_something ign1 ign2 ign3 aid ale aeT2dom =>

                         abbrev bdom'' = [bndtrm_vle nextid' nextid'' dom
                                           nle2 bdom] in
                         abbrev headbT'' = [bndtrm_vle nextid' 
                                             nextid'' headT
                                             nle2 headbT] in
                         abbrev bran'' = [bndtrm_pi3 nextid'' 
                                           headT n1 dom ran
                                           headbT'' headT_eq] in
                         abbrev bn1'' = [bndtrm_pi1 nextid'' 
                                           headT n1 dom ran
                                           headbT'' headT_eq] in
                         abbrev nle12 = [vle_trans nextid nextid' nextid''
                                           nle1 nle2] in

                         % pull back to original ctxt, and cast to dom.
                         abbrev get_d2 = 
                           foralli(t2:trm)(d2:<deriv (gs_ctxt symbols') t2 T2>).
                             abbrev ret = 
                               (dconv G t2 T2 dom aid
                                  cast d2 
                                    by cong <deriv * t2 T2>
                                         symm 
                                         [gs_ctxt_interp symbols 
                                           symbols' U1]
                                  [bndtrm_vle nextid'' aid dom ale bdom'']
                                  aeT2dom) in
                             existsi ret True truei
                         in
                         let tmp =
                         match dep_ran with
                           ff => 
   
                           % simply typed head, so no substitution

                           match k2 with
                             tcheck_ff ign1 ign2 ign3 =>

                              % not creating

                              let K = (Tcheck_nothing nextid'' ran bran'') in
                              let k = cast (tcheck_ff nextid'' symbols ran)
                                      by cong <tcheck_t nextid'' symbols * ran>
                                          symm
                                          [or_eq_ff create dep_ran
                                            inj <tcheck_t ** ** * **> k2_Eq] in
                              dec k1 
                              (mk_check nextid symbols create (nothing trm)
                                 pb_stdin symbols'' nextid'' ran k K 
                                 nle12 trans U1 U2)
                           | tcheck_tt ign1 ign2 ign3 t2 d2 bt2 =>

                              % creating

                             abbrev create_eq = 
                                symm 
                                trans symm inj <tcheck_t ** ** * **> k2_Eq
                                trans cong (or create *) dep_ran_eq
                                           [or_def2ff create] in
                             existse_term [get_d2 t2 d2]
                             fun(spec d2:<deriv G t2 dom>)(ign:True).

                             let K = (Tcheck_nothing nextid'' ran bran'') in
                             let k = 
                                match k1 with
                                  tcheck_ff ign1 ign2 ign3 => 
                                  impossible 
                                    trans symm inj <tcheck_t ** ** * **> k1_Eq
                                      trans create_eq
                                            clash tt ff
                                    <tcheck_t nextid'' symbols create ran>
                                | tcheck_tt ign1 ign2 ign3 t1 d1 bt1 =>
                                  existse_term 
                                    [dapp_simple n1 dom ran
                                       G t1 t2 trans symm dep_ran_eq1 dep_ran_eq
                                       cast d1 by cong <deriv G t1 *> headT_eq
                                       d2]
                                  fun(spec d2:<deriv G (app t1 t2) ran>)
                                     (ign:True).
                                  cast 
                                  (tcheck_tt nextid'' symbols ran
                                    (app t1 t2)
                                    d2
                                    hypjoin (bndtrm nextid'' (app t1 t2)) tt
                                     by [bndtrm_vle nextid' nextid'' t1
                                          nle2 bt1]
                                        bt2 end)
                                  by cong <tcheck_t nextid'' symbols * ran>
                                      symm inj <tcheck_t ** ** * **> k1_Eq
                                end %- k1 -%  in 

                              (mk_check nextid symbols create (nothing trm)
                                 pb_stdin symbols'' nextid'' ran k K 
                                 nle12 trans U1 U2) 
                           end %- k2 -%
                         | tt =>

                           % dependently typed head, so must substitute

                           match k2 with
                             tcheck_ff ign1 ign2 ign3 =>
                               impossible
                                 trans symm [ortt_i2 create dep_ran 
                                              dep_ran_eq]
                                 trans inj <tcheck_t ** ** * **> k2_Eq
                                       clash ff tt
                               <check_t nextid symbols create (nothing trm)>
                           | tcheck_tt ign1 ign2 ign3 t2 d2 bt2 =>

                             existse_term [get_d2 t2 d2]
                             fun(spec d2:<deriv G t2 dom>)(ign:True).
                             let sG = (mctxtc n1 inc t2 inc mctxtn) in
                             abbrev bsG = trans cong (bndmctxt nextid'' *) 
                                                   sG_eq
                                                [bndmctxtc nextid'' n1 t2 bt2] in
                             match (msbst nextid'' sG ran) by eq_sran ign with
                             mk_msbst_t nextid''' sran =>
                              dec ran dec sG
                              abbrev bsran = [bndtrm_msbst nextid'' sG
                                              ran nextid''' sran
                                              bran'' bsG eq_sran] in
                              abbrev nle3 = [msbst_vle nextid'' sG
                                              ran nextid''' sran
                                              eq_sran] in
                              abbrev nle23 = [vle_trans nextid' nextid'' nextid'''
                                               nle2 nle3] in

                              let K = (Tcheck_nothing nextid''' sran 
                                         [bndtrm_msbst nextid'' sG
                                           ran nextid''' sran 
                                           bsG bran'' eq_sran]) in
                              let k = 
                                match k1 with
                                  tcheck_ff ign1 ign2 ign3 => 
                                  dec t2
                                  cast (tcheck_ff nextid''' symbols sran)
                                  by cong <tcheck_t nextid''' symbols * sran>
                                      symm inj <tcheck_t ** ** * **> k1_Eq
                                | tcheck_tt ign1 ign2 ign3 t1 d1 bt1 =>
                                  cast 
                                  (tcheck_tt nextid''' symbols sran
                                    (app t1 t2)
                                    cast
                                    (dapp G t1 t2 n1 dom ran nextid''
                                       cast d1 by cong <deriv G t1 *> headT_eq
                                       d2
                                       bt2 bran'' bn1'')
                                    by cong <deriv G (app t1 t2) *>
                                        hypjoin (sbst nextid'' t2 n1 ran) sran
                                          by eq_sran sG_eq end
                                    hypjoin (bndtrm nextid''' (app t1 t2)) tt
                                     by [bndtrm_vle nextid' nextid''' t1
                                          nle23
                                          bt1]
                                        [bndtrm_vle nextid'' nextid''' t2 nle3 
                                          bt2] end)
                                  by cong <tcheck_t nextid''' symbols * sran>
                                      symm inj <tcheck_t ** ** * **> k1_Eq
                                end %- k1 -%  in 
                              (mk_check nextid symbols create (nothing trm)
                                 pb_stdin symbols'' nextid''' sran k K 
                                 [vle_trans nextid nextid' nextid'''
                                    nle1 nle23]
                                 trans U1 U2)
                             end
                           end
                         end %- dep_ran -% in
     
                         % now just check alpha-equivalence of the 
                         % type produced above with the expected one.
                         match expected with
                           nothing ign => 
                            cast tmp by cong <check_t nextid symbols create *>
                                         symm expected_eq
                         | something ign eT =>
                           match tmp with
                            mk_check ign1 ign2 ign3 ign4 pb_stdin
                              rsymbols rnextid ign5 rk rK rnle rU =>
                            match rK with
                              Tcheck_nothing ign rT brT =>
                              match (aequiv rnextid rT eT) by ae ign with
                              ff =>
                              let r = 
                             (handle_error_sym_unique
                              <check_t nextid symbols create expected>
                              rsymbols
                              (string_app "Expected type is not def. eq. to the"
                              (string_app " computed type of an application,"
                              (string_appnl (string_app "checking a " inc where)
                              (string_appnl (string_app "1. the expected type: "
                                              (trm_to_string eT))
                              (string_appnl "2. the computed type: "
                                            (trm_to_string rT))))))) in
                              dec eT dec pb_stdin dec rk 
                              dec rsymbols dec rT
                              r
                             | tt =>
                             dec eT dec rT
                             match inc rk by ign rk_Eq with
                               tcheck_ff ign1 ign2 ign3 =>
                               dec rk
                               (mk_check nextid symbols create expected
                                 pb_stdin rsymbols nextid rT 
                                 cast (tcheck_ff nextid symbols rT)
                                 by cong <tcheck_t nextid symbols * rT> 
                                     symm inj <tcheck_t ** ** * rT> rk_Eq
                                 cast (Tcheck_something nextid rT eT rnextid
                                         rnle [aequiv_conv rnextid rT eT ae])
                                 by cong <Tcheck_t nextid * rT>
                                     symm expected_eq
                                 [x_vle_x nextid] rU)
                             | tcheck_tt ign1 ign2 ign3 ign4 ign5 ign6 =>
                               dec ign4 
                               (mk_check nextid symbols create expected
                                 pb_stdin rsymbols rnextid rT rk
                                 cast (Tcheck_something rnextid rT eT rnextid
                                         [x_vle_x rnextid]
                                         [aequiv_conv rnextid rT eT ae])
                                 by cong <Tcheck_t rnextid * rT>
                                     symm expected_eq
                                 rnle rU)
                             end %- rk -%
                             end %- aequiv -%
                            | Tcheck_something ign1 ign2 ign3 ign4 ign5 
                                ign6 => nothing
                            end %- rK -%
                          end %- tmp -%
                         end %- expected -% 
                         end %- K2 -%
                       end
                     end
                   | Tcheck_something ign1 ign2 ign3 ign4 ign5 ign6 => nothing
                   end
              end

            | tt => 

              % pi case

              % first read the pi-bound variable
              match (gs_get_chars pb_stdin str_pi ff ff) with
                mk_gs_get_chars pb_stdin s =>
  
                match create with
                  ff => 
                    dec pb_stdin dec s dec expected
                    let r = 
                    (handle_error_sym_unique
                      <check_t nextid symbols create expected>
                      symbols
                      (string_app "A pi-expression appears in an "
                         "invalid position (a term-creating one).")) in
                    dec symbols r
                | tt =>
                match expected with
                  nothing ign => 
                  dec pb_stdin dec s 
                  let r = 
                  (handle_error_sym_unique
                    <check_t nextid symbols create expected>
                    symbols
                    (string_app "A pi-expression appears in an "
                             " invalid position (a type-synthesizing one).")) in
                  dec symbols r
                | something ign eT =>

                % get previous binding
                let oprev = (trie_lookup symbols_e symbols s) by oprev_eq1 in 
 
                % check the domain
                match (check pb_stdin symbols nextid symok tt
                           (something trm (sym tp)) 
                           hypjoin (bndopttrm nextid (something (sym tp))) tt
                           by I5 end
                           str_pi) with
                  mk_check ign1 ign2 ign3 ign4 pb_stdin symbols' nextid' 
                    T1 k1 K1 nle1 U1 =>

                  match k1 with
                  tcheck_ff ign1 ign2 ign3 => nothing
                | tcheck_tt ign1 ign2 ign3 t1 d1 bt1 =>

                  match K1 with
                  Tcheck_nothing ign1 ign2 ign3 => nothing
                | Tcheck_something ign1 ign2 ign3 aid ale acT1tp =>

                  abbrev sym'ok = [symbols_ok_cong nextid symbols symbols' 
                                     symok U1] in

                  abbrev d1 = (dconv G t1 T1 (sym tp) aid
                                 d1 
                                 [bndtrm_vle nextid aid (sym tp)
                                    [vle_trans nextid nextid' aid 
                                       nle1 ale] I5]
                                 acT1tp) in

                  let inssymbols = (trie_insert symbols_e inc s
                                     (mkpair var trm nextid' inc t1) 
                                     symbols') in
                  existse_term [trie_insert_interp symbols_e 
                                 symbols' inssymbols
                                 s (mkpair var trm nextid' t1)
                                 symm inssymbols_eq]
                  fun(spec L1 L2:<list <pair string symbols_e>>)
                     (inssymi : 
                      { (trie_interp inssymbols) = 
                        (append L1 (cons (mkpair s (mkpair nextid' t1)) L2))}).
                  abbrev G1 = 
                   terminates (map <pair string symbols_e> symbols_e
                                 Unit unit
                                 fun(u:Unit).(snd string symbols_e) L1)
                   by trie_range_map_tot in
                  abbrev G2 = 
                   terminates (map <pair string symbols_e> symbols_e
                                 Unit unit 
                                 fun(u:Unit).(snd string symbols_e) L2)
                   by trie_range_map_tot in
                  abbrev inssymr = [trie_interp_range2 symbols_e inssymbols
                                     s (mkpair var trm nextid' t1) L1 L2
                                     inssymi] in
                  abbrev inssymctxt = 
                    trans join (gs_ctxt inssymbols)
                               (trie_range inssymbols)
                    trans inssymr
                          join (append G1 (cons (mkpair nextid' t1) G2))
                               (append G1 (ctxtc nextid' t1 G2)) in
                      
                  match (vS nextid') by Snextid'_eq ign with
                  mk_word_inc_t Snextid' carry => 
                  match carry with 
                  ff => 

                  abbrev Snextid'_eq = trans Snextid'_eq 
                                         cong (mk_word_inc_t Snextid' *)
                                           carry_eq in
                  match (check pb_stdin inssymbols Snextid' 
                              [symbols_ok_insert_next nextid' 
                              symbols' inssymbols s t1 
                              Snextid'
                              symm [word_to_nat_inc2 nextid' Snextid'
                                     Snextid'_eq]
                              [symbols_ok_vle nextid nextid' symbols' 
                                 sym'ok nle1]
                              inssymbols_eq]
                           tt
                           (something trm inc eT) 
                           trans cong (bndopttrm Snextid' *) 
                                   symm expected_eq
                             [bndopttrm_vle nextid 
                               Snextid' expected
                               [vle_trans nextid nextid'
                                  Snextid'
                                  nle1 [vle_S nextid' Snextid' Snextid'_eq]] 
                               bndexpected]
                           str_pi) with
                    mk_check ign1 ign2 ign3 ign4 pb_stdin symbols'' nextid'' 
                         T2 k2 K2 nle2 U2 =>

                    match k2 with
                      tcheck_ff ign1 ign2 ign3 => nothing
                    | tcheck_tt ign1 ign2 ign3 t2 d2 bt2 =>       

                    match K2 with
                      Tcheck_nothing ign1 T2 bT2 => (nothing nat)
                    | Tcheck_something ign1 ign2 ign3 aid ale acT2eT =>

                    let pb_stdin = (eat_char pb_stdin where Crp) in
                     abbrev eTistp = (istp eT) in
                     abbrev eTisknd = (isknd eT) in
                     match (or eTistp eTisknd) by eTistpknd ign with
                       ff => 
                       dec pb_stdin dec t1 dec s dec oprev

                       let ret = 
                        (handle_error_sym_unique
                          <check_t nextid symbols create expected>
                          symbols''
                          (string_app "The classifier expected for a"
                          (string_app " pi-expression is not a type"
                          (string_app " or kind."
                          (string_appnl "1. the classifier: " 
                                         (trm_to_string eT)))))) in
                       dec t2 dec eT dec symbols'' ret
                     | tt =>
                       abbrev PeT = [istpkndEq eT eTistpknd] in
                       abbrev Pnextid' = 
                          [vltle_trans nextid'
                             Snextid' nextid''
                             [vlt_S nextid' Snextid' Snextid'_eq] nle2] in
                       abbrev Pnextid = [vlelt_trans nextid nextid' nextid''
                                           nle1 
                                           Pnextid'] in
                       abbrev d2 = 
                         (dconv (gs_ctxt inssymbols)
                            t2 T2 eT aid d2 
                            [bndtrm_vle nextid aid eT
                              [vlt_implies_vle nextid aid
                                 [vltle_trans nextid nextid'' aid
                                    Pnextid ale]]
                                    hypjoin (bndtrm nextid eT) tt 
                                    by bndexpected expected_eq end]
                             acT2eT) in

                  abbrev lookup' = [trie_lookup_same_interp symbols_e 
                                      symbols symbols' s oprev
                                      symm oprev_eq1 U1] in

                  abbrev symbolsi =
                     foralli(oprev_eq : { oprev = nothing }).
                        trans U1
                          [trie_insert_new symbols_e symbols'
                             inssymbols s (mkpair var trm nextid' t1)
                             trans lookup' oprev_eq
                             symm inssymbols_eq
                             L1 L2 inssymi] in

                  abbrev symctxt_something = 
                          foralli(prev:<pair var trm>)
                                 (oprev_eq : { oprev = (something prev)}).
                           trans join G
                                   (map unit fun(u).snd 
                                      (trie_interp symbols))
                           trans cong (map unit fun(u).snd *) 
                                  [trie_insert_lookup_interp symbols_e
                                     symbols symbols' inssymbols s 
                                     (mkpair var trm nextid' t1)
                                     prev
                                     trans symm oprev_eq1 oprev_eq
                                     U1
                                     symm inssymbols_eq
                                     L1 L2 inssymi] 
                           trans [map_append <pair string <pair var trm>>
                                   <pair var trm> Unit unit 
                                   fun(u:Unit).(snd string <pair var trm>)
                                   L1 (cons <pair string <pair var trm>>
                                        (mkpair string <pair var trm>
                                          s prev)
                                        L2)] 
                               cong (append G1 *)
                                  join (map unit fun(u).snd 
                                         (cons (mkpair s prev) L2))
                                       (cons prev G2) in

                    abbrev symctxt_nothing =
                       foralli(oprev_eq : { oprev = nothing }).
                           trans join G
                                  (map unit fun(u).snd 
                                    (trie_interp symbols))
                           trans cong (map unit fun(u).snd *) 
                                  [symbolsi oprev_eq]
                             [map_append <pair string <pair var trm>>
                                <pair var trm> Unit unit 
                                fun(u:Unit).(snd string <pair var trm>)
                                L1 L2] in

                       abbrev the_deriv = 
                         match oprev with 
                          nothing A => 
                          abbrev G_eq = [symctxt_nothing oprev_eq] in
                          cast
                            (dpi G1 G2 nextid' t1 t2 eTistp 
                               cast d1 by cong <deriv * t1 (sym tp)> G_eq
                               cast d2 by
                               trans cong <deriv (gs_ctxt inssymbols) t2 *> PeT
                                 cong <deriv * t2 (sym (tpknd (istp eT)))> inssymctxt)
                          by cong <deriv * (pi nextid' t1 t2)
                                      (sym (tpknd (istp eT)))> symm G_eq
                      | something ign prev => 

                           % In this case, G = (append G1 (cons prev G2))
                           abbrev G' = (append ctxte G1 (cons ctxte prev G2)) in
                           abbrev Gprev = (cons ctxte prev ctxtn) in
                           abbrev G1' = (append ctxte G1 Gprev) in
                           abbrev G2' = (ctxtc nextid' t1 G2) in
                           abbrev GG = (append ctxte G1' G2) in
                           abbrev GG' = (append ctxte G1' G2') in
                           abbrev GG'' = (append ctxte G1 (cons ctxte prev G2')) in

                        abbrev G_eq = [symctxt_something prev oprev_eq] in
                        abbrev G_eq_GG = 
                               trans G_eq
                                  trans join G' (append G1 (append Gprev G2))
                                        symm [append_assoc ctxte G1 Gprev G2] in
                        abbrev GG'_eq_GG'' = trans [append_assoc ctxte G1 Gprev G2']
                                               join (append G1 (append Gprev G2')) GG'' in
                        abbrev diffidsGG'' = 
                            [cong_diffids GG' GG''
                              [diffids_wk1 G1' G2 nextid' t1 
                                 [cong_diffids G GG I1 G_eq_GG]
                                 [idsbnd1_vle nextid nextid' GG
                                   [cong_idsbnd1 nextid G GG I2 G_eq_GG] nle1]]
                              GG'_eq_GG''] in
                         existse_term 
                         [deriv_wk1 G1 G2' prev t2 eT 
                            diffidsGG''
                            cast d2
                            by cong <deriv * t2 eT> inssymctxt]
                         fun(spec d2:<deriv GG'' t2 eT>)
                            (ign:True).
                        
                          cast 
                          (dpi G1' G2 nextid' t1 t2 eTistp
                            cast d1 by cong <deriv * t1 (sym tp)> 
                                         trans G_eq
                                         trans join (append G1 (cons prev G2))
                                                    (append G1 (append Gprev G2))
                                               symm [append_assoc ctxte G1 Gprev G2]
                            cast d2 by trans cong <deriv * t2 eT> symm GG'_eq_GG''
                                         cong <deriv GG' t2 *> PeT)
                          by cong <deriv * (pi nextid' t1 t2) (sym (tpknd (istp eT)))>
                                 trans [append_assoc ctxte G1 Gprev G2]
                                 trans join (append G1 (append Gprev G2)) G'
                                   symm G_eq
                      end in

                      abbrev bpi = 
                            hypjoin (bndtrm nextid'' (pi nextid' t1 t2)) tt
                            by Pnextid'
                               [bndtrm_vle nextid' nextid'' t1 
                                 [vlt_implies_vle nextid' nextid'' Pnextid'] bt1]
                               bt2 end in

                     let k = 
                       (tcheck_tt nextid'' symbols eT 
                          (pi nextid' t1 t2)
                          cast
                            the_deriv
                            by cong <deriv G (pi nextid' t1 t2) *>
                                symm PeT                    
                          bpi) in
                      
                     let K = (Tcheck_something nextid'' eT eT nextid''
                               [x_vle_x nextid'']
                               join (acanon nextid'' eT)
                                    (acanon nextid'' eT)) in

                     dec eT
                     % restore the previous binding, and then return
                     cast
                     match oprev with 
                       nothing A => 

                       let remsymbols = (trie_remove symbols_e s symbols'') in
                        dec s
                        abbrev remsymbolsi =
                          [trie_remove_interp symbols_e symbols'' remsymbols
                             s (mkpair var trm nextid' t1) 
                             symm remsymbols_eq L1 L2
                             trans symm U2
                                   inssymi] in
                       (mk_check nextid symbols tt (something trm eT)
                          pb_stdin remsymbols nextid'' eT k K
                          [vlt_implies_vle nextid nextid'' Pnextid]
                          trans [symbolsi oprev_eq] symm remsymbolsi)
                           
                     | something ign prev => 
                     
                       let rsymbols = (trie_insert symbols_e s prev symbols'') in
                        abbrev symrsymi = trans U1
                                   [trie_restore_interp symbols_e symbols'
                                     inssymbols symbols'' rsymbols s prev 
                                     (mkpair var trm nextid' t1)
                                     trans lookup' oprev_eq
                                     symm inssymbols_eq
                                     U2 symm rsymbols_eq ] in
                        (mk_check nextid symbols tt (something trm eT)
                          pb_stdin rsymbols nextid'' eT k K
                          [vlt_implies_vle nextid nextid'' Pnextid]
                          symrsymi)

                     end %- match oprev (to restore binding) -%
                     by trans cong <check_t nextid symbols * (something eT)>
                               symm create_eq
                              cong <check_t nextid symbols create *>
                               symm expected_eq

                     end %- eTistpknd -%
                   end %- match K2 -%
                   end %- match k2 -%
                  end %- check range -%
                  | tt %- carry -% =>
                      abort <check_t nextid  symbols create expected> 
                  end %- check carry -%
                  end %- increment nextid' -%
                end %- match K1 -%
                end %- match k1 -%
                end %- check domain -%
                end %- match expected -%
                end %- match create -%
              end %- gs_get_chars -% 

            end %- (eqchar c Cba) = ff -%
          | tt =>

            % lambda case 
            
            match expected with
              nothing ign => 
                dec pb_stdin 
                let r = 
                (handle_error_sym_unique
                  <check_t nextid symbols create expected>
                  symbols
                  (string_app "A lambda-expression appears in an "
                           "invalid position (a type-synthesizing one).")) in
                dec symbols r
            | something ign eT =>

              abbrev handle_err = 
                dec pb_stdin 
                let r = 
                (handle_error_sym_unique
                  <check_t nextid symbols create expected>
                  symbols
                  (string_app "The type expected for a lambda-expression "
                  (string_app "is not a pi-type."
                  (string_appnl "1. the expected type: "
                    (trm_to_string eT))))) in
                dec symbols dec eT r in

              match inc eT by eT_eq ign with
                sym n => handle_err
              | app t1 t2 => dec t1 dec t2 handle_err
              | lam n t1 => dec t1 handle_err
              | pi n1 dom ran => 
                
                dec eT 

                % read the lambda-bound variable
                match (gs_get_chars pb_stdin str_lam ff ff) with
                  mk_gs_get_chars pb_stdin s =>
                
                  % get previous binding for the var.
                  let oprev = (trie_lookup symbols_e symbols s) by oprev_eq1 in 
                  
                  let inssymbols = (trie_insert symbols_e inc s
                                     (mkpair var trm nextid dom) 
                                     symbols) in
                  existse_term [trie_insert_interp symbols_e 
                                 symbols inssymbols
                                 s (mkpair var trm nextid dom)
                                 symm inssymbols_eq]
                  fun(spec L1 L2:<list <pair string symbols_e>>)
                     (inssymi : 
                      { (trie_interp inssymbols) = 
                        (append L1 (cons (mkpair s (mkpair nextid dom)) L2))}).
                  abbrev G1 = 
                   terminates (map <pair string symbols_e> symbols_e
                                 Unit unit
                                 fun(u:Unit).(snd string symbols_e) L1)
                   by trie_range_map_tot in
                  abbrev G2 = 
                   terminates (map <pair string symbols_e> symbols_e
                                 Unit unit 
                                 fun(u:Unit).(snd string symbols_e) L2)
                   by trie_range_map_tot in
                  abbrev inssymr = [trie_interp_range2 symbols_e inssymbols
                                     s (mkpair var trm nextid dom) L1 L2
                                     inssymi] in
                  abbrev inssymctxt = 
                    trans join (gs_ctxt inssymbols)
                               (trie_range inssymbols)
                    trans inssymr
                          join (append G1 (cons (mkpair nextid dom) G2))
                               (append G1 (ctxtc nextid dom G2)) in
                      
                  let sG = (mctxtc n1 (sym nextid) inc mctxtn) in
                  match (vS nextid) by Snextid_eq ign with
                  mk_word_inc_t Snextid carry =>
                  match carry with
                  ff =>

                  abbrev Snextid_eq = trans Snextid_eq 
                                         cong (mk_word_inc_t Snextid *)
                                           carry_eq in

                  match (msbst Snextid sG ran) by meq ign with
                    mk_msbst_t nextid' ran' =>

                    dec sG dec ran
                    abbrev meq1 = trans cong (msbst Snextid * ran)
                                         symm sG_eq
                                       meq in
                    abbrev PSnextid = [msbst_vle Snextid sG ran nextid' ran'
                                        meq] in
                    abbrev Pnextid1 = [vltle_trans nextid Snextid nextid'
                                        [vlt_S nextid Snextid Snextid_eq] 
                                        PSnextid] in

                    abbrev bran' = [bndtrm_msbst Snextid sG ran nextid' ran'
                                     trans cong (bndmctxt Snextid *)
                                             sG_eq
                                       [bndmctxtc Snextid n1 (sym nextid) 
                                         hypjoin (bndtrm Snextid
                                                   (sym nextid)) tt
                                         by [vlt_S nextid Snextid Snextid_eq] 
                                         end]
                                     [bndtrm_vle nextid Snextid ran 
                                      [vle_S nextid Snextid Snextid_eq]
                                      [bndtrm_pi3 nextid eT n1 dom ran
                                        hypjoin (bndtrm nextid eT) tt
                                         by bndexpected expected_eq end
                                        eT_eq]]
                                     meq] in
                    match (check pb_stdin inssymbols nextid'
                            [symbols_ok_vle Snextid nextid' inssymbols
                              [symbols_ok_insert_next nextid symbols inssymbols
                                s dom Snextid 
                                symm [word_to_nat_inc2 nextid Snextid
                                       Snextid_eq]
                                symok inssymbols_eq]
                              PSnextid]
                           create
                           (something trm ran')
                           hypjoin (bndopttrm nextid' (something ran'))
                                   tt 
                            by bran' end
                           str_lam) with
                      mk_check ign1 ign2 ign3 ign4 pb_stdin symbols'
                        nextid'' rT rk rK nle U =>
                      
                      let pb_stdin = (eat_char pb_stdin str_lam Crp) in

                      abbrev Pnextid2 = [vltle_trans nextid nextid' nextid''
                                          Pnextid1 nle] in

                      abbrev Pnextid2a = 
                         [vlt_implies_vle nextid nextid'' Pnextid2] in

                      abbrev symbolsi =
                         foralli(oprev_eq : { oprev = nothing }).
                              [trie_insert_new symbols_e symbols
                                inssymbols s (mkpair var trm nextid dom)
                                trans symm oprev_eq1 oprev_eq
                                symm inssymbols_eq
                                L1 L2 inssymi] in
                      cast
                      match rk with
                        tcheck_ff ign1 ign2 ign3 =>
                        
                        dec rK 
                        abbrev create_eq = inj <tcheck_t ** ** * **> rk_Eq in
                        
                        let K = (Tcheck_something nextid eT eT nextid''
                                  Pnextid2a
                                  join (acanon nextid'' eT)
                                       (acanon nextid'' eT)) in
                        let k = (tcheck_ff nextid symbols eT) in

                        cast
                        match oprev with
                          nothing A => 

                          let remsymbols = (trie_remove symbols_e s symbols') in
                          dec s
                          abbrev remsymbolsi =
                            [trie_remove_interp symbols_e symbols' remsymbols
                               s (mkpair var trm nextid dom) 
                               symm remsymbols_eq L1 L2
                               trans symm U
                                     inssymi] in

                          (mk_check nextid symbols ff (something trm eT)
                            pb_stdin remsymbols nextid eT k K
                            [x_vle_x nextid]
                            trans [symbolsi oprev_eq] symm remsymbolsi)
                           
                        | something ign prev => 
                     
                          let rsymbols = 
                               (trie_insert symbols_e s prev symbols') in
                          abbrev symrsymi = 
                                   [trie_restore_interp symbols_e symbols
                                     inssymbols symbols' rsymbols s prev 
                                     (mkpair var trm nextid dom)
                                     trans symm oprev_eq1 oprev_eq
                                     symm inssymbols_eq
                                     U symm rsymbols_eq ] in

                          (mk_check nextid symbols ff (something trm eT)
                            pb_stdin rsymbols nextid eT k K
                            [x_vle_x nextid] symrsymi)

                        end %- match oprev (to restore binding) -%
                        by cong <check_t nextid symbols * (something trm eT)>
                             symm create_eq
                      | tcheck_tt ign1 ign2 ign3 t1 d1 bt1 =>

                        abbrev create_eq = inj <tcheck_t ** ** * **> rk_Eq in

                        abbrev rettp = (pi nextid dom ran') in
                        abbrev blam = 
                           hypjoin (bndtrm nextid'' (lam nextid t1)) tt
                           by Pnextid2 bt1 end in
                        let K = 
                          cast (Tcheck_something nextid'' 
                                  rettp (pi n1 dom ran) nextid''
                                  [x_vle_x nextid'']
                                  [acanon_rename_pi nextid'' 
                                    nextid n1 dom ran' ran])
                          by cong <Tcheck_t nextid'' (something *) rettp> 
                               symm eT_eq in

                        abbrev bran'' = [bndtrm_vle nextid' nextid'' ran'
                                          nle bran'] in

                        match rK with
                          Tcheck_nothing ign1 ign2 ign3 => nothing
                        | Tcheck_something ign1 ign2 ign3 aid ale ae =>
                        abbrev symctxt_nothing = 
                           foralli(oprev_eq : { oprev = nothing }).
                           trans join G
                                  (map unit fun(u).snd 
                                    (trie_interp symbols))
                           trans cong (map unit fun(u).snd *) 
                                  [symbolsi oprev_eq]
                             [map_append <pair string <pair var trm>>
                                <pair var trm> Unit unit 
                                fun(u:Unit).(snd string <pair var trm>)
                                L1 L2] in

                        abbrev symctxt_something = 
                          foralli(prev:<pair var trm>)
                                 (oprev_eq : { oprev = (something prev)}).
                           trans join G
                                   (map unit fun(u).snd 
                                      (trie_interp symbols))
                           trans cong (map unit fun(u).snd *) 
                                  [trie_insert_lookup_interp symbols_e
                                     symbols symbols inssymbols s 
                                     (mkpair var trm nextid dom)
                                     prev
                                     trans symm oprev_eq1 oprev_eq
                                     join (trie_interp symbols) 
                                          (trie_interp symbols)
                                     symm inssymbols_eq
                                     L1 L2 inssymi] 
                           trans [map_append <pair string <pair var trm>>
                                   <pair var trm> Unit unit 
                                   fun(u:Unit).(snd string <pair var trm>)
                                   L1 (cons <pair string <pair var trm>>
                                        (mkpair string <pair var trm>
                                          s prev)
                                        L2)] 
                               cong (append G1 *)
                                  join (map unit fun(u).snd 
                                         (cons (mkpair s prev) L2))
                                       (cons prev G2) in

                        abbrev d1 = cast
                                    (dconv (gs_ctxt inssymbols) t1 rT ran' aid d1
                                      [bndtrm_vle nextid'' aid ran' ale bran'']
                                      ae)
                                    by cong <deriv * t1 ran'> inssymctxt in

                        cast
                        match oprev with
                          nothing A => 

                          abbrev G_eq = [symctxt_nothing oprev_eq] in
                          let remsymbols = (trie_remove symbols_e s symbols') in
                          dec s
                          abbrev remsymbolsi =
                            [trie_remove_interp symbols_e symbols' remsymbols
                               s (mkpair var trm nextid dom) 
                               symm remsymbols_eq L1 L2
                               trans symm U
                                     inssymi] in
                          
                          let k = 
                            (tcheck_tt nextid'' symbols rettp
                               (lam nextid t1)
                               cast 
                               (dlam G1 G2 t1 nextid dom ran' d1)
                               by cong <deriv * (lam nextid t1) (pi nextid dom ran')>
                                    symm G_eq
                               blam) in

                          (mk_check nextid symbols tt (something trm eT)
                            pb_stdin remsymbols nextid'' rettp k K
                            Pnextid2a
                            trans [symbolsi oprev_eq] symm remsymbolsi)
                           
                        | something ign prev => 
                     
                          abbrev G_eq = [symctxt_something prev oprev_eq] in
                          let rsymbols = 
                               (trie_insert symbols_e s prev symbols') in
                          abbrev symrsymi = 
                                   [trie_restore_interp symbols_e symbols
                                     inssymbols symbols' rsymbols s prev 
                                     (mkpair var trm nextid dom)
                                     trans symm oprev_eq1 oprev_eq
                                     symm inssymbols_eq
                                     U symm rsymbols_eq ] in
                           % In this case, G = (append G1 (cons prev G2))
                           abbrev G' = (append ctxte G1 (cons ctxte prev G2)) in
                           abbrev Gprev = (cons ctxte prev ctxtn) in
                           abbrev G1' = (append ctxte G1 Gprev) in
                           abbrev G2' = (ctxtc nextid dom G2) in
                           abbrev GG = (append ctxte G1' G2) in
                           abbrev GG' = (append ctxte G1' G2') in
                           abbrev GG'' = (append ctxte G1 (cons ctxte prev G2')) in

                        abbrev G_eq = [symctxt_something prev oprev_eq] in
                        abbrev G_eq_GG = 
                               trans G_eq
                                  trans join G' (append G1 (append Gprev G2))
                                        symm [append_assoc ctxte G1 Gprev G2] in
                        abbrev GG'_eq_GG'' = trans [append_assoc ctxte G1 Gprev G2']
                                               join (append G1 (append Gprev G2')) GG'' in
                        abbrev diffidsGG'' = 
                            [cong_diffids GG' GG''
                              [diffids_wk1 G1' G2 nextid dom
                                 [cong_diffids G GG I1 G_eq_GG]
                                 [cong_idsbnd1 nextid G GG I2 G_eq_GG]]
                              GG'_eq_GG''] in
                         existse_term 
                         [deriv_wk1 G1 G2' prev t1 ran' 
                            diffidsGG'' d1]
                         fun(spec d1:<deriv GG'' t1 ran'>)
                            (ign:True).
                        
                         let k =
                          (tcheck_tt nextid'' symbols rettp
                            (lam nextid t1)
                            cast
                              (dlam G1' G2 t1 nextid dom ran'
                                cast d1 by cong <deriv * t1 ran'> symm GG'_eq_GG'')
                            by cong <deriv * (lam nextid t1) (pi nextid dom ran')>
                                 trans [append_assoc ctxte G1 Gprev G2]
                                 trans join (append G1 (append Gprev G2)) G'
                                   symm G_eq
                            blam) in

                          (mk_check nextid symbols tt (something trm eT)
                            pb_stdin rsymbols nextid'' rettp k K
                            Pnextid2a
                            symrsymi)

                        end %- match oprev (to restore binding) -%
                        by cong <check_t nextid symbols * (something trm eT)>
                             symm create_eq
                        end %- rK -%
                      end %- rk -%
                      by cong <check_t nextid symbols create *>
                            symm expected_eq
                    end %- check body of lam -%
                  end %- msbst into ran -%
                  | tt %- carry -% => 
                    abort <check_t nextid symbols create expected>
                  end %- check carry -%
                  end %- increment nextid -%
                end %- gs_get_chars -%
              end %- eT -%
            end %- expected -%
          end %- (eqchar Cbs) -%
          
          % finished processing compound expression

        end %- (gs_char pb_stdin) -%
      end
    end.

