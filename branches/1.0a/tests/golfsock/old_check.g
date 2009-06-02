Include "symbols_thm.g".
Include trusted "bndtrm_thm.g".
Include "deriv_thm.g".
Include "gs_io.g".
Include "checkh.g".

Inductive tcheck_t : Fun(nextid:nat)(symbols:symbols_t)
                        (create:bool)(T:trm).type :=
  tcheck_ff : Fun(spec nextid:nat)
                 (spec symbols:symbols_t)
                 (spec T:trm).
                 <tcheck_t nextid symbols ff T>
| tcheck_tt : Fun(spec nextid:nat)
                 (spec symbols:symbols_t)
                 (spec T:trm)
                 (t:trm)
                 (spec d:<deriv (gs_ctxt symbols) t T>)
                 (bt : { (bndtrm nextid t) = tt}).
                 <tcheck_t nextid symbols tt T>.

Inductive Tcheck_t : Fun(nextid:nat)
                        (expected:<option trm>)
                        (T:trm).type :=
  Tcheck_nothing : Fun(spec nextid:nat)
                      (T:trm)
                      (bT:{(bndtrm nextid T) = tt}).
                     <Tcheck_t nextid (nothing trm) T>
| Tcheck_something : Fun(spec nextid:nat)
                        (spec T eT:trm)
                        (u2 : { (acanon nextid T) = (acanon nextid eT)}).
                      <Tcheck_t nextid (something trm eT) T>.

Inductive check_t : Fun(nextid:nat)(symbols:symbols_t)
                       (create:bool)(expected:<option trm>).type :=
  mk_check : Fun(spec nextid:nat)(spec symbols:symbols_t)
                (spec create:bool)(spec expected:<option trm>)
                (unique pb_stdin:pb_stdin_t)
                (unique symbols':symbols_t)
                (nextid':nat)
                (spec T:trm)
                (k:<tcheck_t nextid' symbols create T>)
                (K:<Tcheck_t nextid' expected T>)
                (nle : { (le nextid nextid') = tt })
                (U : { (trie_interp symbols) = (trie_interp symbols')}).

                <check_t nextid symbols create expected>.

Define check : Fun(unique pb_stdin:pb_stdin_t)(unique symbols:symbols_t)
                  (nextid:nat)
                  (spec symok:@<symbols_ok nextid symbols>)
                  (create:bool)
                  (expected:<option trm>)
                  (bndexpected:{(bndopttrm nextid expected) = tt})
                  (owned where:string).
                  unique <check_t nextid symbols create expected> :=
  fun check(unique pb_stdin:pb_stdin_t)
           (unique symbols:symbols_t)
           (nextid:nat)
           (spec symok:@<symbols_ok nextid symbols>)
           (create:bool)
           (expected:<option trm>)
           (bndexpected:{(bndopttrm nextid expected) = tt})
           (owned where:string)
         :unique <check_t nextid symbols create expected>.
  existse_term symok
  fun(I1 : @<diffids (gs_ctxt symbols)>)
     (I2 : @<idsbnd1 nextid (gs_ctxt symbols)>)
     (I3 : @<idsbnd2 nextid (gs_ctxt symbols)>)
     (I4 : @<decsderiv (gs_ctxt symbols)>)
     (I5 : { (bndtrm nextid (sym tp)) = tt})
     (ign : True).
  abbrev G = terminates (gs_ctxt symbols) by gs_ctxt_tot in
    match (gs_char pb_stdin) with
      getc_none ign pb_stdin => 
         dec pb_stdin dec expected dec nextid
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

             dec pb_stdin dec expected dec nextid
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
                    (ud : {G = 
                              (append l1 (ctxtc n T l2)) }).
                 abbrev G' = (append ctxte l1 l2) in
                 abbrev G'' = (append ctxte l1 (ctxtc n T l2)) in
                 abbrev bndT = [I3 n T l1 l2 ud] in
                 abbrev bndn = hypjoin (bndtrm nextid (sym n)) tt
                               by [I2 n T l1 l2 ud] end in
                 let k = 
                 match create with
                   ff => dec n
                         cast (tcheck_ff nextid symbols T)
                         by cong <tcheck_t nextid symbols * T>
                              symm create_eq
                 | tt => 
                     % get the derivation for G |- n : T
                       existse_term [I4 n T l1 l2 ud]
                         fun(spec b:bool)
                            (spec x:<deriv G' T (sym (tpknd b))>)
                            (ign : True).
                       existse_term
                         [deriv_wk l1 l2 n T T 
                           (sym terminates (tpknd b) by tpknd_tot)
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
                  end in

                  let K = 
                    match expected with
                      nothing ign =>
                      dec s
                      cast
                        (Tcheck_nothing nextid T
                           bndT join (csbst nextid ctxtn T) 
                                     (acanon nextid T))
                      by cong <Tcheck_t nextid * T>
                           symm expected_eq
                    | something ign eT =>
                       match (aequiv inc nextid T eT) by ae ign with
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
                        cast (Tcheck_something nextid T eT
                                [aequiv_conv nextid T eT ae])
                        by cong <Tcheck_t nextid * T>
                             symm expected_eq
                     end %- match aequiv -%
                     end %- let K = match expected -% in
                 (mk_check nextid symbols create expected
                    pb_stdin symbols nextid T k K
                    [x_le_x nextid] 
                    join (trie_interp symbols) (trie_interp symbols))
             end %- match e -% 
         end
        end
      | tt => 

        % check a compound expression (we just parsed a "(")

        match (gs_char pb_stdin) with
          getc_none ign pb_stdin => 
            dec pb_stdin dec expected dec nextid
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
                   
                   abbrev sym'ok = [symbols_ok_le nextid nextid' symbols'
                                      [symbols_ok_cong nextid symbols symbols' 
                                        symok U1]
                                      nle1] in
                   match K1 with
                     Tcheck_nothing ign1 headT headbT' =>
                     abbrev err = 
                       dec pb_stdin dec nextid' dec k1 
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
                       sym n => dec n err
                     | app h1 h2 => dec h1 dec h2 err
                     | lam n1 h1 => dec n1 dec h1 err
                     | pi n1 dom ran => 
                       
                       % check the argument
                       dec headT
                       abbrev bdom = [bndtrm_pi2 nextid' 
                                       headT n1 dom ran headbT' headT_eq] in
                       let dep_ran = (free_in n1 ran) by dep_ran_eq1 in

                       match (msbst nextid' headsG dom) by meq ign with
                         mk_msbst_t nextid'a sdom =>

                       abbrev nle1a = [msbst_le nextid' headsG dom 
                                        nextid'a sdom meq] in
                       match (check pb_stdin symbols' nextid'a 
                                [symbols_ok_le nextid' nextid'a symbols'
                                   sym'ok nle1a]
                                (or create dep_ran)
                                (something trm sdom)
                                hypjoin (bndopttrm nextid'a (something sdom)) tt
                                  by [bndtrm_msbst nextid' headsG dom
                                        nextid'a sdom 
                                        headbsG bdom meq]
                                  end
                                str_app) by ign carg with
                        mk_check ign1 ign2 ign3 ign4 pb_stdin
                         symbols'' nextid'' T2 k2 K2 nle2 U2 =>
                         
                         let pb_stdin = (eat_char pb_stdin where Crp) in

                         match K2 with
                           Tcheck_nothing ign1 ign2 ign3 =>
                             nothing
                         | Tcheck_something ign1 ign2 ign3 aeT2dom =>

                         abbrev nlea2 = [le_trans nextid' nextid'a nextid''
                                           nle1a nle2] in
                         abbrev bdom'' = [bndtrm_le nextid' nextid'' dom
                                           nlea2 bdom] in
                         abbrev headbT'' = [bndtrm_le nextid' 
                                             nextid'' headT
                                             nlea2 headbT'] in
                         abbrev bran'' = [bndtrm_pi3 nextid'' 
                                           headT n1 dom ran
                                           headbT'' headT_eq] in
                         abbrev bn1'' = [bndtrm_pi1 nextid'' 
                                           headT n1 dom ran
                                           headbT'' headT_eq] in
                         abbrev nle12 = [le_trans nextid nextid' nextid''
                                           nle1 nlea2] in

                         % pull back to original ctxt, and cast to dom.
                         abbrev get_d2 = 
                           fun(t2:trm)(d2:<deriv (gs_ctxt symbols') t2 T2>).
                              (dconv G t2 T2 dom aid
                                 cast d2 
                                   by cong <deriv * t2 T2>
                                        symm 
                                        [gs_ctxt_interp symbols 
                                          symbols' U1]
                                 [bndtrm_le nextid'' aid dom
                                    ale bdom'']
                                 aeT2dom) in
                         let tmp =
                         match dep_ran with
                           ff => 
   
                           % simply typed head, so no substitution

                           dec n1

                           abbrev rT = (csbst nextid'' headsG ran) in

                           let K = (Tcheck_nothing nextid'' ran bran'') in
                           match k2 with
                             tcheck_ff ign1 ign2 ign3 =>

                              % not creating

                              let k = cast (tcheck_ff nextid'' symbols rT)
                                      by cong <tcheck_t nextid'' symbols * rT>
                                          symm
                                          [or_eq_ff create dep_ran
                                            inj <tcheck_t ** ** * **> k2_Eq] in
                              dec k1 
                              (mk_check nextid symbols create (nothing trm)
                                 pb_stdin symbols'' nextid'' rT k K 
                                 nle12 trans U1 U2)
                           | tcheck_tt ign1 ign2 ign3 t2 d2 bt2 =>

                              % creating

                             abbrev create_eq = 
                                symm 
                                trans symm inj <tcheck_t ** ** * **> k2_Eq
                                trans cong (or create *) dep_ran_eq
                                           [or_def2ff create] in
                             abbrev d2 = (get_d2 t2 d2) in

                             let k = 
                                match k1 with
                                  tcheck_ff ign1 ign2 ign3 => 
                                  impossible 
                                    trans symm inj <tcheck_t ** ** * **> k1_Eq
                                      trans create_eq
                                            clash tt ff
                                    <tcheck_t nextid'' symbols create rT>
                                | tcheck_tt ign1 ign2 ign3 t1 d1 bt1 =>

                                  abbrev ci = 
                                    (csbst_nextid nextid' headsG headT) in

                                  abbrev cile = [csbst_nextid_le] in
                                  abbrev d1 =
                                    (dconv G t1 T1 
                                      (csbst nextid' headsG headT)
                                      ci d1
                                      [bndtrm_csbst_nextid nextid' headsG headT
                                        headbT' headbsG]
                                      trans symm [acanon_idem nextid' ci headT
                                                    headbT' cile]
                                        cong (acanon ci *) symm headae) in
                                      

                                  existse_term 
                                    [dapp_simple n1 dom ran
                                       G t1 t2 trans symm dep_ran_eq1 dep_ran_eq
                                       cast (nothing show d1 end) by cong <deriv G t1 *> headT_eq
                                       d2]
                                  fun(spec d2:<deriv G (app t1 t2) ran>)
                                     (ign:True).
                                  cast 
                                  (tcheck_tt nextid'' symbols ran
                                    (app t1 t2)
                                    d2
                                    hypjoin (bndtrm nextid'' (app t1 t2)) tt
                                     by [bndtrm_le nextid' nextid'' t1
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
                               <check_app_t nextid symbols create (nothing trm)>
                           | tcheck_tt ign1 ign2 ign3 t2 d2 bt2 =>

                             abbrev d2 = (get_d2 t2 d2) in
                             let sG = terminates
                                         (ctxtc n1 inc t2 inc ctxtn) 
                                       by ctxtc_tot in
                             abbrev bsG = trans cong (bndctxt nextid'' *) 
                                                   sG_eq
                                                hypjoin (bndctxt nextid''
                                                          (ctxtc n1 t2 ctxtn))
                                                        tt
                                                by bt2 end in
                             match (msbst inc nextid'' sG ran) by eq_sran ign with
                             mk_msbst_t nextid''' sran =>
                              dec ran dec sG
                              abbrev bsran = [bndtrm_msbst nextid'' sG
                                              ran nextid''' sran
                                              bsG bran'' eq_sran] in
                              abbrev nle3 = [msbst_le nextid'' sG
                                              ran nextid''' sran
                                              eq_sran] in
                              abbrev nle23 = [le_trans nextid' nextid'' nextid'''
                                               nle2 nle3] in

                              let K = (Tcheck_nothing nextid''' sran 
                                         [bndtrm_msbst nextid'' sG
                                           ran nextid''' sran bsG
                                           bran'' eq_sran]) in
                              let k = 
                                match k1 with
                                  tcheck_ff ign1 ign2 ign3 => 
                                  dec t2
                                  cast (tcheck_ff nextid'' symbols sran)
                                  by cong <tcheck_t nextid'' symbols * sran>
                                      symm inj <tcheck_t ** ** * **> k1_Eq
                                | tcheck_tt ign1 ign2 ign3 t1 d1 bt1 =>
                                  cast 
                                  (tcheck_tt nextid'' symbols sran
                                    (app t1 t2)
                                    cast
                                    (dapp G t1 t2 n1 dom ran nextid''
                                       cast d1 by cong <deriv G t1 *> headT_eq
                                       d2
                                       bt2 bran'' bn1'')
                                    by cong <deriv G (app t1 t2) *>
                                        hypjoin (sbst nextid'' t2 n1 ran) sran
                                          by eq_sran sG_eq end
                                    hypjoin (bndtrm nextid'' (app t1 t2)) tt
                                     by [bndtrm_le nextid' nextid'' t1
                                          nle2
                                          bt1]
                                        bt2 end)
                                  by cong <tcheck_t nextid'' symbols * sran>
                                      symm inj <tcheck_t ** ** * **> k1_Eq
                                end %- k1 -%  in 
                              (mk_check nextid symbols create (nothing trm)
                                 pb_stdin symbols'' nextid''' sran k K 
                                 [le_trans nextid nextid'' nextid''' 
                                    nle12 nle3]
                                 trans U1 U2)
                             end
                           end
                         end %- dep_ran -% in
     
                         % now just check alpha-equivalence of the 
                         % type produced above with the expected one.
                         match expected with
                           nothing ign => 
                           cast tmp 
                           by cong <check_t nextid symbols create *>
                               symm expected_eq
                         | something ign eT =>
                           match tmp with
                            mk_check ign1 ign2 ign3 ign4 pb_stdin
                              rsymbols rnextid rT rk rK rnle rU =>

                            match rK with
                              Tcheck_nothing ign rT brT =>
                              match (aequiv inc rnextid rT eT) by ae ign with
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
                              dec eT dec pb_stdin dec rnextid dec rk 
                              dec rsymbols dec rT dec pnextid
                              r
                             | tt =>
                             dec eT dec rT 

                             let rK = cast
                                        (Tcheck_something rnextid rT eT
                                           [aequiv_conv rnextid rT eT ae])
                                        by cong <Tcheck_t rnextid * rT>
                                            symm expected_eq in
                               (mk_check nextid symbols create expected
                                 pb_stdin rsymbols rnextid rT 
                                 rk rK rnle rU)
                             end %- aequiv -%
                            | Tcheck_something ign1 ign2 ign3 ign4 => nothing
                            end %- rK -%
                          end %- tmp -%
                         end %- expected -% 
                         end %- K2 -%
                       end %- check arg -%
                       end %- substitute into domain -%
                     end %- headT -%
                   | Tcheck_something ign1 ign2 ign3 ign4 => nothing
                   end %- K1 -%
              end

            | tt => 

              % pi case

              % first read the pi-bound variable
              match (gs_get_chars pb_stdin str_pi ff ff) with
                mk_gs_get_chars pb_stdin s =>
  
                match create with
                  ff => 
                    dec pb_stdin dec nextid dec s dec expected
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
                  dec pb_stdin dec nextid dec s 
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
                           (something trm (sym inc tp)) 
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
                | Tcheck_something ign1 ign2 ign3 acT1tp =>

                  abbrev sym'ok = [symbols_ok_cong nextid symbols symbols' 
                                     symok U1] in

                  abbrev d1 = (dconv G t1 T1 (sym tp) aid
                                 d1 [bndtrm_le nextid aid (sym tp)
                                       [le_trans nextid nextid' aid
                                          nle1 ale] I5]
                                 acT1tp) in

                  let inssymbols = (trie_insert symbols_e inc s
                                     (mkpair nat trm inc nextid' inc t1) 
                                     symbols') in
                  existse_term [trie_insert_interp symbols_e 
                                 symbols' inssymbols
                                 s (mkpair nat trm inc nextid' t1)
                                 symm inssymbols_eq]
                  fun(spec L1 L2:<list <pair string symbols_e>>)
                     (inssymi : 
                      { (trie_interp inssymbols) = 
                        (append L1 (cons (mkpair s (mkpair nextid' t1)) L2))}).
                  abbrev G1 = 
                   terminates (map <pair string symbols_e> symbols_e
                                 Unit unit
                                 fun(u:Unit).(snd string symbols_e) L1)
                   by [map_total string symbols_e L1 snd sndTot] in
                  abbrev G2 = 
                   terminates (map <pair string symbols_e> symbols_e
                                 Unit unit 
                                 fun(u:Unit).(snd string symbols_e) L2)
                   by [map_total string symbols_e L2 snd sndTot] in
                  abbrev inssymr = [trie_interp_range2 symbols_e inssymbols
                                     s (mkpair nat trm nextid' t1) L1 L2
                                     inssymi] in
                  abbrev inssymctxt = 
                    trans join (gs_ctxt inssymbols)
                               (trie_range inssymbols)
                    trans inssymr
                          join (append G1 (cons (mkpair nextid' t1) G2))
                               (append G1 (ctxtc nextid' t1 G2)) in
                      
                  match (check pb_stdin inssymbols (S inc nextid') 
                              [symbols_ok_insert_next nextid' 
                              symbols' inssymbols s t1 
                              [symbols_ok_le nextid nextid' symbols' 
                                 sym'ok nle1]
                              inssymbols_eq]
                           tt
                           (something trm inc eT) 
                           trans cong (bndopttrm (S nextid') *) 
                                   symm expected_eq
                             [bndopttrm_le nextid (S nextid') expected
                               [le_trans nextid nextid' (S nextid')
                                  nle1 [le_S nextid']] 
                               bndexpected]
                           str_pi) with
                    mk_check ign1 ign2 ign3 ign4 pb_stdin symbols'' nextid'' 
                         T2 k2 K2 nle2 U2 =>

                    match k2 with
                      tcheck_ff ign1 ign2 ign3 => nothing
                    | tcheck_tt ign1 ign2 ign3 t2 d2 bt2 =>       

                    match K2 with
                      Tcheck_nothing ign1 T2 bT2 => nothing
                    | Tcheck_something ign1 ign2 ign3 acT2eT =>

                    let pb_stdin = (eat_char pb_stdin where Crp) in
                     abbrev eTistp = (istp eT) in
                     abbrev eTisknd = (isknd eT) in
                     match (or eTistp eTisknd) by eTistpknd ign with
                       ff => 
                       dec pb_stdin dec t1 dec nextid'
                       dec s dec nextid'' dec oprev

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
                       abbrev Pnextid' = [ltle_trans nextid' (S nextid') nextid''
                                            [lt_S nextid'] nle2] in
                       abbrev Pnextid = [lelt_trans nextid nextid' nextid''
                                           nle1 
                                           Pnextid'] in
                       abbrev d2 = (dconv (gs_ctxt inssymbols)
                                     t2 T2 eT aid
                                     d2 [bndtrm_le nextid aid eT
                                          [le_trans nextid nextid'' aid
                                            [lt_implies_le nextid nextid''
                                              Pnextid]
                                            ale]
                                          hypjoin (bndtrm nextid eT) tt 
                                            by bndexpected expected_eq end]
                                     acT2eT) in

                    existse_term 
                      [deriv_perm 
                         terminates (gs_ctxt inssymbols) by gs_ctxt_tot
                         t2 eT G1 G2 nextid' t1 d2
                         inssymctxt]
                    fun(spec d2:<deriv 
                                   (ctxtc nextid' t1 (append ctxte G1 G2))
                                   t2 eT>)
                       (ign:True).

                       abbrev lookup' = [trie_lookup_same_interp symbols_e 
                                          symbols symbols' s oprev
                                          symm oprev_eq1 U1] in

                  abbrev symbolsi =
                     foralli(oprev_eq : { oprev = nothing }).
                        trans U1
                          [trie_insert_new symbols_e symbols'
                             inssymbols s (mkpair nat trm nextid' t1)
                             trans lookup' oprev_eq
                             symm inssymbols_eq
                             L1 L2 inssymi] in

                  abbrev symctxt_something = 
                          foralli(prev:<pair nat trm>)
                                 (oprev_eq : { oprev = (something prev)}).
                           trans join G
                                   (map unit fun(u).snd 
                                      (trie_interp symbols))
                           trans cong (map unit fun(u).snd *) 
                                  [trie_insert_lookup_interp symbols_e
                                     symbols symbols' inssymbols s 
                                     (mkpair nat trm nextid' t1)
                                     prev
                                     trans symm oprev_eq1 oprev_eq
                                     U1
                                     symm inssymbols_eq
                                     L1 L2 inssymi] 
                           trans [map_append <pair string <pair nat trm>>
                                   <pair nat trm> Unit unit 
                                   fun(u:Unit).(snd string <pair nat trm>)
                                   L1 (cons <pair string <pair nat trm>>
                                        (mkpair string <pair nat trm>
                                          s prev)
                                        L2)] 
                               cong (append G1 *)
                                  join (map unit fun(u).snd 
                                         (cons (mkpair s prev) L2))
                                       (cons prev G2) in

                       % pull d2 back from symbols'' to an extension of symbols
                       abbrev d2 = 
                         match oprev with 
                          nothing A => 
                          abbrev symctxt_nothing = 
                           trans join G
                                  (map unit fun(u).snd 
                                    (trie_interp symbols))
                           trans cong (map unit fun(u).snd *) 
                                  [symbolsi oprev_eq]
                             [map_append <pair string <pair nat trm>>
                                <pair nat trm> Unit unit 
                                fun(u:Unit).(snd string <pair nat trm>)
                                L1 L2] in
                          cast d2
                          by cong <deriv (ctxtc nextid' t1 *) t2 eT>
                               symm symctxt_nothing
                      | something ign prev => 
                           abbrev G1' = (ctxtc nextid' t1 G1) in
                           abbrev GG = (append ctxte G1' (cons ctxte prev G2)) in
                           abbrev origG = (append ctxte G1 (cons ctxte prev G2)) in
                           abbrev GG' = (ctxtc nextid' t1 origG) in
                        abbrev diffidsGG = 
                            [cong_diffids GG' GG
                                 [diffids_wk origG nextid' t1
                                    [cong_diffids G origG I1
                                      [symctxt_something prev oprev_eq]]
                                    [idsbnd1_le nextid nextid' 
                                       origG [cong_idsbnd1 nextid G origG
                                               I2 [symctxt_something prev oprev_eq]]
                                       nle1]]
                                  join GG' GG] in
                         existse_term 
                           [deriv_wk1 G1' G2 prev t2 eT 
                              diffidsGG
                              cast d2
                              by cong <deriv * t2 eT>
                                   join (ctxtc nextid' t1 (append G1 G2))
                                        (append (ctxtc nextid' t1 G1) G2)]
                        fun(spec d2:<deriv GG t2 eT>)
                           (ign:True).
                        
                          cast d2
                          by trans cong <deriv * t2 eT>
                                     join GG GG'
                               cong <deriv (ctxtc nextid' t1 *) t2 eT>
                                 symm [symctxt_something prev oprev_eq]
                      end in

                      abbrev bpi = 
                            hypjoin (bndtrm nextid'' (pi nextid' t1 t2)) tt
                            by Pnextid'
                               [bndtrm_le nextid' nextid'' t1 
                                 [lt_implies_le nextid' nextid'' Pnextid'] bt1]
                               bt2 end in

                     let k = 
                       (tcheck_tt nextid'' symbols eT 
                          (pi nextid' t1 t2)
                          cast
                            (dpi G nextid' t1 t2 eTistp
                               d1 cast d2
                                  by cong <deriv (ctxtc nextid' t1 G)
                                             t2 *>
                                       PeT)
                            by cong <deriv G (pi nextid' t1 t2) *>
                                symm PeT                    
                          bpi) in
                      
                     let K = (Tcheck_something nextid'' eT eT
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
                             s (mkpair nat trm nextid' t1) 
                             symm remsymbols_eq L1 L2
                             trans symm U2
                                   inssymi] in
                       (mk_check nextid symbols tt (something trm eT)
                          pb_stdin remsymbols nextid'' eT k K
                          [lt_implies_le nextid nextid'' Pnextid]
                          trans [symbolsi oprev_eq] symm remsymbolsi)
                           
                     | something ign prev => 
                     
                       let rsymbols = (trie_insert symbols_e s prev symbols'') in
                        abbrev symrsymi = trans U1
                                   [trie_restore_interp symbols_e symbols'
                                     inssymbols symbols'' rsymbols s prev 
                                     (mkpair nat trm nextid' t1)
                                     trans lookup' oprev_eq
                                     symm inssymbols_eq
                                     U2 symm rsymbols_eq ] in
                        (mk_check nextid symbols tt (something trm eT)
                          pb_stdin rsymbols nextid'' eT k K
                          [lt_implies_le nextid nextid'' Pnextid]
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
                dec pb_stdin dec nextid 
                let r = 
                (handle_error_sym_unique
                  <check_t nextid symbols create expected>
                  symbols
                  (string_app "A lambda-expression appears in an "
                           "invalid position (a type-synthesizing one).")) in
                dec symbols r
            | something ign eT =>

              abbrev handle_err = 
                dec pb_stdin dec nextid 
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
                sym n => dec n handle_err
              | app t1 t2 => dec t1 dec t2 handle_err
              | lam n t1 => dec n dec t1 handle_err
              | pi n1 dom ran => 
                
                dec eT 

                % read the lambda-bound variable
                match (gs_get_chars pb_stdin str_lam ff ff) with
                  mk_gs_get_chars pb_stdin s =>
                
                  % get previous binding for the var.
                  let oprev = (trie_lookup symbols_e symbols s) by oprev_eq1 in 
                  
                  let inssymbols = (trie_insert symbols_e inc s
                                     (mkpair nat trm inc nextid dom) 
                                     symbols) in
                  existse_term [trie_insert_interp symbols_e 
                                 symbols inssymbols
                                 s (mkpair nat trm nextid dom)
                                 symm inssymbols_eq]
                  fun(spec L1 L2:<list <pair string symbols_e>>)
                     (inssymi : 
                      { (trie_interp inssymbols) = 
                        (append L1 (cons (mkpair s (mkpair nextid dom)) L2))}).
                  abbrev G1 = 
                   terminates (map <pair string symbols_e> symbols_e
                                 Unit unit
                                 fun(u:Unit).(snd string symbols_e) L1)
                   by [map_total string symbols_e L1 snd sndTot] in
                  abbrev G2 = 
                   terminates (map <pair string symbols_e> symbols_e
                                 Unit unit 
                                 fun(u:Unit).(snd string symbols_e) L2)
                   by [map_total string symbols_e L2 snd sndTot] in
                  abbrev inssymr = [trie_interp_range2 symbols_e inssymbols
                                     s (mkpair nat trm nextid dom) L1 L2
                                     inssymi] in
                  abbrev inssymctxt = 
                    trans join (gs_ctxt inssymbols)
                               (trie_range inssymbols)
                    trans inssymr
                          join (append G1 (cons (mkpair nextid dom) G2))
                               (append G1 (ctxtc nextid dom G2)) in
                      
                  let sG = terminates (ctxtc n1 (sym inc nextid) inc ctxtn) 
                           by ctxtc_tot in
                  match (msbst (S inc nextid) sG ran) by meq ign with
                    mk_msbst_t nextid' ran' =>

                    dec sG dec ran
                    abbrev meq1 = trans cong (msbst (S nextid) * ran)
                                         symm sG_eq
                                       meq in
                    abbrev PSnextid = [msbst_le (S nextid) sG ran nextid' ran'
                                        meq] in
                    abbrev Pnextid1 = [ltle_trans nextid (S nextid) nextid'
                                        [lt_S nextid] PSnextid] in

                    abbrev bran' = [bndtrm_msbst (S nextid) sG ran nextid' ran'
                                     hypjoin (bndctxt (S nextid) sG) tt
                                      by [lt_S nextid] sG_eq end
                                     [bndtrm_le nextid (S nextid) ran [le_S nextid]
                                      [bndtrm_pi3 nextid eT n1 dom ran
                                        hypjoin (bndtrm nextid eT) tt
                                         by bndexpected expected_eq end
                                        eT_eq]]
                                     meq] in
                    match (check pb_stdin inssymbols nextid'
                            [symbols_ok_le (S nextid) nextid' inssymbols
                              [symbols_ok_insert_next nextid symbols inssymbols
                                s dom symok inssymbols_eq]
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

                      abbrev Pnextid2 = [ltle_trans nextid nextid' nextid''
                                          Pnextid1 nle] in

                      abbrev Pnextid2a = 
                         [lt_implies_le nextid nextid'' Pnextid2] in

                      abbrev symbolsi =
                         foralli(oprev_eq : { oprev = nothing }).
                              [trie_insert_new symbols_e symbols
                                inssymbols s (mkpair nat trm nextid dom)
                                trans symm oprev_eq1 oprev_eq
                                symm inssymbols_eq
                                L1 L2 inssymi] in
                      cast
                      match rk with
                        tcheck_ff ign1 ign2 ign3 =>
                        
                        dec rK dec nextid
                        abbrev create_eq = inj <tcheck_t ** ** * **> rk_Eq in
                        
                        let K = (Tcheck_something nextid'' eT eT
                                  join (acanon nextid'' eT)
                                       (acanon nextid'' eT)) in
                        let k = (tcheck_ff nextid'' symbols eT) in

                        cast
                        match oprev with
                          nothing A => 

                          let remsymbols = (trie_remove symbols_e s symbols') in
                          dec s
                          abbrev remsymbolsi =
                            [trie_remove_interp symbols_e symbols' remsymbols
                               s (mkpair nat trm nextid dom) 
                               symm remsymbols_eq L1 L2
                               trans symm U
                                     inssymi] in

                          (mk_check nextid symbols ff (something trm eT)
                            pb_stdin remsymbols nextid'' eT k K
                            Pnextid2a
                            trans [symbolsi oprev_eq] symm remsymbolsi)
                           
                        | something ign prev => 
                     
                          let rsymbols = 
                               (trie_insert symbols_e s prev symbols') in
                          abbrev symrsymi = 
                                   [trie_restore_interp symbols_e symbols
                                     inssymbols symbols' rsymbols s prev 
                                     (mkpair nat trm nextid dom)
                                     trans symm oprev_eq1 oprev_eq
                                     symm inssymbols_eq
                                     U symm rsymbols_eq ] in

                          (mk_check nextid symbols ff (something trm eT)
                            pb_stdin rsymbols nextid'' eT k K
                            Pnextid2a
                            symrsymi)

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
                                  rettp (pi n1 dom ran) 
                                  [acanon_rename_pi nextid'' 
                                    nextid n1 dom ran' ran])
                          by cong <Tcheck_t nextid'' (something *) rettp> 
                               symm eT_eq in

                        abbrev bran'' = [bndtrm_le nextid' nextid'' ran'
                                          nle bran'] in

                        abbrev GG = (ctxtc nextid dom (append ctxte G1 G2)) in
                        existse_term 
                         [deriv_perm 
                           terminates (gs_ctxt inssymbols) by gs_ctxt_tot
                           t1 rT G1 G2 nextid dom d1
                           inssymctxt]
                        fun(spec d1:<deriv GG t1 rT>)
                           (ign:True).

                        match rK with
                          Tcheck_nothing ign1 ign2 ign3 => nothing
                        | Tcheck_something ign1 ign2 ign3 ae =>
                        abbrev d1 = (dconv GG t1 rT ran' aid d1 
                                     [bndtrm_le nextid'' aid ran'
                                          ale bran''] 
                                     ae) in
                        cast
                        match oprev with
                          nothing A => 

                          let remsymbols = (trie_remove symbols_e s symbols') in
                          dec s
                          abbrev remsymbolsi =
                            [trie_remove_interp symbols_e symbols' remsymbols
                               s (mkpair nat trm nextid dom) 
                               symm remsymbols_eq L1 L2
                               trans symm U
                                     inssymi] in
                          
                          abbrev symctxt_nothing = 
                           trans join G
                                  (map unit fun(u).snd 
                                    (trie_interp symbols))
                           trans cong (map unit fun(u).snd *) 
                                  [symbolsi oprev_eq]
                             [map_append <pair string <pair nat trm>>
                                <pair nat trm> Unit unit 
                                fun(u:Unit).(snd string <pair nat trm>)
                                L1 L2] in
                          let k = 
                            (tcheck_tt nextid'' symbols rettp
                               (lam nextid t1)
                               (dlam G t1 nextid dom ran' 
                                  cast d1
                                  by cong <deriv (ctxtc nextid dom *) t1 ran'>
                                      symm symctxt_nothing)
                               blam) in

                          (mk_check nextid symbols tt (something trm eT)
                            pb_stdin remsymbols nextid'' rettp k K
                            Pnextid2a
                            trans [symbolsi oprev_eq] symm remsymbolsi)
                           
                        | something ign prev => 
                     
                          let rsymbols = 
                               (trie_insert symbols_e s prev symbols') in
                          abbrev symrsymi = 
                                   [trie_restore_interp symbols_e symbols
                                     inssymbols symbols' rsymbols s prev 
                                     (mkpair nat trm nextid dom)
                                     trans symm oprev_eq1 oprev_eq
                                     symm inssymbols_eq
                                     U symm rsymbols_eq ] in
                          abbrev symctxt_something = 
                          foralli(prev:<pair nat trm>)
                                 (oprev_eq : { oprev = (something prev)}).
                           trans join G
                                   (map unit fun(u).snd 
                                      (trie_interp symbols))
                           trans cong (map unit fun(u).snd *) 
                                  [trie_insert_lookup_interp symbols_e
                                     symbols symbols inssymbols s 
                                     (mkpair nat trm nextid dom)
                                     prev
                                     trans symm oprev_eq1 oprev_eq
                                     join (trie_interp symbols) 
                                          (trie_interp symbols)
                                     symm inssymbols_eq
                                     L1 L2 inssymi] 
                           trans [map_append <pair string <pair nat trm>>
                                   <pair nat trm> Unit unit 
                                   fun(u:Unit).(snd string <pair nat trm>)
                                   L1 (cons <pair string <pair nat trm>>
                                        (mkpair string <pair nat trm>
                                          s prev)
                                        L2)] 
                               cong (append G1 *)
                                  join (map unit fun(u).snd 
                                         (cons (mkpair s prev) L2))
                                       (cons prev G2) in

                          abbrev G1' = (ctxtc nextid dom G1) in
                          abbrev GG = (append ctxte G1' (cons ctxte prev G2)) in
                          abbrev origG = (append ctxte G1 (cons ctxte prev G2)) in
                          abbrev GG' = (ctxtc nextid dom origG) in
                          abbrev GorigG = [symctxt_something prev oprev_eq] in
                          abbrev diffidsGG = 
                            [cong_diffids GG' GG
                              [diffids_wk origG nextid dom
                                 [cong_diffids G origG I1 GorigG]
                                 [cong_idsbnd1 nextid G origG I2 GorigG]]
                              join GG' GG] in
                          existse_term 
                           [deriv_wk1 G1' G2 prev t1 ran'
                              diffidsGG
                              cast d1
                              by cong <deriv * t1 ran'>
                                   join (ctxtc nextid dom (append G1 G2))
                                        (append (ctxtc nextid dom G1) G2)]
                         fun(spec d1:<deriv GG t1 ran'>)
                            (ign:True).
                        
                         let k =
                          (tcheck_tt nextid'' symbols rettp
                            (lam nextid t1)
                            (dlam G t1 nextid dom ran'
                             cast d1
                             by trans cong <deriv * t1 ran'>
                                       join GG GG'
                                  cong <deriv (ctxtc nextid dom *) t1 ran'>
                                    symm [symctxt_something prev oprev_eq])
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
                end %- gs_get_chars -%
              end %- eT -%
            end %- expected -%
          end %- (eqchar Cbs) -%
          
          % finished processing compound expression

        end %- (gs_char pb_stdin) -%
      end
    end.

