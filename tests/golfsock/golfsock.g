%Set "show_includes".
%Set "print_parsed".
Set "check_spec_terminates".
Set "trust_hypjoins".
Include trusted "../../lib/trie.g".

%Include "../../lib/trie.g".

Include "gs_io.g".
Include "check.g".

Inductive cmd_result_t : type :=
  cmd_result : Fun(cont:bool)
                  (unique pb_stdin:pb_stdin_t)
                  (unique symbols:symbols_t)
                  (nextid : var)
                  (spec symok:@<symbols_ok nextid symbols>).
                  cmd_result_t.

Define cmd_handler_t := Fun(classifier:var)
                           (unique pb_stdin:pb_stdin_t)
                           (unique symbols:symbols_t)
                           (nextid : var)
                           (bc : { (vlt classifier nextid) = tt})
                           (spec symok:@<symbols_ok nextid symbols>).
                           cmd_result_t.

Define dispatcher_t := <trie <pair bool cmd_handler_t>>.

Define str_top_level_command := "top-level command".
Define str_declare := "declare command".
Define str_check := "check command".

%Set "print_parsed".

Define handle_declare : cmd_handler_t :=
  fun(classifier:var)
     (unique pb_stdin:pb_stdin_t)
     (unique symbols:symbols_t)
     (nextid : var)
     (bc : { (vlt classifier nextid) = tt})
     (spec symok:@<symbols_ok nextid symbols>) :unique cmd_result_t.
    match (gs_get_chars pb_stdin str_declare ff tt %- disallow_empty -%) with
      mk_gs_get_chars pb_stdin s =>
        match (check pb_stdin symbols nextid symok tt
                 (something trm (sym classifier)) 
                 hypjoin (bndopttrm nextid (something (sym classifier))) tt
                   by bc end
                 str_declare)
        by c_eq c_Eq with 
          mk_check ign1 ign2 ign3 ign4 pb_stdin symbols' nextid' T 
            k K nle U =>
 
            match k with
              tcheck_ff ign1 ign2 ign3 => nothing
            | tcheck_tt ign1 ign2 ign3 t d bt =>
              match K with
                Tcheck_nothing ign1 T bT => nothing
              | Tcheck_something ign1 ign2 ign3 ign4 ign5 ign6 => 
                let symbols'' = 
                   (trie_insert symbols_e s 
                     (mkpair var trm nextid' t) symbols') in
                 match (vS nextid') by Snextid'_eq ign with
                 mk_word_inc_t Snextid' carry =>
                 match carry with
                 ff => 

                 abbrev Snextid'_eq = trans Snextid'_eq 
                                        cong (mk_word_inc_t Snextid' *)
                                          carry_eq in

                 (cmd_result tt pb_stdin symbols'' Snextid'
                    [symbols_ok_insert_next nextid' symbols' symbols'' 
                      s t Snextid'
                      symm [word_to_nat_inc2 nextid' Snextid'
                            Snextid'_eq]
                      [symbols_ok_cont nextid nextid' 
                        symbols symbols' symok U nle]
                      symbols''_eq])
                 | tt %- carry -% => abort cmd_result_t
                 end %- check carry -%
                 end %- increment nextid' -%
              end %- match K -%
            end  %- match k -%
       end 
    end.

Define handle_check : cmd_handler_t :=
  fun(classifier:var)
     (unique pb_stdin:pb_stdin_t)
     (unique symbols:symbols_t)
     (nextid:var)
     (bc:{(vlt classifier nextid) = tt})
     (spec symok:@<symbols_ok nextid symbols>) :unique cmd_result_t.
     match (check pb_stdin symbols nextid symok tt 
              (something trm (sym classifier)) 
              hypjoin (bndopttrm nextid (something (sym classifier))) tt
               by bc end
              str_check)
     by c_eq c_Eq with 
       mk_check ign1 ign2 ign3 ign4 pb_stdin symbols' nextid' T 
         k K nle U =>

         dec K
         match k with
           tcheck_ff ign1 ign2 ign3 => nothing
         | tcheck_tt ign1 ign2 ign3 t d bt =>

           abbrev sym'ok = [symbols_ok_cont nextid nextid' symbols symbols'
                             symok U nle] in
           match (check pb_stdin symbols' nextid'
                    sym'ok
                    ff (something trm t) 
                    hypjoin (bndopttrm nextid' (something t)) tt by bt end
                    str_check) 
           by c_eq c_Eq with 
             mk_check ign1 ign2 ign3 ign4 pb_stdin symbols'' nextid'' T 
               k2 K2 nle U =>

             dec k2 dec K2
             (cmd_result tt pb_stdin symbols'' nextid''
                [symbols_ok_cont nextid' nextid'' symbols' symbols''
                   sym'ok U nle])
           end
         end
     end.

Define initialize_dispatcher : Fun(u:Unit).unique dispatcher_t :=
  fun(u:Unit):unique dispatcher_t.
    (trie_insert <pair bool cmd_handler_t> "declare-term" 
                               (mkpair bool cmd_handler_t tt handle_declare)
    (trie_insert <pair bool cmd_handler_t> "declare-type" 
                               (mkpair bool cmd_handler_t ff handle_declare)
    (trie_insert <pair bool cmd_handler_t> "check-term" 
                               (mkpair bool cmd_handler_t tt handle_check) 
      (trie_none <pair bool cmd_handler_t>)))).

Define dispatch :=
  fun(s:string)(unique pb_stdin:pb_stdin_t)(unique symbols:symbols_t)
     (nextid:var)
     (spec symok:@<symbols_ok nextid symbols>)
     (unique_owned dispatcher:dispatcher_t).
     let oh = (trie_lookup <pair bool cmd_handler_t> dispatcher s) in
       match oh with
         nothing ign => dec pb_stdin 
                let r = (handle_error_sym cmd_result_t
                         symbols
                         (string_app "Unrecognized command " 
                         (string_app (stringc Cdq s) 
                                     (stringc Cdq inc stringn))))
                in dec symbols r
       | something ign a =>
         match a with
           mkpair ign1 ign2 use_tp handler =>
             dec s
            existse_term symok
            fun(I1 : @<diffids (gs_ctxt symbols)>)
               (I2 : @<idsbnd1 nextid (gs_ctxt symbols)>)
               (I3 : @<idsbnd2 nextid (gs_ctxt symbols)>)
               (I4 : @<decsderiv (gs_ctxt symbols)>)
               (I5 : { (bndtrm nextid (sym tp)) = tt})
               (ign : True).
             abbrev P = hypjoin (vlt tp nextid) tt by I5 end in
             match use_tp with
               ff => 
               (handler knd pb_stdin symbols nextid 
                  [vlt_trans knd tp nextid
                     [vlt_S knd tp 
                       join (word_inc knd) (mk_word_inc_t tp ff)] 
                     P]
                  symok)
             | tt =>
               (handler tp pb_stdin symbols nextid P symok)

             end
         end
       end.

Define consume_input :=
  fun consume_input(unique pb_stdin:pb_stdin_t)
                   (unique dispatcher:dispatcher_t)
                   (unique symbols:symbols_t)
                   (nextid:var)
                   (spec symok:@<symbols_ok nextid symbols>):Unit.
  match (gs_char pb_stdin) with
     getc_none ign pb_stdin' => 
       dec pb_stdin' dec dispatcher dec symbols 
       unit %- no more input -%
   | getc_char ign c pb_stdin' =>
     match (eqchar c Clp) with
       ff => dec pb_stdin' dec dispatcher 
         let r = (handle_error_sym Unit
                  symbols
                  (string_app "Expected a left parenthesis to start "
                  (string_app "a command, but encountered '" 
                       (stringc c (stringc Csq inc stringn))))) in
         dec symbols r
     | tt => 
       match (gs_get_chars pb_stdin' str_top_level_command 
                ff tt %- disallow_empty -%) with
         mk_gs_get_chars pb_stdin' s =>
         match (dispatch s pb_stdin' symbols nextid symok dispatcher) with
           cmd_result cont pb_stdin symbols nextid symok =>
             match cont with
               ff => dec dispatcher dec symbols dec pb_stdin 
                     unit
             | tt => 
               match (gs_char pb_stdin) with
                 getc_none ign pb_stdin' => 
                   dec pb_stdin' dec dispatcher dec symbols 
                   unit %- no more input -%
               | getc_char ign c pb_stdin' =>
                 match (eqchar c Crp) with
                   ff => 
                   dec pb_stdin' dec dispatcher 
                   let r = 
                   (handle_error_sym Unit symbols
                    (string_app "Expected a right parenthesis to end "
                    (string_app "a command, but encountered '" 
                         (stringc c (stringc Csq inc stringn))))) in
                   dec symbols r
                 | tt =>
                   (consume_input pb_stdin' dispatcher symbols nextid symok)
                 end
               end
             end
         end
       end
     end
   end.

Define main :=
  fun(unique stdin:stdin_t).
    let ign = mk_ucvmod_t2 in % so we will compile this
    let dispatcher = (initialize_dispatcher unit) in 
    let pb_stdin = (mk_pb_stdin inc stringn stdin) in
    let ign = (consume_input pb_stdin dispatcher (initial_symbols unit) 
                 first_id initial_symbols_ok) in
      Z.

Unset "check_spec_terminates". %- not behaving properly during compilation -%

%Set "debug_check_refs".
%Set "no_expand_vars".
%Set "show_some_computed_types".
%Set "debug_eta_expand".
%Set "debug_compiler_free_vars".
%Set "debug_classify_apps".
%Set "debug_drop_noncomp".
%Set "print_ownership_annos".
%Set "compiler_print_initial_context".
%Set "debug_flatten_types".
%Set "print_pattern_var_types".
%Set "debug_add_lets".
%Set "debug_split_by_arity".
%Set "comment_vars".
%Set "Debug_compiler".
%Set "debug_uniquify_vars".
%Set "comment_vars". 
%Set "debug_classify_casts".
%Set "debug_compiler_emit".
%Set "debug_compiler_emit_details".
%Set "debug_refine_cases".
%Set "expand_vars".

%Set "print_trusted_details".

Compile main to "golfsock.c".
