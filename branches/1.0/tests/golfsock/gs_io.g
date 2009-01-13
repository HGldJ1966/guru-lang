Include "../../lib/pb_stdin.g".
Include "symbols.g".

%-
Inductive gs_io : type :=
  mk_gs_io : Fun(unique pb_stdin:pb_stdin_t)
                (line:word)
                (
-%

Define print_symbols :=
  fun(unique_owned symbols:symbols_t).
  let ign = (print_string "Symbol table:") in
  let ign = (print_char Cnl) in
  let l = (trie_interp symbols_e symbols) in
  let ign = 
  (foldr <pair string symbols_e> Unit Unit
     unit 
     fun(u:Unit)(owned x:<pair string symbols_e>)(u:Unit).
       match x with
         mkpair ign1 ign2 s e =>
           let ign = (print_string inc s) in
           let ign = (print_string " --> ") in
           match e with
             mkpair ign1 ign2 n t =>
%-             let ign = (print_var n) in
             let ign = (print_string " : ") in -%
             let ign = (print_string (trm_to_string t)) in
               (print_char Cnl) 
           end
       end
     unit
     l) in dec l ign.

Define handle_error_sym :=
  fun(A:type)(unique_owned symbols:symbols_t)(msg:string).
    let ign = (print_string msg) in
    let ign = (print_char Cnl) in
    let ign = (print_char Cnl) in
    let ign = (print_symbols symbols) in
    let ign = (print_char Cnl) in
      abort A.

Define handle_error_sym_unique :=
  fun(A:type)(unique_owned symbols:symbols_t)(msg:string):unique A.
    let r = (handle_error_sym A symbols msg) in
    dec r
      abort A.

Define handle_error :=
  fun(A:type)(msg:string).
    let ign = (print_string msg) in
    let ign = (print_char Cnl) in
      abort A.

Define handle_error_unique :=
  fun(A:type)(msg:string):unique A.
    let r = (handle_error A msg) in
    dec r
      abort A.

%- comments to the end of the line are initiated with '%'. -%
Define gs_comment_char := Cpe.

% next non-whitespace, non-comment character
Define gs_char := 
  (next_nonws_noncomment pb_stdin_t pb_stdin_reader gs_comment_char).

Inductive gs_get_chars_t : type :=
  mk_gs_get_chars : Fun(unique pb_stdin:pb_stdin_t)(s:string).gs_get_chars_t.

% non-whitespace, non-comment characters which can terminate an identifier.
Define gs_stop_chars := 
  let a = (mk_charvec bool ff) in
  (cvupdate bool Clp tt
  (cvupdate bool Crp tt
  (cvupdate bool pi_char tt
  (cvupdate bool lam_char tt
   a)))).

%-
Define gs_stop_chars := 
  (stringc Clp
  (stringc Crp
  (stringc pi_char
  (stringc lam_char
    inc stringn)))).-%

Define is_stop_char := (cvget bool gs_stop_chars).

%-
Define is_stop_char :=
fun(c:char).(member char c gs_stop_chars eqchar). -%

%- get the next maximal non-whitespace, non-comment sequence of characters,
   possibly empty. -%
Define gs_get_chars_h :=
  fun gs_get_chars_h(our_next_char : Fun(unique pb_stdin:pb_stdin_t).
                                        <getc_t pb_stdin_t>)
                    (unique pb_stdin:pb_stdin_t)
                    (owned where:string):unique gs_get_chars_t.
    match (our_next_char pb_stdin) with
       getc_none ign pb_stdin => 
        (mk_gs_get_chars pb_stdin inc stringn)
     | getc_char ign c pb_stdin =>
         match (eqchar c gs_comment_char) with
           ff =>
           match (is_whitespace c) with
             ff => match (is_stop_char c) with
                     ff =>
                     match (gs_get_chars_h pb_next_char
                               pb_stdin where) with
                       mk_gs_get_chars pb_stdin s => 
                          (mk_gs_get_chars pb_stdin (stringc c s))
                     end
                   | tt => % do not forget to push back the stop character
                     (mk_gs_get_chars (pb_push pb_stdin c) inc stringn)
                   end
           | tt => (mk_gs_get_chars pb_stdin inc stringn)
           end
        | tt => % c matches our comment character
                (mk_gs_get_chars (consume_to_eol pb_stdin_t pb_stdin_reader
                                    pb_stdin)
                   inc stringn)
        end
     end.

%- get the next maximal non-whitespace, non-comment non-empty 
   sequence of characters.  Report an error if this is empty
   and disallow_empty is true. If in_symbol is true, we will
   not skip initial whitespace and comments; otherwise, we
   will. -%
Define gs_get_chars := 
  fun gs_get_chars(unique pb_stdin:pb_stdin_t)
                  (owned where:string)
                  (in_symbol:bool)
                  (disallow_empty : bool):unique gs_get_chars_t.
    match (gs_get_chars_h 
             match in_symbol with ff => gs_char 
                                | tt => pb_next_char
                             end
             pb_stdin where) with
      mk_gs_get_chars pb_stdin' s => 
        match (and disallow_empty (isnil char s)) with
          ff => (mk_gs_get_chars pb_stdin' s)
        | tt => dec pb_stdin' dec s
                (handle_error_unique gs_get_chars_t 
                   (string_app "Expected a non-empty sequence of "
                   (string_app "non-whitespace, non-comment characters while"
                   (string_appnl "parsing " inc where))))
        end
    end.

Define eat_char :=
  fun(unique pb_stdin:pb_stdin_t)(owned where:string)(expected:char):unique pb_stdin_t.
    abbrev m = (string_app " while expecting character '"
               (string_app (stringc expected inc stringn)
               (string_app "' during parsing of " inc where))) in
    match (gs_char pb_stdin) with
       getc_none ign pb_stdin => 
         dec pb_stdin
         (handle_error_unique pb_stdin_t
           (string_app "Unexpected end of input"  m))
     | getc_char ign c pb_stdin =>
       match (eqchar c expected) with
         ff => dec pb_stdin
                (handle_error_unique pb_stdin_t 
                    (string_app "Encountered character '" 
	            (string_app (stringc c (stringc Csq inc stringn))
	                        m)))
       | tt => pb_stdin
       end
     end.

