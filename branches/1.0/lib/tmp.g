Inductive read_string_t : type :=
  mk_read_string_t : Fun(s:string)(unique l:stdin_t).read_string_t.

%- eat whitespace, then read non-whitespace, and consume the first
   character of subsequent whitespace. -%
Define read_string_h :=
  fun read_string_h(reading:bool)(unique stdin:stdin_t):unique read_string_t.
    match (next_char stdin) with
      getc_none stdin' => (mk_read_string_t inc stringn stdin')
    | getc_char a stdin' => 
      match (is_whitespace a) with
        ff => match (read_string_h tt stdin') with
                mk_read_string_t s stdin'' => 
                 (mk_read_string_t (stringc a s) stdin'')
                end
      | tt => match reading with 
                ff => (read_string_h reading stdin')
              | tt => (mk_read_string_t inc stringn stdin')
              end
      end
    end.

Define read_string := (read_string_h ff).

% return the next non-whitespace char if any
Define next_nonws :=
  fun next_nonws_char(unique stdin:stdin_t):unique getc_t .
    let nc = (next_char stdin) in
    match nc with
      getc_none stdin' => (getc_none stdin')
    | getc_char a stdin' => 
      match (is_whitespace a) with
        ff => (getc_char a stdin')
      | tt => (next_nonws_char stdin')
      end
    end.

% read to the next newline character
Define consume_to_eol :=
  fun consume_to_eol(unique stdin:stdin_t):unique stdin_t.
    match (next_char stdin) with
      getc_none stdin' => stdin'
    | getc_char a stdin' => 
      match (eqchar a Cnl) with
        ff => (consume_to_eol stdin')
      | tt => stdin'
      end
    end.

% consume whitespace and single-line comments initiated with the
% given comment char.
Define next_nonws_noncomment :=
  fun next_nonws_noncomment(comment:char)(unique stdin:stdin_t):unique getc_t.
    let nw = (next_nonws stdin) in
    match nw with
      getc_none stdin' => (getc_none stdin')
    | getc_char a stdin' => 
      match (eqchar a comment) with
        ff => (getc_char a stdin')
      | tt => (next_nonws_noncomment comment (consume_to_eol stdin'))
      end
    end.
