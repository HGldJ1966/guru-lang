Include "stdio.g".

Inductive reader_t : Fun(A:type).type :=
  mk_reader : Fun(A:type)(read_char:Fun(unique file:A).unique <getc_t A>).
                 <reader_t A>.

Define do_read := 
  fun(A:type)(owned r:<reader_t A>)(unique file:A):unique <getc_t A>.
    match r with
      mk_reader ign read_char =>
        cast (read_char file) by cong <getc_t *> symm inj <reader_t *> r_Eq
    end.

Inductive read_string_t : Fun(A:type).type :=
  mk_read_string_t : Fun(A:type)(s:string)(unique file:A).<read_string_t A>.

%- eat whitespace, then read non-whitespace, and consume the first
   character of subsequent whitespace. -%
Define read_string_h :=
  fun read_string_h(reading:bool)(A:type)(owned r:<reader_t A>)
                   (unique file:A):unique <read_string_t A>.
    match (do_read A r file) with
      getc_none ign file => 
        (mk_read_string_t A inc stringn file)
    | getc_char ign a file => 
      match (is_whitespace a) with
        ff => match (read_string_h tt A r file) with
                mk_read_string_t ign s file => 
                 (mk_read_string_t A (stringc a s) file)
                end
      | tt => match reading with 
                ff => (read_string_h reading A r file)
              | tt => (mk_read_string_t A inc stringn file)
              end
      end
    end.

Define read_string := (read_string_h ff).

% return the next non-whitespace char if any
Define next_nonws :=
  fun next_nonws_char(A:type)(owned r:<reader_t A>)
                     (unique file:A):unique <getc_t A>.
    match (do_read A r file) with
      getc_none ign file => (getc_none A file)
    | getc_char ign a file => 
      match (is_whitespace a) with
        ff => (getc_char A a file)
      | tt => (next_nonws_char A r file)
      end
    end.
% read to the next newline character
Define consume_to_eol :=
  fun consume_to_eol(A:type)(owned r:<reader_t A>)
                    (unique file:A):unique A.
    match (do_read A r file) by ign E with
      getc_none ign file => 
        cast file by symm inj <getc_t *> E
    | getc_char ign a file => 
      match (eqchar a Cnl) with
        ff => (consume_to_eol A r file)
      | tt => file
      end
    end.

% consume whitespace and single-line comments initiated with the
% given comment char.
Define next_nonws_noncomment :=
  fun next_nonws_noncomment(A:type)(owned r:<reader_t A>)
                           (comment:char)(unique file:A):unique <getc_t A>.
    let nw = (next_nonws A r file) in
    match nw with
      getc_none ign file => (getc_none A file)
    | getc_char ign a file => 
      match (eqchar a comment) with
        ff => (getc_char A a file)
      | tt => (next_nonws_noncomment A r comment 
                 (consume_to_eol A r file))
      end
    end.

Define stdio_reader := (mk_reader stdin_t next_char).