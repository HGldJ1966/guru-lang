Include trusted "../lib/trie.g".
Include "../lib/stdio.g".
Include "../lib/reader.g".

Define hist := <trie nat>.
Define histget := (trie_lookup nat).
Define histupdate := (trie_insert nat).

Define do_hist :=
  fun hist(#unique stdin:stdin_t)(#unique h:hist):#unique hist.
    match (read_until_char stdio ' ' join (eqchar ' ' Cc0) ff tt %- eat the newline -%) with
      mk_read_string_t ign s stdin' =>
      match inc s with
          nil A => dec stdin' dec s h
        | cons A' a' s' => 
            dec s'
            let r = (histget h s) in
            let n = match r with
                      nothing A => Z
                    | something A n => cast n by symm inj <option *> r_Eq
                    end in
            (hist stdin' (histupdate s (S n) h))
        end
    end.

Define spin := fun spin(u:Unit):Unit. (spin unit).

Define main :=
  fun(unique stdin:stdin_t).
    let ign = mk_ucvmod_t2 in % so we will compile this
    let r = (do_hist stdin (trie_none nat)) in 
    let s = (stringc Cc (stringc Co (stringc Cw inc stringn))) in
    let o = (histget r s) in
    dec s
    let ign = 
      match o with
        nothing A' => (print_nat zero)
      | something A' a' => 
        let r = (print_nat cast a' by symm inj <option *> o_Eq) in
          dec a' r
      end in
%    let ign = (spin unit) in
    dec r Z.
 
%Set "debug_split_by_arity".
%Set "comment_vars".

%Set "Debug_compiler".
%Set "debug_compiler_emit".
%Set "debug_eta_expand".
%Set "debug_check_refs".
%Set "print_ownership_annos".
%Set "printing_expand_consts".
%Set "print_pattern_var_types".
%Set "comment_vars".

Compile main to "wordhist.c".
