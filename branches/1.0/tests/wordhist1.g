Include "../lib/trie.g".
Include "../lib/stdio.g".

Define hist := <trie nat>.
Define histget := (trie_lookup nat).
Define histupdate := (trie_insert nat).

%Define four := (S (S (S (S Z)))).

Define alength :=
  fun alength(A:type)(owned l:<list A>):nat .
    match l with
      nil A' => Z
    | cons A' a' l' => (S (alength A cast l' by symm l_Eq))
    end.

Define do_hist :=
  fun hist(unique stdin:stdin_t)(unique h:hist):unique hist.
    match (read_string stdin) with
      mk_read_string_t s stdin' =>
      let owned os = s in
      match os with
          nil A => dec stdin' dec s h
        | cons A' a' s' => 
          let l = (alength char s) in
          match (lt l nine) with
            ff => dec l dec s (hist stdin' h)
          | tt => dec l
            let r = (histget h s) in
            let n = match r with
                      nothing A => Z
                    | something A n => cast n by symm inj <option *> r_Eq
                    end in
            (hist stdin' (histupdate h s (S n)))
          end
        end
    end.

Define spin := fun spin(u:Unit):Unit. (spin unit).

Define main :=
  fun(unique stdin:stdin_t).
    let r = (do_hist stdin (trie_none nat)) in 
    let s = (stringc Cc (stringc Co (stringc Cw inc stringn))) in
    let o = (histget r s) in
    dec s
    let ign = 
      match o with
        nothing A' => (print_nat Z)
      | something A' a' => (print_nat cast a' by symm inj <option *> o_Eq)
      end in
%    let ign = (spin unit) in
    dec r Z.
 
Set "debug_split_by_arity".
%Set "comment_vars".

Set "Debug_compiler".
%Set "debug_compiler_emit".
Set "debug_check_refs".
Set "print_ownership_annos".

Compile main to "wordhist1.c".
