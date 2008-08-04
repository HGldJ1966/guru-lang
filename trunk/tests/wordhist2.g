Include "../lib/trie.g".
Include "../lib/stdio.g".

Define hist := Unit.

Define do_hist :=
  fun hist(unique stdin:stdin_t)(h:hist):hist.
    match (read_string stdin) with
      mk_read_string_t s stdin' =>
      let owned os = s in
      match os with
          nil A => dec stdin' dec s h
        | cons A' a' s' => dec s (hist stdin' h)
        end
    end.

Define spin := fun spin(u:Unit):Unit. (spin unit).

Define main :=
  fun(unique stdin:stdin_t).
    let r = (do_hist stdin unit) in 
    Z.
 
Set "debug_split_by_arity".
%Set "comment_vars".

Set "Debug_compiler".
%Set "debug_compiler_emit".
Set "debug_check_refs".
Set "print_ownership_annos".

Compile main to "wordhist2.c".
