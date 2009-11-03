Include "../lib/trie.g".
Include "../lib/pb_stdio.g".

Define hist := Unit.

Define do_hist :=
  fun hist(#unique pb_stdio:pb_stdio_t)(h:hist):hist.
    match (pb_cur_char pb_stdio) with %read_string
      mk_read_string_t s pb_stdio' =>
      let #owned os = s in
      match os with
          nil A => do (dec pb_stdio_t pb_stdio')
					  (dec string s)
					  h
				   end
        | cons A' a' s' => do (dec string s)
							  (hist pb_stdio' h)
						   end
        end
    end.

Define spin := fun spin(u:Unit):Unit. (spin unit).

Define main :=
  fun(#unique pb_stdio:pb_stdio_t).
    let r = (do_hist pb_stdio unit) in 
    Z.
 
Set "debug_split_by_arity".
%Set "comment_vars".

Set "Debug_compiler".
%Set "debug_compiler_emit".
Set "debug_check_refs".
Set "print_ownership_annos".

Compile main to "wordhist2.c".
