Include "../lib/trie.g".
Include "../lib/pb_stdio.g".

Define hist := Unit.

Define do_hist :=
  fun do_hist(#unique pb_stdio:<pb_stdio_t tt>)(h:Unit):Unit.
    match (pb_readstring pb_stdio) with
      mk_pb_readstring s pb_stdio =>
      match s with
          unil _ => h
        | ucons _ a' s' => do (dec string s')
							  (do_hist pb_stdio h)
						   end
        end
    end.

Define spin := fun spin(u:Unit):Unit. (spin unit).

Define main :=
  fun(#unique pb_stdio:<pb_stdio_t tt>).
    let r = (do_hist pb_stdio unit) in 
    Z.
 
Set "debug_split_by_arity".
%Set "comment_vars".

Set "Debug_compiler".
%Set "debug_compiler_emit".
Set "debug_check_refs".
Set "print_ownership_annos".

Compile main to "wordhist2.c".
