Include trusted "../lib/trie.g".
Include "../lib/pb_stdio.g".

Define hist := <trie nat>.
Define histget := (trie_lookup nat).
Define histupdate := (trie_insert nat).

Inductive do_hist_t : type := 
	return_do_hist : Fun(#unique pb_stdio : <pb_stdio_t ff>)(#unique h:hist).#unique do_hist_t.

Define do_hist :=
  fun do_hist(#unique pb_stdio:<pb_stdio_t tt>)(#unique h:hist):#unique hist.
    match (pb_read_until_char pb_stdio ' ' join (eqchar ' ' Cc0) ff tt %- eat the newline -%) with
      return_pb_read_until_char s ign pb_stdio' =>
      match (inc string s) with
          unil _ => do (consume_unique <pb_stdio_t tt> pb_stdio')
					   (dec string s)
					   h
					end
        | ucons _ a' s' => 
            do (dec string s')
				let r = (histget (inspect_unique hist h) (inspect string s)) in
				let n = match r with
						  nothing _ => Z
						| something _ n => cast n by symm inj <option *> r_Eq
						end in
				(do_hist pb_stdio' (histupdate s (S n) h))
			end
        end
    end.

Define spin := fun spin(u:Unit):Unit. (spin unit).

Define main :=
  fun(#unique pb_stdio:<pb_stdio_t tt>).
    %let ign = mk_ucvmod_t2 in % so we will compile this
    let r = (do_hist pb_stdio (trie_none nat)) in 
    let s = "cow" in
    let o = (histget (inspect_unique hist r) (inspect string s)) in
    do (dec string s)
	    let ign = 
	      match o with
			nothing _ => (pb_print_nat pb_stdio zero)
	      | something _ a' => 
			let r = (pb_print_nat pb_stdio cast a' by symm inj <option *> o_Eq) in
		  do (dec nat a')
				  r
			  end
	      end in
	%    let ign = (spin unit) in
		do (consume_unique hist r)
			Z
		end
    end.
 
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
