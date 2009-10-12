Include "unique_owned.g".
Include trusted "stdio.g".

% define a type for "pushback stdio"
Inductive pb_stdio_t : type :=
	mk_pb_stdio : Fun(s:string)(#unique_point stdio:stdio_t) . #unique pb_stdio_t.

Define pb_stdio := (mk_pb_stdio stringn stdio).

Define pb_cur_char2 : Fun(^ #unique_owned pb_stdio : pb_stdio_t) . #untracked char :=
 fun(^ #unique_owned pb_stdio : pb_stdio_t).
 let ret = match ! pb_stdio with
           mk_pb_stdio l s =>
             let ret = match ! l with
		        unil _ => (cur_char2 s)
		      | ucons _ a l' => do (consume_owned string l') 
                                           (consume_unique_owned_point stdio_t s)
                                           a
                                        end
                      end in
             do (consume_owned string l)
                ret
             end 
           end in
   do (consume_unique_owned pb_stdio_t pb_stdio)
      ret
   end.

Define pb_cur_char : Fun(! #unique pb_stdio : pb_stdio_t) . #untracked char :=
  fun(! #unique pb_stdio : pb_stdio_t): #untracked char.
    (pb_cur_char2 (inspect_unique pb_stdio_t pb_stdio)).

Define pb_print_char := 
  fun(#unique x:pb_stdio_t)(#untracked c:char): #unique pb_stdio_t.
    match x with
      mk_pb_stdio l s =>
        (mk_pb_stdio l (print_char s c))
   end.

Define pb_skip : Fun(! #unique pb_stdio : pb_stdio_t) . #unique pb_stdio_t :=
	fun(! #unique pb_stdio : pb_stdio_t).
	match pb_stdio with
		mk_pb_stdio l s =>
		match l with
			unil _ => pb_stdio
		|	ucons _ a l' => (mk_pb_stdio l' s)
		end
	end.

Define pb_skip2 : Fun(n : nat)(! #unique pb_stdio : pb_stdio_t) . #unique pb_stdio_t :=
	fun pb_skip2(n : nat)(! #unique pb_stdio : pb_stdio_t): #unique pb_stdio_t.
	match n with
		Z => pb_stdio
	|	S n' => (pb_skip2 n' (pb_skip pb_stdio))
	end.

Define pb_reset : Fun(! #unique pb_stdio : pb_stdio_t) . #unique pb_stdio_t :=
	fun(! #unique pb_stdio : pb_stdio_t).
	match pb_stdio with
		mk_pb_stdio l s =>	(mk_pb_stdio stringn s)
	end.

Define pb_next_char : Fun(! #unique pb_stdio : pb_stdio_t) . #untracked char :=
	fun(! #unique pb_stdio : pb_stdio_t).
	match pb_stdio with
		mk_pb_stdio l s =>
		match l with
			unil _ => (pb_cur_char (mk_pb_stdio l (next_char s)))
		|	ucons _ a l' => (pb_cur_char (mk_pb_stdio l' s))
		end
	end.

Define pb_pushback : Fun(c : char)(! #unique pb_stdio : pb_stdio_t) . #unique pb_stdio_t :=
	fun(c : char)(! #unique pb_stdio : pb_stdio_t).
	match pb_stdio with
		mk_pb_stdio l s => (mk_pb_stdio (ucons char c l) s)
	end.

Define pb_pushback2 : Fun(str : string)(! #unique pb_stdio : pb_stdio_t) . #unique pb_stdio_t :=
	fun(str : string)(! #unique pb_stdio : pb_stdio_t).
	match pb_stdio with
		mk_pb_stdio l s => (mk_pb_stdio (string_app str l) s)
	end.
