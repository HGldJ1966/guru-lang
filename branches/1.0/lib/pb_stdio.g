Include "unique_owned.g".
Include "stdio.g".

% Set "print_parsed".
% define a type for "pushback stdio"
Inductive pb_stdio_t : Fun(stdio_present : bool). type :=
	mk_pb_stdio : Fun(s:string)(#unique_point stdio:stdio_t) . #unique <pb_stdio_t tt>
      | mk_pb_stdio2 : Fun(s:string). #unique <pb_stdio_t ff>.

Define pb_stdio := (mk_pb_stdio (inc string stringn) stdio).

Inductive pb_checkout_t : type :=
  return_pb_checkout : Fun(#unique pb_stdio : <pb_stdio_t ff>)(#unique_point stdio:stdio_t).#unique pb_checkout_t.

Define pb_checkout : Fun(#unique pb_stdio : <pb_stdio_t tt>).#unique pb_checkout_t :=
  fun(#unique pb_stdio : <pb_stdio_t tt>):#unique pb_checkout_t.
    match pb_stdio with
      mk_pb_stdio l s => (return_pb_checkout (mk_pb_stdio2 l) s)
    | mk_pb_stdio2 l => Z
    end.

Define pb_checkin : Fun(#unique pb_stdio : <pb_stdio_t ff>)(#unique_point stdio:stdio_t).#unique <pb_stdio_t tt> :=
  fun(#unique pb_stdio : <pb_stdio_t ff>)(#unique_point stdio:stdio_t):#unique <pb_stdio_t tt> .
    match pb_stdio with
      mk_pb_stdio l s => Z
    | mk_pb_stdio2 l => (mk_pb_stdio l stdio)
    end.

Define pb_cur_char2 : Fun(^ #unique_owned pb_stdio : <pb_stdio_t tt>) . #untracked char :=
	fun(^ #unique_owned pb_stdio : <pb_stdio_t tt>).
	let ret = match ! pb_stdio with
		mk_pb_stdio l s =>
		let ret = match ! l with
					unil _ => (cur_char2 s)
				|	ucons _ a l' => do (consume_owned string l') 
							(consume_unique_owned_point stdio_t s)
							a
							end
				end in
		do (consume_owned string l)
			ret
		end 
             | mk_pb_stdio2 l => Z
	end in
	do (consume_unique_owned <pb_stdio_t tt> pb_stdio)
		ret
	end.

Define pb_cur_char : Fun(! #unique pb_stdio : <pb_stdio_t tt>) . #untracked char :=
  fun(! #unique pb_stdio : <pb_stdio_t tt>): #untracked char.
    (pb_cur_char2 (inspect_unique <pb_stdio_t tt> pb_stdio)).

%-
Define pb_print_char := 
	fun(#unique x:<pb_stdio_t tt>)(#untracked c:char): #unique <pb_stdio_t tt>.
	match x with
		mk_pb_stdio l s =>
			(mk_pb_stdio l (print_char s c))
             | mk_pb_stdio2 l => Z
	end.
-%

Define pb_skip :=
	fun(#unique pb_stdio : <pb_stdio_t tt>) : #unique <pb_stdio_t tt>.
	match pb_stdio with
		mk_pb_stdio l s =>
		match l with
			unil _ => (mk_pb_stdio (inc string stringn) (next_char s))
		|	ucons _ a l' => (mk_pb_stdio l' s)
		end
             | mk_pb_stdio2 l => Z
	end.

Define pb_skip2 :=
	fun pb_skip2(n : nat)(#unique pb_stdio : <pb_stdio_t tt>) : #unique <pb_stdio_t tt>.
	match n with
		Z => pb_stdio
	|	S n' => (pb_skip2 n' (pb_skip pb_stdio))
	end.

Define pb_reset :=
	fun(#unique pb_stdio : <pb_stdio_t tt>) : #unique <pb_stdio_t tt>.
	match pb_stdio with
		mk_pb_stdio l s =>	do (dec string l)
			(mk_pb_stdio (inc string stringn) s)
			end
             | mk_pb_stdio2 l => Z
	end.

Define pb_next_char := pb_skip.

Define pb_pushback :=
	fun(c : char)(#unique pb_stdio : <pb_stdio_t tt>) : #unique <pb_stdio_t tt>.
	match pb_stdio with
		mk_pb_stdio l s => (mk_pb_stdio (ucons char c l) s)
             | mk_pb_stdio2 l => Z
	end.

Define pb_pushback2 :=
	fun(str : string)(#unique pb_stdio : <pb_stdio_t tt>) : #unique <pb_stdio_t tt>.
	match pb_stdio with
		mk_pb_stdio l s => (mk_pb_stdio (string_app1 str l) s)
             | mk_pb_stdio2 l => Z
	end.

% Opaque pb_stdio_t.