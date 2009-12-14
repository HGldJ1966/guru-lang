Include "unique_owned.g".
Include "stdio.g".

% Set "print_parsed".
% define a type for "pushback stdio"
Inductive pb_stdio_t : Fun(stdio_present : bool). type :=
	mk_pb_stdio : Fun(s:string)(#unique_point stdio:stdio_t) . #unique <pb_stdio_t tt>
|	mk_pb_stdio2 : Fun(s:string). #unique <pb_stdio_t ff>.

Define pb_stdio := (mk_pb_stdio (inc string stringn) stdio).

Inductive pb_checkout_t : type :=
	return_pb_checkout : Fun(#unique pb_stdio : <pb_stdio_t ff>)(#unique_point stdio:stdio_t).#unique pb_checkout_t.

Inductive pb_readstring_t : type :=
	mk_pb_readstring : Fun(#unique pb_stdio : <pb_stdio_t tt>)(s:string) . #unique pb_readstring_t.

Define pb_checkout : Fun(#unique pb_stdio : <pb_stdio_t tt>).#unique pb_checkout_t :=
  fun(#unique pb_stdio : <pb_stdio_t tt>):#unique pb_checkout_t.
    match pb_stdio with
      mk_pb_stdio l s => (return_pb_checkout (mk_pb_stdio2 l) s)
    | mk_pb_stdio2 l => abort pb_checkout_t
    end.

Define pb_checkin : Fun(#unique pb_stdio : <pb_stdio_t ff>)(#unique_point stdio:stdio_t).#unique <pb_stdio_t tt> :=
  fun(#unique pb_stdio : <pb_stdio_t ff>)(#unique_point stdio:stdio_t):#unique <pb_stdio_t tt> .
    match pb_stdio with
      mk_pb_stdio l s => abort <pb_stdio_t tt>
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
             | mk_pb_stdio2 l => ' '
	end in
	do (consume_unique_owned <pb_stdio_t tt> pb_stdio)
		ret
	end.

Define pb_cur_char : Fun(! #unique pb_stdio : <pb_stdio_t tt>) . #untracked char :=
  fun(! #unique pb_stdio : <pb_stdio_t tt>): #untracked char.
    (pb_cur_char2 (inspect_unique <pb_stdio_t tt> pb_stdio)).

Define pb_print_char := 
	fun(#unique pb_stdio:<pb_stdio_t tt>)(#untracked c:char): #unique <pb_stdio_t tt>.
	match (pb_checkout pb_stdio) with
		return_pb_checkout pb_stdio stdio =>
			(pb_checkin pb_stdio (print_char stdio c))
        end.

Define pb_skip :=
	fun(#unique pb_stdio : <pb_stdio_t tt>) : #unique <pb_stdio_t tt>.
	match pb_stdio with
		mk_pb_stdio l s =>
		match l with
			unil _ => (mk_pb_stdio (inc string stringn) (next_char s))
		|	ucons _ a l' => (mk_pb_stdio l' s)
		end
             | mk_pb_stdio2 l => abort <pb_stdio_t tt>
	end.

Define pb_skip2 :=
	fun pb_skip2(#unique pb_stdio : <pb_stdio_t tt>)(n : nat) : #unique <pb_stdio_t tt>.
	match n with
		Z => pb_stdio
	|	S n' => (pb_skip2 (pb_skip pb_stdio) n')
	end.

Define pb_reset :=
	fun(#unique pb_stdio : <pb_stdio_t tt>) : #unique <pb_stdio_t tt>.
	match pb_stdio with
		mk_pb_stdio l s =>	do (dec string l)
			(mk_pb_stdio (inc string stringn) s)
			end
             | mk_pb_stdio2 l => abort <pb_stdio_t tt>
	end.

Define pb_next_char := pb_skip.

Define pb_pushback :=
	fun(#unique pb_stdio : <pb_stdio_t tt>)(c : char) : #unique <pb_stdio_t tt>.
	match pb_stdio with
		mk_pb_stdio l s => (mk_pb_stdio (ucons char c l) s)
             | mk_pb_stdio2 l => abort <pb_stdio_t tt>
	end.

Define pb_pushback2 :=
	fun(#unique pb_stdio : <pb_stdio_t tt>)(str : string) : #unique <pb_stdio_t tt>.
	match pb_stdio with
		mk_pb_stdio l s => (mk_pb_stdio (string_app1 str l) s)
             | mk_pb_stdio2 l => abort <pb_stdio_t tt>
	end.

Define pb_print_string :=
	fun(#unique pb_stdio : <pb_stdio_t tt>)(str : string) : #unique <pb_stdio_t tt>.
	match (pb_checkout pb_stdio) with
		return_pb_checkout pb_stdio stdio =>
			(pb_checkin pb_stdio (print_string stdio str))
	end.

Define pb_println_string :=
	fun(#unique pb_stdio : <pb_stdio_t tt>)(str : string) : #unique <pb_stdio_t tt>.
	match (pb_checkout pb_stdio) with
		return_pb_checkout pb_stdio stdio =>
			(pb_checkin pb_stdio (println_string stdio str))
	end.

Define pb_readstring :=
	fun pb_readstring(#unique pb_stdio : <pb_stdio_t tt>) : #unique pb_readstring_t.
	let c = (pb_cur_char pb_stdio) in
	let pb_stdio = (pb_next_char pb_stdio) in
	match (eqchar c Cnl) with
		ff => match (pb_readstring pb_stdio) with
				mk_pb_readstring pb_stdio s => (mk_pb_readstring pb_stdio (ucons char c s))
			  end
	|	tt => (mk_pb_readstring pb_stdio (inc string stringn))
	end.

Define pb_readstring2 :=
	fun pb_readstring2(#unique pb_stdio : <pb_stdio_t tt>)(n : nat) : #unique pb_readstring_t.
	let c = (pb_cur_char pb_stdio) in
	let pb_stdio = (pb_next_char pb_stdio) in
	match n with
		Z => (mk_pb_readstring pb_stdio (inc string stringn))
	|	S n' => match (pb_readstring2 pb_stdio n') with
					mk_pb_readstring pb_stdio s => (mk_pb_readstring pb_stdio (ucons char c s))
			    end
	end.

Inductive pb_read_until_char_t : type :=
	return_pb_read_until_char : Fun(s:string)(eof:bool)(#unique pb_stdio:<pb_stdio_t tt>).#unique pb_read_until_char_t.

Define pb_read_until_char : Fun(#unique pb_stdio:<pb_stdio_t tt>)(c:char)(u:{ (eqchar c Cc0) = ff })
                            (eat_char:bool).#unique pb_read_until_char_t :=
	fun (#unique pb_stdio:<pb_stdio_t tt>)(c:char)(u:{ (eqchar c Cc0) = ff})(eat_char:bool):#unique pb_read_until_char_t.
	match (pb_checkout pb_stdio) with
		return_pb_checkout pb_stdio stdio =>
			match (read_until_char stdio c u eat_char) with
				return_read_until_char s eof stdio =>
					(return_pb_read_until_char s eof (pb_checkin pb_stdio stdio))
			end
	end.

Define pb_print_nat :=
	fun pb_print_nat (#unique pb_stdio:<pb_stdio_t tt>)(n:nat):#unique <pb_stdio_t tt>.
	match n with 
		Z => (pb_print_char pb_stdio CZ)
	|	S n' => let pb_stdio = (pb_print_char pb_stdio CS) in 
					(pb_print_nat pb_stdio n')
	end.

% read the next character which is non-whitespace, non-comment
Define pb_next_nonws_noncomment :=
	fun r(#unique pb_stdio:<pb_stdio_t tt>)(c_char:char) : #unique pb_readstring_t.
	let c = (pb_cur_char pb_stdio) in
	match (eqchar c ' ') with
		ff => match (eqchar c c_char) with
				ff => match (pb_read_until_char pb_stdio C10 join (eqchar C10 Cc0) ff tt) with
						return_pb_read_until_char s ign pb_stdio => (r pb_stdio c_char)
					  end
			  |	tt => (mk_pb_readstring pb_stdio (ucons char c (unil char)))
			  end
	|	tt => let pb_stdio = (pb_skip pb_stdio) in
				  (r pb_stdio c_char)
	end.

% Opaque pb_stdio_t.
