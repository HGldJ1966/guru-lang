Include "../lib/pb_stdio.g".

Define test := 
%-	let pb_stdio = (pb_skip pb_stdio) in
	let c = (pb_cur_char pb_stdio) in
	(pb_print_char pb_stdio c).
-%

%	(pb_printstring pb_stdio "xyz").

%	match (pb_readstring2 pb_stdio (inc nat five)) with
	match (pb_readstring pb_stdio) with
		mk_pb_readstring s pb_stdio => (pb_println_string pb_stdio s)
	end.

%-	let pb_stdio = (pb_skip2 pb_stdio (S Z)) in
	let pb_stdio = (pb_pushback pb_stdio (pb_cur_char pb_stdio)) in
	%let pb_stdio = (pb_reset pb_stdio) in
	let pb_stdio = (pb_pushback2 pb_stdio "xyz") in
	let pb_stdio = (pb_skip pb_stdio) in
		match pb_stdio with
			mk_pb_stdio l s => (print_string s l)
		|	mk_pb_stdio2 l => Z
		end.
-%

%-	let s1 = (ucons char CA (inc string stringn)) in
	let s2 = (ucons char CB (inc string stringn)) in
	let s = (string_app1 s1 s2) in
		(print_string stdio s).
-%
%Set "debug_to_carraway".
%Set "debug_stages".
%Set "debug_simulate".
%Set "debug_eta_expand".

Compile test to "test-pb_stdio.c".
