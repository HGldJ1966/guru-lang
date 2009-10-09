Include "../lib/pb_stdio.g".

Define test := 
	(print_char stdio (pb_cur_char pb_stdio)).
%-
	let c1 = (pb_cur_char pb_stdio) in
	let c2 = (pb_cur_char pb_stdio) in
	let c3 = (pb_cur_char (pb_pushback c1 (pb_pushback c2 pb_stdio))) in
	let c4 = (pb_next_char pb_stdio) in
		(print_char (print_char (print_char (print_char stdio c2) c3) c4) Cba).
-%

%Set "debug_to_carraway".
%Set "debug_stages".
%Set "debug_simulate".
%Set "debug_eta_expand".

Compile test to "test-pb_stdio.c".