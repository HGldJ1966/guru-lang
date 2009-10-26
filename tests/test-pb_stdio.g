Include "../lib/pb_stdio.g".

Define test := 
%	Bug case one: leaking
%	let c = (pb_next_char pb_stdio) in
%	(pb_print_char pb_stdio c).

%	Case Two: works fine
	let pb_stdio = (pb_skip pb_stdio) in
	let c = (pb_cur_char pb_stdio) in
        match (pb_checkout pb_stdio) with
          return_pb_checkout pb_stdio stdio =>
  	   let pb_stdio = (pb_checkin pb_stdio (print_char stdio c)) in
             pb_stdio % <pb_stdio_t tt>
        end.


%	let pb_stdio = (pb_skip2 (S Z) pb_stdio) in
%	let pb_stdio = (pb_pushback (pb_cur_char pb_stdio) pb_stdio) in
%	let pb_stdio = (pb_reset pb_stdio) in
%	let pb_stdio = (pb_pushback2 "xyz" pb_stdio) in
%	let pb_stdio = (pb_skip pb_stdio) in
%-		match pb_stdio with
			mk_pb_stdio l s => (print_string s l)
		end.
-%
%	let pb_stdio = (pb_skip pb_stdio) in
%	let c = (pb_next_char pb_stdio) in
%	(pb_print_char pb_stdio c).
%-	let c1 = (pb_cur_char pb_stdio) in
	let c2 = (pb_cur_char pb_stdio) in
	let c3 = (pb_cur_char (pb_pushback c1 (pb_pushback c2 pb_stdio))) in
	let c4 = (pb_next_char pb_stdio) in
		(pb_print_char (pb_print_char (pb_print_char (pb_print_char stdio c2) c3) c4) Cba). 
-%

%Set "debug_to_carraway".
%Set "debug_stages".
%Set "debug_simulate".
%Set "debug_eta_expand".

Compile test to "test-pb_stdio.c".
