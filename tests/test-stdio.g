Include "../lib/stdio.g".

Define test := 
  let stdio = (stdio unit) in
  let c = (cur_char stdio) in
    (print_char (print_char (print_char stdio c) c) Cba).

%Set "debug_to_carraway".
%Set "debug_stages".
%Set "debug_simulate".
%Set "debug_eta_expand".

Compile test to "test-stdio.c".