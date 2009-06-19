Include trusted "../lib/stdio.g".

Define test := 
  let stdio = (stdio unit) in
  let s = "hello world!" in
    (println_string stdio s).

%Set "debug_to_carraway".
%Set "debug_stages".
%Set "debug_simulate".
%Set "debug_eta_expand".

Compile test to "hello-world.c".