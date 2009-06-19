Include trusted "../lib/stdio.g".

Define test := 
  let s = "hello world!" in
  let stdio' = (println_string stdio (inc string s)) in
    (println_string stdio' s).

%Set "debug_to_carraway".
%Set "debug_stages".
%Set "debug_simulate".
%Set "debug_eta_expand".

Compile test to "hello-world.c".