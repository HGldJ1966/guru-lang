Include trusted "../lib/plus.g".

Define n1 := (plus Z (S Z)).

Define n2 := (S Z).

Define test := (dec nat compile n1 as n2 by join n1 n2 ).

Set "debug_to_carraway".
Set "debug_eta_expand".
Set "debug_stages".
%Set "debug_symbols".
Set "use_malloc".
Compile test to "compile_as.c".
