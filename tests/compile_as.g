Include trusted "../lib/nat.g".
Include trusted "../lib/list.g".

Define spec n1 := (concat nat (cons <list nat> (nil nat) (cons <list nat> (nil nat) (nil <list nat>)))).

Define n2 := (nil <list nat>).

Define test := (dec <list nat> compile n1 as n2 by join n1 n2 ).

Set "debug_to_carraway".
Set "debug_eta_expand".
Set "debug_stages".
%Set "debug_symbols".
Set "use_malloc".
Compile test to "compile_as.c".
