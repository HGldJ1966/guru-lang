Include "../lib/nat.g".
Include "../lib/pb_stdio.g".

Define test1 : Fun(a : nat)(#unique pb_stdio:<pb_stdio_t tt>) .#abort nat :=
fun(a :nat)(#unique pb_stdio:<pb_stdio_t tt>):#abort nat.
	abort nat.

Define test : Fun(a b:nat)(#unique pb_stdio:<pb_stdio_t tt>) . #unique <pb_stdio_t tt> :=
fun(a b:nat)(#unique pb_stdio:<pb_stdio_t tt>) : #unique <pb_stdio_t tt>.
let k=
match a with
	Z => (test1 b pb_stdio)
|	S a' => b
end
in
(pb_print_nat pb_stdio k).

Define main :=
(test Z Z).

Set "debug_to_carraway".
Set "debug_eta_expand".

Compile main to "test-abort.c".
