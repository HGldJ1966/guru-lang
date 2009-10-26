Include "../lib/word.g".

Define test := 
    (word_inc2 (word_inc2 (word_inc2 0x01)))
.

%Set "debug_to_carraway".
%Set "debug_stages".
%Set "debug_simulate".
%Set "debug_eta_expand".

Compile test to "test-word.c".
