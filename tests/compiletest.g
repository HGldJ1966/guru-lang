Include trusted "../lib/list.g".

%Set "debug_classify_term_apps".

Define natlist := <list nat>.

Define test := (dec natlist (cons nat (S (S Z)) (nil nat))).

%Set "debug_to_carraway".
%Set "debug_eta_expand".
%Set "debug_stages".
%Set "debug_symbols".
Set "use_malloc".
Compile test to "compiletest.c".