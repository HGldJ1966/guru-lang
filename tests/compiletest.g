Include trusted "../lib/list.g".

%Set "debug_classify_term_apps".

Define natlist := <list nat>.

Define l1 := (cons nat (S (S Z)) (nil nat)).

Define l2 := (cons nat (S Z) (nil nat)).

Define test := do 
                 (dec natlist (append nat (inspect natlist l1) l2))
                 (dec natlist l1)
               end.

%Set "debug_to_carraway".
%Set "debug_eta_expand".
%Set "debug_stages".
%Set "debug_symbols".
Set "use_malloc".
Compile test to "compiletest.c".