Include "../lib/word.g".

Define spec_fun := fun(spec x:nat)(y:nat).y.
Define fun1 := fun(n:nat).(spec_fun n n).

% Set "debug_classify_apps".

Define fun2 := fun(w:word).(spec_fun (word_to_nat w) Z).