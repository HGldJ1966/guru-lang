Include "../lib/list.g".
Include "../lib/stdio.g".

Set "Debug_compiler".

Define polyfun := Fun(A:type)(x:A).A.

Define plist := <list polyfun>.

Define id := fun(A:type)(x:A).x.

Define tmp := (cons polyfun id (nil polyfun)).

Define main :=
  fun(unique stdin:stdin_t).
    dec stdin ((hd polyfun tmp) polyfun id nat (S Z)).

Compile main to "polyfun.c".