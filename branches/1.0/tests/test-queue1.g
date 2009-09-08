Include "../lib/queue.g".
Include "../lib/stdio.g".
Include "../lib/string.g".

Define eat_all_words : Fun(#unique_point stdio:stdio_t).#unique_point stdio_t :=
  fun r(#unique_point stdio:stdio_t):#unique_point stdio_t.
     match (read_until_char stdio Csp join (eqchar Csp Cc0) ff tt %- eat the newline -%) with
       return_read_until_char s eof stdio =>
       do (dec string s)
          match eof with
           ff => (r stdio)
         | tt => stdio
         end
       end
     end.

Define test := (consume_unique_point stdio_t (eat_all_words stdio)).

%Set "debug_to_carraway".
%Set "debug_stages".
%Set "debug_init_terms".
%Set "debug_eta_expand".
%Set "debug_simulate".

Compile test to "test-queue1.c".
