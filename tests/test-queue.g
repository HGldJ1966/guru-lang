Include "../lib/queue.g".
Include "../lib/stdio.g".
Include "../lib/string.g".

Define test := 
  match (queue_new string rheaplet_id0) with
  return_queue_new _ q nextI =>
  do (consume_unique rheaplet_id nextI)
     (consume_unique stdio_t 
        match (queue_is_empty string (inspect_unique <queue string> q)) with
          ff => (print_string stdio "non-empty")
        | tt => (print_string stdio "empty")
        end)
     (consume_unique <queue string> q)
  end
  end.

%Set "debug_to_carraway".
%Set "debug_eta_expand".

Compile test to "test-queue.c".
