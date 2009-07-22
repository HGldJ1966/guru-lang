Include "../lib/queue.g".
Include "../lib/stdio.g".
Include "../lib/string.g".

Define test := 
  let ign = (init_rheaplets unit) in
  match (queue_new string rheaplet_id0) with
  return_queue_new _ q nextI =>
    let q = (enqueue string q "hi") in
    do (consume_unique rheaplet_id nextI)
       (consume_unique stdio_t 
          match (queue_is_empty string (inspect_unique <queue string> q)) by u ign with
            ff => (print_string stdio (queue_front string (inspect_unique <queue string> q) u))
          | tt => (print_string stdio "empty")
          end)
       (consume_unique <queue string> q)
    end
  end.

%Set "debug_to_carraway".
Set "debug_stages".
%Set "debug_init_terms".
%Set "debug_eta_expand".
%Set "debug_simulate".

Compile test to "test-queue.c".
