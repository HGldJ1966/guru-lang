Include "../lib/queue.g".
Include "../lib/stdio.g".
Include "../lib/string.g".

Inductive enqueue_all_t : type :=
  return_enqueue_all : Fun(#unique stdio:stdio_t)(#unique q:<queue string>).#unique enqueue_all_t.

Define enqueue_all : Fun(#unique stdio:stdio_t)(#unique q:<queue string>).#unique enqueue_all_t :=
  fun enqueue_all(#unique stdio:stdio_t)(#unique q:<queue string>):#unique enqueue_all_t.
     match (read_until_char stdio Csp join (eqchar Csp Cc0) ff tt %- eat the newline -%) with
       return_read_until_char s eof stdio =>
       let q = match (inc string s) with
                 unil _ => do (dec string s) q end
               | ucons _ a l' => do (dec string l') (enqueue string q s) end 
               end in
         match eof with
           ff => (enqueue_all stdio q)
         | tt => (return_enqueue_all stdio q)
         end
     end.

% this dequeues everything and prints the last entry (or prev if none)
Define dequeue_all : Fun(#unique q:<queue string>)(prev:string)(#unique stdio:stdio_t).#unique stdio_t :=
  fun r(#unique q:<queue string>)(prev:string)(#unique stdio:stdio_t) : #unique stdio_t.
    match (queue_is_empty string (inspect_unique <queue string> q)) by u ign with
      ff => do (dec string prev)
               let prev = (queue_front string (inspect_unique <queue string> q) u) in
                 (r (dequeue string q hypjoin (queue_is_empty string q) ff by u end) prev stdio)
            end
    | tt => do (consume_unique <queue string> q)
               (print_string stdio prev) 
            end
    end.

Define test := 
  let ign = (init_rheaplets unit) in
  match (queue_new string rheaplet_id0) with
  return_queue_new _ q nextI =>
    match (enqueue_all stdio q) with
    return_enqueue_all stdio q =>
      do (consume_unique rheaplet_id nextI)
         (consume_unique stdio_t (dequeue_all q "<empty>" stdio))
      end
    end
  end.

%Set "debug_to_carraway".
Set "debug_stages".
%Set "debug_init_terms".
%Set "debug_eta_expand".
%Set "debug_simulate".

Compile test to "test-queue.c".
