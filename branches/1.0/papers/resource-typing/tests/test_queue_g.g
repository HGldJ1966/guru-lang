Include "../../../lib/queue2.g".
Include "../../../lib/stdio.g".
Include "../../../lib/string.g".

Inductive enqueue_all_t : type :=
  return_enqueue_all : Fun(#unique_point stdio:stdio_t)(#unique q:<queue string>).#unique enqueue_all_t.

Define enqueue_all : Fun(#unique_point stdio:stdio_t)(#unique q:<queue string>).#unique enqueue_all_t :=
  fun enqueue_all(#unique_point stdio:stdio_t)(#unique q:<queue string>):#unique enqueue_all_t.
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

Define shift_all : Fun(#unique q1 q2:<queue string>). #unique <queue string> :=
   fun r(#unique q1 q2:<queue string>) : #unique <queue string> .
     let iq1 = (inspect_unique <queue string> q1) in
     match (queue_is_empty string (clone_unique_owned <queue string> iq1)) by u _ with
       ff => let x = (queue_front string iq1 hypjoin (queue_is_empty iq1) ff by u iq1_eq end) in
               (r (dequeue string q1 
                     hypjoin (queue_is_empty q1) ff by u iq1_eq end) (enqueue string q2 x))
     | tt => do (consume_unique_owned <queue string> iq1)
                (consume_unique <queue string> q1)
                q2
             end
     end. 

% this dequeues everything and prints the last entry (or prev if none)
Define dequeue_all : Fun(#unique q:<queue string>)(prev:string)(#unique_point stdio:stdio_t).#unique_point stdio_t :=
  fun r(#unique q:<queue string>)(prev:string)(#unique_point stdio:stdio_t) : #unique_point stdio_t.
    match (queue_is_empty string (inspect_unique <queue string> q)) by u ign with
      ff => do (dec string prev)
               let prev = (queue_front string (inspect_unique <queue string> q) u) in
                 (r (dequeue string q hypjoin (queue_is_empty string q) ff by u end) prev stdio)
            end
    | tt => do (consume_unique <queue string> q)
               (print_string stdio prev) 
            end
    end.

Define test1 := 
  let ign = (init_rheaplets unit) in
  match (queue_new string rheaplet_id0) with
  return_queue_new _ q nextI =>
    match (enqueue_all stdio q) with
    return_enqueue_all stdio q =>
      do (consume_unique rheaplet_id nextI)
         (consume_unique_point stdio_t (dequeue_all q "<empty>" stdio))
      end
    end
  end.

Define test2 := 
  let ign = (init_rheaplets unit) in
  match (queue_new string rheaplet_id0) with
  return_queue_new _ q1 nextI =>
    match (queue_new string nextI) with
    return_queue_new _ q2 nextI =>
      match (enqueue_all stdio q1) with
      return_enqueue_all stdio q1 =>
        do (consume_unique rheaplet_id nextI)
           (consume_unique_point stdio_t (dequeue_all (shift_all q1 q2) "<empty>" stdio))
        end
      end
    end
  end.

%Set "debug_to_carraway".
Set "debug_stages".
%Set "debug_init_terms".
%Set "debug_eta_expand".
%Set "debug_simulate".

Compile test2 to "test_queue_g.c".
