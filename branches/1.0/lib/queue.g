% efficient imperative queues.

Include "rheaplet.g".
Include "qoption.g".
Include "unique_owned.g".

Inductive queue : Fun(A:type).type :=
  queue_data : Fun(A:type)(spec I:rheaplet_id)(#unique h:<rheaplet A I>)
                  (#unique hd tl : <qoption <alias I>>).#unique <queue A>.

Inductive queue_new_t : Fun(A:type).type :=
  return_queue_new : Fun(spec A:type)(#unique q:<queue A>)
                       (#unique nextI:rheaplet_id).#unique <queue_new_t A>.

Define queue_new : Fun(A:type)(#unique I:rheaplet_id).#unique <queue_new_t A> :=
  fun(A:type)(#unique I:rheaplet_id):#unique <queue_new_t A>.
    match (new_rheaplet A I) with
      return_new_rheaplet _ _ nextI h =>
        (return_queue_new A (queue_data A I h (qnothing <alias I>) (qnothing <alias I>))
           nextI)
    end.

Define queue_is_empty : Fun(spec A:type)(^#unique_owned q:<queue A>).bool :=
  fun(spec A:type)(^#unique_owned q:<queue A>).
    match q with
      queue_data _ I h hd tl => 
      do (consume_unique_owned <rheaplet A I> h)
         (consume_unique_owned <qoption <alias I>> tl)
         match hd with
           qnothing _ => tt
         | qsomething _ l => do (consume_unique_owned <alias I> l) ff end
         end
      end
    end.

Define queue_front : Fun(spec A:type)(^#unique_owned q:<queue A>)(u:{ (queue_is_empty q) = ff }).A :=
  fun(spec A:type)(^#unique_owned q:<queue A>)(u:{ (queue_is_empty q) = ff }).
    match q with
      queue_data _ I h hd tl => 
      do (consume_owned <qoption <alias I>> tl)
          match hd with
            qnothing _ => impossible 
                           trans symm u
                           trans hypjoin (queue_is_empty q) tt by hd_eq q_eq end
                                 clash tt ff
                         A
          | qsomething _ p => 
              (inc_owned A (rheaplet_get A I h p))
          end
      end
    end.
 
