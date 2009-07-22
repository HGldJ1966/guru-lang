% efficient imperative queues.

Include "rheaplet.g".
Include "option.g".
Include "unique_owned.g".

Inductive queue_cell : Fun(A:type)(I:rheaplet_id).type :=
  mk_queue_cell : Fun(A:type)(spec I:rheaplet_id)(a:A)
                     (nextp : <option <alias I>>).
                   <queue_cell A I>.

Define type_family_abbrev rheaplet_queue := fun(A:type)(I:rheaplet_id).<rheaplet <queue_cell A I> I>.

Inductive queue : Fun(A:type).type :=
  queue_data : Fun(A:type)(spec I:rheaplet_id)(#unique h:<rheaplet_queue A I>)
                  (hd tl : <option <alias I>>).#unique <queue A>.

Inductive queue_new_t : Fun(A:type).type :=
  return_queue_new : Fun(spec A:type)(#unique q:<queue A>)
                       (#unique nextI:rheaplet_id).#unique <queue_new_t A>.

Define queue_new : Fun(A:type)(#unique I:rheaplet_id).#unique <queue_new_t A> :=
  fun(A:type)(#unique I:rheaplet_id):#unique <queue_new_t A>.
    match (new_rheaplet <queue_cell A I> I) with
      return_new_rheaplet _ _ nextI h =>
        (return_queue_new A (queue_data A I h (nothing <alias I>) (nothing <alias I>))
           nextI)
    end.

Define queue_is_empty : Fun(spec A:type)(^#unique_owned q:<queue A>).bool :=
  fun(spec A:type)(^#unique_owned q:<queue A>).
    match $ q with
      queue_data _ I h hd tl => 
      do (consume_unique_owned <rheaplet_queue A I> h)
         (consume_owned <option <alias I>> tl)
         match $ hd with
           nothing _ => tt
         | something _ l => do (consume_owned <alias I> l) ff end
         end
      end
    end.

Define queue_front : Fun(spec A:type)(^#unique_owned q:<queue A>)(u:{ (queue_is_empty q) = ff }).A :=
  fun(spec A:type)(^#unique_owned q:<queue A>)(u:{ (queue_is_empty q) = ff }).
    match $ q with
      queue_data _ I h hd tl => 
      do (consume_owned <option <alias I>> tl)
          match $ hd with
            nothing _ => impossible 
                            trans symm u
                            trans hypjoin (queue_is_empty q) tt by hd_eq q_eq end
                                  clash tt ff
                          A
          | something _ p => 
              match $ @ (rheaplet_get <queue_cell A I> I h p) with
                mk_queue_cell _ _ a nextp => 
                  do (consume_owned <option <alias I>> nextp)
                     let ret = (owned_to_unowned A a) in
                     do
                       (consume_unique_owned <rheaplet_queue A I> h)
                       ret
                     end
                  end
              end
          end
      end
    end.
 
Define enqueue : Fun(A:type)(#unique q:<queue A>)(a:A).#unique <queue A> :=
  fun(A:type)(#unique q:<queue A>)(a:A) : #unique <queue A>.
  match q with
    queue_data _ I h hd tl => 
    do (dec <option <alias I>> tl)
       match hd with
         nothing _ => 
         match (rheaplet_in <queue_cell A I> I h 
                  (mk_queue_cell A I a (nothing <alias I>))) with
           return_rheaplet_in _ _ h phd =>
           (queue_data A I h (something <alias I> (inc <alias I> phd)) (something <alias I> phd))
         end
       | something _ phd => 
       

abort <queue A>
         
       end
    end
  end.

