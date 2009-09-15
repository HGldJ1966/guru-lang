% efficient imperative queues.

Include "rheaplet_thms.g".
Include "option.g".
Include "unique_owned.g".

% queue_cell
%
% queue_cellc -- for cells of the queue which point to another cell (via an alias)
% queue_celln -- for cells of the queue which don't.

Inductive queue_cell : Fun(A:type)(I:rheaplet_id).type :=
  queue_cellc : Fun(A:type)(spec I:rheaplet_id)(a:A)(nextp : <alias I>).
                   <queue_cell A I>
| queue_celln : Fun(A:type)(spec I:rheaplet_id)(a:A). <queue_cell A I>.

Define type_family_abbrev rheaplet_queue := fun(A:type)(I:rheaplet_id).<rheaplet <queue_cell A I> I>.

Define spec queue_cell_inv := fun(A:type)(I:rheaplet_id)(bound:nat)(c:<queue_cell A I>).
                                 match c with queue_cellc _ _ a nextp => (lt nextp bound)
                                            | queue_celln _ _ a => tt
                                 end.

Define predicate rheaplet_queue_inv := 
  fun(A:type)(I:rheaplet_id)(r:<rheaplet_queue A I>)(bound:nat).
   { (list_all (queue_cell_inv bound) r) = tt }.

Define weaken_rheaplet_queue_inv : 
  Forall(A:type)(I:rheaplet_id)(r:<rheaplet_queue A I>)
        (bound1 bound2:nat)
        (u1:@<rheaplet_queue_inv A I r bound1>)
        (u2:{(lt bound1 bound2) = tt}).
    @<rheaplet_queue_inv A I r bound2> :=
  foralli(A:type)(I:rheaplet_id)(r:<rheaplet_queue A I>)
         (bound1 bound2:nat)
         (u1:@<rheaplet_queue_inv A I r bound1>)
         (u2:{(lt bound1 bound2) = tt}).
    [list_all_implies <queue_cell A I> 
      (queue_cell_inv A I bound1) (queue_cell_inv A I bound2)
      foralli(c:<queue_cell A I>)(u:{(queue_cell_inv A I bound1 c) = tt}). 
        case c with
          queue_cellc _ _ a nextp => hypjoin (queue_cell_inv A I bound2 c) tt
                                     by c_eq u [lt_trans nextp bound1 bound2 
                                                  hypjoin (lt nextp bound1) tt by c_eq u end
                                                  u2] 
                                     end
        | queue_celln _ _ a => truei
        end].

Define queue_cell_has_next : Fun(A:type)(spec I:rheaplet_id)(c:<queue_cell A I>).bool :=
  fun(A:type)(spec I:rheaplet_id)(c:<queue_cell A I>):bool.
    match c with
      queue_cellc _ _ a p => 
        do (consume_owned A a)
           (dec <alias I> p)
           tt
        end
    | queue_celln _ _ a => 
        do (consume_owned A a)
           ff
        end
    end.

Inductive queue : Fun(A:type).type :=
  queue_datac : Fun(A:type)(spec I:rheaplet_id)(#unique h:<rheaplet_queue A I>)
                   (qin qout : <alias I>)
                   (inv : @<rheaplet_queue_inv A I h>)
                   (inv_qin : {(lt qin (length h)) = tt})
                   (inv_qout : {(lt qout (length h)) = tt})
                   (inv_qin2 : {(queue_cell_has_next (rheaplet_get qin h)) = ff}).
                   #unique <queue A>
| queue_datan : Fun(A:type)(spec I:rheaplet_id)(#unique h:<rheaplet_queue A I>)
                   (inv:@<rheaplet_queue_inv A I h>).#unique <queue A>.

Inductive queue_new_t : Fun(A:type).type :=
  return_queue_new : Fun(spec A:type)(#unique q:<queue A>)
                       (#unique nextI:rheaplet_id).#unique <queue_new_t A>.

Define queue_new : Fun(A:type)(#unique I:rheaplet_id).#unique <queue_new_t A> :=
  fun(A:type)(#unique I:rheaplet_id):#unique <queue_new_t A>.
    match (new_rheaplet <queue_cell A I> I) by u _ with
      return_new_rheaplet _ _ nextI h =>
        (return_queue_new A 
          (queue_datan A I h
             hypjoin (list_all (queue_cell_inv (length h)) h) tt
             by inj (return_new_rheaplet ** *) trans symm eval (new_rheaplet I) u end)
          nextI)
    end.

Define queue_is_empty : Fun(spec A:type)(^#unique_owned q:<queue A>).bool :=
  fun(spec A:type)(^#unique_owned q:<queue A>).
  let ret = 
    match ! q with
      queue_datac _ I h qin qout _ _ _ _ => 
        do (consume_unique_owned <rheaplet_queue A I> h)
           (consume_owned <alias I> qin) 
           (consume_owned <alias I> qout) 
           ff
        end
    | queue_datan _ I h _ => 
        do (consume_unique_owned <rheaplet_queue A I> h)
           tt
        end
    end in
  do (consume_unique_owned <queue A> q)
     ret
  end.    

Define queue_front : Fun(spec A:type)(^#unique_owned q:<queue A>)(u:{ (queue_is_empty q) = ff }).A :=
  fun(spec A:type)(^#unique_owned q:<queue A>)(u:{ (queue_is_empty q) = ff }).
    match ! q with
      queue_datac _ I h qin qout _ _ _ _ => 
        let cell = (rheaplet_get <queue_cell A I> I qout h) in
        let ret = 
           match ! cell by v1 _ with
             queue_cellc _ _ a nextp => do (consume_owned <alias I> nextp) (owned_to_unowned A a) end
           | queue_celln _ _ a => (owned_to_unowned A a)
           end in
        do (consume_owned <queue_cell A I> cell)
           (consume_owned <alias I> qin)
           (consume_unique_owned <rheaplet_queue A I> h)
           ret
        end
    | queue_datan _ I h _ => 
      impossible transs symm u
                        hypjoin (queue_is_empty q) tt by q_eq end
                        clash tt ff
                 end
        A
    end.
 
Define enqueue : Fun(spec A:type)(#unique q:<queue A>)(a:A).#unique <queue A> :=
  fun(spec A:type)(#unique q:<queue A>)(a:A) : #unique <queue A>.
  match q with
    queue_datac A1 I h qin qout _ _ _ inv_qin2 => 
      let ih = (inspect_unique <rheaplet_queue A I> h) in
      let cell = (rheaplet_get <queue_cell A I> I (inspect <alias I> qin) ih) in
      match ! cell by cell_eq2 _ with
        queue_cellc _ _ b nextp =>
          impossible transs hypjoin tt (queue_cell_has_next (rheaplet_get qin h))
                              by cell_eq cell_eq2 ih_eq end
                            inv_qin2 
                            clash ff tt
                     end
           <queue A>
      | queue_celln _ _ b => 
        let x = (owned_to_unowned A1 b) in
        do (consume_owned <queue_cell A I> cell)
           (consume_unique_owned <rheaplet_queue A I> ih) 
           match (rheaplet_in <queue_cell A I> I h (queue_celln A1 I a)) by i _ with
             return_rheaplet_in _ _ h' new_qin => 
               let h'' = (rheaplet_set <queue_cell A I> I (inspect <alias I> qin) h' 
                           (queue_cellc A1 I x (inc <alias I> new_qin))) in
               do (dec <alias I> qin)
                  cast (queue_datac A1 I h'' new_qin qout
                          show [rheaplet_in_length <queue_cell A I> I h h' 
                                 (queue_celln A1 I a) new_qin i]
                          end
                         ) by symm q_Eq
               end
           end
        end
      end
  | queue_datan A1 I h =>
    match (rheaplet_in <queue_cell A I> I h (queue_celln A1 I a)) with
      return_rheaplet_in _ _ h new_qout => 
        cast (queue_datac A1 I h (inc <alias I> new_qout) new_qout) by symm q_Eq
    end
  end.

Define dequeue : Fun(spec A:type)(#unique q:<queue A>)(u:{ (queue_is_empty q) = ff }).#unique <queue A> :=
  fun(spec A:type)(#unique q:<queue A>)(u:{ (queue_is_empty q) = ff }):#unique <queue A>.
    match q with
      queue_datac A1 I h qin qout => 
        let ih = (inspect_unique <rheaplet_queue A I> h) in
        let cell = (rheaplet_get <queue_cell A I> I (inspect <alias I> qout) ih) in
          match ! cell with
            queue_cellc _ _ b nextp =>
            let nextp = (owned_to_unowned <alias I> nextp) in
            do (consume_owned A1 b)
               (consume_owned <queue_cell A I> cell)
               (consume_unique_owned <rheaplet_queue A I> ih) 
               (dec <alias I> qout)
               cast (queue_datac A1 I h nextp qin) by symm q_Eq
            end
          | queue_celln _ _ b => 
            do (consume_owned A1 b)
               (consume_owned <queue_cell A I> cell)
               (consume_unique_owned <rheaplet_queue A I> ih) 
               (dec <alias I> qout)
               (dec <alias I> qin)
               cast (queue_datan A1 I h) by symm q_Eq
            end
          end 
    | queue_datan A1 I h =>
      impossible transs symm u
                        hypjoin (queue_is_empty q) tt by q_eq end
                        clash tt ff
                 end
        <queue A1>
    end.
