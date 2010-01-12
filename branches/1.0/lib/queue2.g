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

Define spec queue_cell_inv := fun(A:type)(spec I:rheaplet_id)(bound:nat)(c:<queue_cell A I>).
                                 match c with queue_cellc _ _ a nextp => (lt nextp bound)
                                            | queue_celln _ _ a => tt
                                 end.

Define queue_cell_inv_tot :=
  foralli(A:type)(I:rheaplet_id)(bound:nat)(c:<queue_cell A I>).
    case c with
      queue_cellc _ _ a nextp => existsi (lt nextp bound) { (queue_cell_inv bound c) = * }
                                   hypjoin (queue_cell_inv bound c) (lt nextp bound)
                                   by c_eq end
    | queue_celln _ _ a => existsi tt { (queue_cell_inv bound c) = * }
                              hypjoin (queue_cell_inv bound c) tt
                              by c_eq end
    end.

Total queue_cell_inv queue_cell_inv_tot.

Define predicate rheaplet_queue_inv_h := 
  fun(A:type)(I:rheaplet_id)(bound:nat)(r:<rheaplet_queue A I>).
   { (list_all (queue_cell_inv bound) r) = tt }.

Define predicate rheaplet_queue_inv := 
  fun(A:type)(I:rheaplet_id)(r:<rheaplet_queue A I>).
   { (list_all (queue_cell_inv (length r)) r) = tt }.

Define weaken_rheaplet_queue_inv_h : 
  Forall(A:type)(I:rheaplet_id)(r:<rheaplet_queue A I>)
        (bound1 bound2:nat)
        (u1:@<rheaplet_queue_inv_h A I bound1 r>)
        (u2:{(lt bound1 bound2) = tt}).
    @<rheaplet_queue_inv_h A I bound2 r> :=
  foralli(A:type)(I:rheaplet_id)(r:<rheaplet_queue A I>)
         (bound1 bound2:nat)
         (u1:@<rheaplet_queue_inv_h A I bound1 r>)
         (u2:{(lt bound1 bound2) = tt}).
    [list_all_implies <queue_cell A I> 
      (queue_cell_inv A I bound1) (queue_cell_inv A I bound2)
      foralli(c:<queue_cell A I>)(u:{(queue_cell_inv bound1 c) = tt}). 
        case c with
          queue_cellc _ _ a nextp => hypjoin (queue_cell_inv bound2 c) tt
                                     by c_eq u [lt_trans nextp bound1 bound2 
                                                  hypjoin (lt nextp bound1) tt by c_eq u end
                                                  u2] 
                                     end
        | queue_celln _ _ a => hypjoin (queue_cell_inv bound2 c) tt
                               by c_eq end
        end
      r u1].

Define queue_cell_has_next : Fun(A:type)(spec I:rheaplet_id)(c:<queue_cell A I>).bool :=
  fun(A:type)(spec I:rheaplet_id)(c:<queue_cell A I>):bool.
    match c with
      queue_cellc _ _ a p => 
        do (dec <alias I> p)
           tt
        end
    | queue_celln _ _ a => 
        ff
    end.

Inductive queue : Fun(A:type).type :=
  queue_datac : Fun(A:type)(spec I:rheaplet_id)(#unique h:<rheaplet_queue A I>)
                   (qin qout : <alias I>)
                   (inv_qin : {(lt qin (length h)) = tt})
                   (inv_qout : {(lt qout (length h)) = tt})
                   (inv : @<rheaplet_queue_inv A I h>)
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
    match ! q with
      queue_datac _ I h qin qout _ _ _ _ => 
        ff
    | queue_datan _ I h _ => 
        tt
    end.    

Define queue_front : Fun(spec A:type)(^#unique_owned q:<queue A>)(u:{ (queue_is_empty q) = ff }).A :=
  fun(spec A:type)(^#unique_owned q:<queue A>)(u:{ (queue_is_empty q) = ff }).
    match ! q with
      queue_datac _ I h qin qout _ _ _ _ => 
        let cell = (rheaplet_get <queue_cell A I> I qout h) in
           match ! cell by v1 _ with
             queue_cellc _ _ a nextp => (owned_to_unowned A a)
           | queue_celln _ _ a => (owned_to_unowned A a)
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
    queue_datac A1 I h qin qout inv_qin inv_qout inv inv_qin2 => 
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
               abbrev qin_lt_length_h' = 
                           [lt_trans qin (length <queue_cell A I> h) (length <queue_cell A I> h')
                              inv_qin
                              trans cong (lt (length h) *)
                                      [rheaplet_in_length2 <queue_cell A I>
                                          I h h' (queue_celln A1 I a) new_qin i]
                                    [lt_S (length <queue_cell A I> h)]] in
               abbrev h''_eq2 = trans h''_eq 
                                  join (rheaplet_set (inspect qin) h' (queue_cellc x (inc new_qin)))
                                       (rheaplet_set qin h' (queue_cellc x new_qin)) in
               abbrev length_h''_eq = 
                  trans cong (length *) h''_eq2
                        [rheaplet_set_length 
                           <queue_cell A I> I h' (queue_cellc A1 I x new_qin) qin
                           qin_lt_length_h'] in
              abbrev length_h_lt_length_h'' = 
                       trans cong (lt (length h) *)
                              trans length_h''_eq
                                    [rheaplet_in_length2 <queue_cell A I> I h h' 
                                       (queue_celln A1 I a) new_qin i]
                            [lt_S (length <queue_cell A I> h)] in
              abbrev new_qin_lt_length_h'' = trans cong (lt new_qin *) length_h''_eq
                                               [rheaplet_in_length <queue_cell A I> I h h' 
                                                 (queue_celln A1 I a) new_qin i] in
               do (dec <alias I> qin)
                  cast (queue_datac A1 I h'' new_qin qout new_qin_lt_length_h''
                          [lt_trans qout (length <queue_cell A I> h) (length <queue_cell A I> h'')
                              inv_qout length_h_lt_length_h'']
                          abbrev f = (queue_cell_inv A I (length <queue_cell A I> h'')) in
                            trans cong (list_all (queue_cell_inv (length h'')) *) h''_eq2
                              [rheaplet_set_list_all <queue_cell A I> f
                                I h' (queue_cellc A1 I x new_qin) qin
                                [rheaplet_in_list_all <queue_cell A I>
                                  f
                                  [queue_cell_inv_tot A I (length <queue_cell A I> h'')]
                                  I h h' (queue_celln A1 I a) new_qin
                                  [weaken_rheaplet_queue_inv_h A I h 
                                    (length <queue_cell A I> h) (length <queue_cell A I> h'')
                                    inv length_h_lt_length_h'']
                                  join ((queue_cell_inv (length h'')) (queue_celln a)) tt
                                  i]
                                hypjoin ((queue_cell_inv (length h'')) (queue_cellc x new_qin)) tt
                                  by new_qin_lt_length_h'' end
                                qin_lt_length_h']
                          hypjoin (queue_cell_has_next (rheaplet_get new_qin h'')) ff
                          by h''_eq2 [rheaplet_in_get <queue_cell A I> I h h' new_qin
                                        (queue_celln A I a) i]
                             [rheaplet_set_get <queue_cell A I> I h' new_qin qin 
                               (queue_cellc A I x (inc <alias I> new_qin))
                               symm
                               [lt_implies_neq qin new_qin
                                 trans cong (lt qin *)
                                        symm inj (return_rheaplet_in ** *) 
                                               trans join (return_rheaplet_in
                                                            (append h (cons (queue_celln a) nil)) (length h))
                                                          (rheaplet_in h (queue_celln a))
                                                     i 
                                       inv_qin]]
                          end
                      ) by symm q_Eq
               end
           end
        end
     end
  | queue_datan A1 I h inv =>
    match (rheaplet_in <queue_cell A I> I h (queue_celln A1 I a)) by i _ with
      return_rheaplet_in _ _ h' new_qout => 
        abbrev new_qout_lt_length_h' = [rheaplet_in_length <queue_cell A I> I h h'(queue_celln A1 I a) new_qout i] in
        cast (queue_datac A1 I h' (inc <alias I> new_qout) new_qout
                trans join (lt (inc <alias I> new_qout) (length h'))
                           (lt new_qout (length h'))
                      new_qout_lt_length_h'
                new_qout_lt_length_h'
                [rheaplet_in_list_all <queue_cell A I>
                   (queue_cell_inv A I (length <queue_cell A I> h'))
                   [queue_cell_inv_tot A I (length <queue_cell A I> h')]
                   I h h' (queue_celln A1 I a) new_qout
                   [weaken_rheaplet_queue_inv_h A I h 
                      (length <queue_cell A I> h) (length <queue_cell A I> h') inv 
                      trans cong (lt (length h) *)
                              [rheaplet_in_length2 <queue_cell A I> I h h' 
                                (queue_celln A1 I a) new_qout i]
                            [lt_S (length <queue_cell A I> h)]]
                   join ((queue_cell_inv (length h')) (queue_celln a)) tt
                   i]
                hypjoin (queue_cell_has_next (rheaplet_get (inc new_qout) h')) ff
                by [rheaplet_in_get <queue_cell A I> I h h' new_qout (queue_celln A I a) i]
                end
             ) by symm q_Eq
    end
  end.

Define dequeue : Fun(spec A:type)(#unique q:<queue A>)(u:{ (queue_is_empty q) = ff }).#unique <queue A> :=
  fun(spec A:type)(#unique q:<queue A>)(u:{ (queue_is_empty q) = ff }):#unique <queue A>.
    match q with
      queue_datac A1 I h qin qout inv_qin inv_qout inv inv_qin2 => 
        let ih = (inspect_unique <rheaplet_queue A I> h) in
        let cell = (rheaplet_get <queue_cell A I> I (inspect <alias I> qout) ih) in
          match ! cell by cell_eq2 _ with
            queue_cellc _ _ b nextp =>
            let nextp = (owned_to_unowned <alias I> nextp) in
            do (consume_owned A1 b)
               (consume_owned <queue_cell A I> cell)
               (consume_unique_owned <rheaplet_queue A I> ih) 
               (dec <alias I> qout)
               cast (queue_datac A1 I h qin nextp
                       inv_qin 
                       trans hypjoin (lt nextp (length h))
                                     ((queue_cell_inv (length h)) cell)
                             by cell_eq2 nextp_eq end
                          [rheaplet_get_list_all <queue_cell A I>
                             (queue_cell_inv A I (length <queue_cell A I> h))
                             [queue_cell_inv_tot A I (length <queue_cell A I> h)]
                             I ih cell (inspect <alias I> qout) 
                             trans hypjoin (list_all (queue_cell_inv (length h)) ih) 
                                           (list_all (queue_cell_inv (length h)) h) 
                                   by ih_eq end
                                 inv 
                             symm cell_eq]
                       inv
                       inv_qin2) by symm q_Eq
            end
          | queue_celln _ _ b => 
            do (consume_owned A1 b)
               (consume_owned <queue_cell A I> cell)
               (consume_unique_owned <rheaplet_queue A I> ih) 
               (dec <alias I> qout)
               (dec <alias I> qin)
               cast (queue_datan A1 I h inv) by symm q_Eq
            end
          end 
    | queue_datan A1 I h inv =>
      impossible transs symm u
                        hypjoin (queue_is_empty q) tt by q_eq end
                        clash tt ff
                 end
        <queue A1>
    end.
