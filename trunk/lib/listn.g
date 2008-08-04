Include "nat.g".
Include "list.g".

Inductive listn : Fun(A:type)(n:nat). type :=
  niln : Fun(A:type). <listn A Z>
| consn : Fun(A:type)(n:nat)(a:A)(l:<listn A n>).<listn A (S n)>.

Define nthn :=
  fun nthn(A:type)(n:nat)(l:<listn A n>)(m:nat)(u:{ (lt m n) = tt }):A.
    match l by ul vl with
      niln A' => abort A
    | consn A' n' a' l' =>
         match m by um vm with
           Z => cast a' by symm inj <listn * **> vl
         | S m' => (nthn A n' cast l' by cong <listn * n'> 
                                          symm inj <listn * **> vl m'
                      symm
                      trans symm u
                      trans cong (lt * n) um 
                      trans cong (lt (S m') *) inj <listn ** *> vl
                            [S_lt_S m' n'])
         end
    end.

Define updaten : Fun(A:type)(n:nat)(l:<listn A n>)(m:nat)(a:A)
                    (u:{ (lt m n) = tt }).<listn A n> :=
    fun updaten(A:type)(n:nat)(l:<listn A n>)(m:nat)(a:A)
               (u:{ (lt m n) = tt }):<listn A n>.
      match l by ul vl with 
        niln A' => abort <listn A n>
      | consn A' n' a' l' =>
        abbrev P1 = symm inj <listn * **> vl in
        abbrev cl' = cast l' by cong <listn * n'> P1 in
        cast
           match m by um vm with
             Z => (consn A n' a cl')
           | S m' => (consn A n' cast a' by P1
                        (updaten A n' cl' m' a
                           symm
                           trans symm u
                           trans cong (lt * n) um 
                           trans cong (lt (S m') *) inj <listn ** *> vl
                                 [S_lt_S m' n']))
           end
        by
         cong <listn A *> symm inj <listn ** *> vl
      end.


Define mk_listn :=
   fun mk_listn(A:type)(a:A)(n:nat):<listn A n>.
      match n by un vn with
        Z => cast (niln A) by cong <listn A *> symm un
      | S n' => 
         cast (consn A n' a (mk_listn A a n'))
         by cong <listn A *> symm un
      end.

Define appendn : Fun(A:type)(n m:nat)(l1 : <listn A n>)(l2 : <listn A m>).
                 <listn A (plus n m)> :=
fun appendn(A:type)(n m:nat)(l1 : <listn A n>)(l2 : <listn A m>):
                 <listn A (plus n m)>.
    match l1 by u v return <listn A (plus n m)> with
      niln B => cast l2 by
                cong <listn A *>
                 symm trans
                        cong (plus * m)
                            inj <listn ** *> v
                        join (plus Z m) m
    | consn A' n' x l1' => 
       cast
          (consn A' (plus n' m) x (appendn A' n' m l1'
                                    cast l2 by cong <listn * m>
                                                 inj <listn * **> v)) 
       by trans
            cong <listn * (S (plus n' m))>
              symm inj <listn * **> v
            cong <listn A *>
               trans
                 symm join (plus (S n') m)
                           (S (plus n' m))
                 cong (plus * m)
                   symm inj <listn ** *> v
    end.

Define list_to_listn : Fun(A:type)(l:<list A>).<listn A (list_length A l)> :=
  fun list_to_listn(A:type)(l:<list A>):<listn A (list_length A l)>.
  match l by lp lt return <listn A (list_length A l)> with
    nil A' => cast (niln A) by
                cong <listn A *>
                     trans join Z (list_length A (nil A))
                           cong (list_length A *) symm lp
  | cons A' h t =>
      abbrev h' = cast h by symm inj <list *> lt in
      abbrev t' = cast t by cong <list *> symm inj <list *> lt in
      cast (consn A (list_length A t') h' (list_to_listn A t')) by
        cong <listn A *>
             trans join (S (list_length A t'))
                        (list_length A (cons A h t))
                   cong (list_length A *) symm lp
  end.

Define listn_to_list : Fun(A:type)(n:nat)(l:<listn A n>).<list A> :=
  fun listn_to_list(A:type)(n:nat)(l:<listn A n>):<list A>.
  match l by lp lt return <list A> with
    niln A' =>
      (nil A)
  | consn A' n' h t =>
      (cons A cast h by symm inj <listn * **> lt (listn_to_list A n' cast t by cong <listn * n'> symm inj <listn * **> lt))
  end.

Define list_listn_same : Forall(A:type)(l:<list A>).{ (listn_to_list A (list_length A l) (list_to_listn A l)) = l } :=
  foralli(A:type).
    induction(l:<list A>) by lp lt IHl return { (listn_to_list A (list_length A l) (list_to_listn A l)) = l } with
      nil A' =>
        trans cong (listn_to_list A (list_length A l) *)
                   trans cong (list_to_listn A *) lp
                         join (list_to_listn A (nil A)) (niln A)
        trans cong (listn_to_list A * (niln A))
                   trans cong (list_length A *) lp
                         join (list_length A (nil A)) Z
        trans join (listn_to_list A Z (niln A))
                   (nil A)
              symm lp
    | cons A' h t =>
        existse [list_length_total A cast t by cong <list *> symm inj <list *> lt]
          foralli(n:nat).
            foralli(u:{ (list_length A t) = n }).
              trans cong (listn_to_list A (list_length A *) (list_to_listn A *)) lp
              trans join (listn_to_list A (list_length A (cons A h t)) (list_to_listn A (cons A h t)))
                         (cons A h (listn_to_list A (list_length A t) (list_to_listn A t)))
              trans cong (cons A h *)
                         [IHl cast t by cong <list *> symm inj <list *> lt]
                    symm lp
    end.

Define list_length_listn : Forall(A:type)(n:nat)(l:<listn A n>).{ (list_length A (listn_to_list A n l)) = n } :=
  foralli(A:type).
    induction(n:nat) by np nt IHn return Forall(l:<listn A n>).{ (list_length A (listn_to_list A n l)) = n } with
      Z =>
        induction(l:<listn A n>) by lp lt IHl return { (list_length A (listn_to_list A n l)) = n } with
          niln A' =>
            trans cong (list_length A *)
                       trans cong (listn_to_list A n *) lp
                       trans cong (listn_to_list A * (niln A)) np
                             join (listn_to_list A Z (niln A)) (nil A)
            trans join (list_length A (nil A)) Z
                  symm np
        | consn A' n'' h t =>
            contra trans inj <listn ** *>
                             trans cong <listn A *> symm np
                                   lt
                         clash (S n'') Z
                   { (list_length A (listn_to_list A n l)) = n }
        end
    | S n' =>
        induction(l:<listn A n>) by lp lt IHl return { (list_length A (listn_to_list A n l)) = n } with
          niln A' =>
            contra trans inj <listn ** *>
                             trans symm lt
                                   cong <listn A *> np
                         clash (S n') Z
                   { (list_length A (listn_to_list A n l)) = n }
        | consn A' n'' h t =>
            trans cong (list_length A (listn_to_list A n *)) lp
            trans cong (list_length A (listn_to_list A * (consn A n'' h t))) np
            trans join (list_length A (listn_to_list A (S n') (consn A n'' h t)))
                       (S (list_length A (listn_to_list A n' t)))
            trans cong (S *) [IHn n' cast t by trans cong <listn * n''> symm inj <listn * **> lt cong <listn A *> inj (S *) trans symm inj <listn ** *> lt np]
                  symm np
        end
    end.

% there is a lot of redundant code here -- the breakouts might be necessary?!  think about this..
Define listn_list_same : Forall(A:type)(n:nat)(l:<listn A n>).{ (list_to_listn A (listn_to_list A n l)) = l } :=
  foralli(A:type).
    induction(n:nat) by np nt IHn return Forall(l:<listn A n>).{ (list_to_listn A (listn_to_list A n l)) = l } with
      Z =>
        induction(l:<listn A n>) by lp lt IHl return { (list_to_listn A (listn_to_list A n l)) = l } with
          niln A' =>
            trans cong (list_to_listn A (listn_to_list A n *)) lp
            trans join (list_to_listn A (listn_to_list A n (niln A)))
                       (niln A)
                  symm lp
        | consn A' n' h t =>
            %% this breakout is probably not necessary
            [ induction(n'':nat) by n''p n''t IHn'' return Forall(u:{ n' = n'' }).{ (list_to_listn A (listn_to_list A n l)) = l } with
                Z =>
                  foralli(u:{ n' = n'' }).
                    trans cong (list_to_listn A *)
                               trans cong (listn_to_list A n *) lp
                               trans cong (listn_to_list A n (consn A * h t)) trans u n''p
                                     join (listn_to_list A n (consn A Z h t))
                                          (cons A h (listn_to_list A n' t))
                    trans join (list_to_listn A (cons A h (listn_to_list A n' t)))
                               (consn A (list_length A (listn_to_list A Z t)) h (list_to_listn A (listn_to_list A n' t)))
                    trans cong (consn A (list_length A (listn_to_list A Z t)) h *)
                               [IHn n' cast t by cong <listn * n'> symm inj <listn * **> lt]
                    trans cong (consn A * h t)
                               trans cong (list_length A (listn_to_list A * t)) symm trans u n''p
                                     [list_length_listn A n' cast t by cong <listn * n'> symm inj <listn * **> lt]
                          symm lp
              | S n''' =>%% (consn A (list_length A (listn_to_list A Z t)) h t)
                  foralli(u:{ n' = n'' }).
                    trans cong (list_to_listn A *)
                               trans cong (listn_to_list A n *) lp
                               trans cong (listn_to_list A n (consn A * h t)) trans u n''p
                                     join (listn_to_list A n (consn A (S n''') h t))
                                          (cons A h (listn_to_list A n' t))
                    trans join (list_to_listn A (cons A h (listn_to_list A n' t)))
                               (consn A (list_length A (listn_to_list A (S n''') t)) h (list_to_listn A (listn_to_list A n' t)))
                    trans cong (consn A (list_length A (listn_to_list A (S n''') t)) h *)
                               [IHn n' cast t by cong <listn * n'> symm inj <listn * **> lt]
                    trans cong (consn A * h t)
                               trans cong (list_length A (listn_to_list A * t)) symm trans u n''p
                                     [list_length_listn A n' cast t by cong <listn * n'> symm inj <listn * **> lt]
                          symm lp
              end n' join n' n' ]
        end
    | S npred =>
        induction(l:<listn A n>) by lp lt IHl return { (list_to_listn A (listn_to_list A n l)) = l } with
          niln A' =>
            trans cong (list_to_listn A (listn_to_list A n *)) lp
            trans join (list_to_listn A (listn_to_list A n (niln A)))
                       (niln A)
                  symm lp
        | consn A' n' h t =>
            %% this breakout is probably not necessary
            [ induction(n'':nat) by n''p n''t IHn'' return Forall(u:{ n' = n'' }).{ (list_to_listn A (listn_to_list A n l)) = l } with
                Z =>
                  foralli(u:{ n' = n'' }).
                    trans cong (list_to_listn A *)
                               trans cong (listn_to_list A n *) lp
                               trans cong (listn_to_list A n (consn A * h t)) trans u n''p
                                     join (listn_to_list A n (consn A Z h t))
                                          (cons A h (listn_to_list A n' t))
                    trans join (list_to_listn A (cons A h (listn_to_list A n' t)))
                               (consn A (list_length A (listn_to_list A Z t)) h (list_to_listn A (listn_to_list A n' t)))
                    trans cong (consn A (list_length A (listn_to_list A Z t)) h *)
                               [IHn n' cast t by cong <listn * n'> symm inj <listn * **> lt]
                    trans cong (consn A * h t)
                               trans cong (list_length A (listn_to_list A * t)) symm trans u n''p
                                     [list_length_listn A n' cast t by cong <listn * n'> symm inj <listn * **> lt]
                          symm lp
              | S n''' =>%% (consn A (list_length A (listn_to_list A Z t)) h t)
                  foralli(u:{ n' = n'' }).
                    trans cong (list_to_listn A *)
                               trans cong (listn_to_list A n *) lp
                               trans cong (listn_to_list A n (consn A * h t)) trans u n''p
                                     join (listn_to_list A n (consn A (S n''') h t))
                                          (cons A h (listn_to_list A n' t))
                    trans join (list_to_listn A (cons A h (listn_to_list A n' t)))
                               (consn A (list_length A (listn_to_list A (S n''') t)) h (list_to_listn A (listn_to_list A n' t)))
                    trans cong (consn A (list_length A (listn_to_list A (S n''') t)) h *)
                               [IHn n' cast t by cong <listn * n'> symm inj <listn * **> lt]
                    trans cong (consn A * h t)
                               trans cong (list_length A (listn_to_list A * t)) symm trans u n''p
                                     [list_length_listn A n' cast t by cong <listn * n'> symm inj <listn * **> lt]
                          symm lp
              end n' join n' n' ]
        end
    end.


%-

Define test := (nth nat (S (S Z))
                   (cons nat (S Z)
                   (cons nat (S (S Z))
                   (cons nat (S (S (S Z))) (nil nat))))).


Set "print_parsed".

Interpret test.

-%
