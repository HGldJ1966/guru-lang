%Set "use_malloc".

Include "../guru-lang/tests/carraway/stdin.w".

Function append(^l1:owned)(^l2:owned).unowned :=
  match l1 with
    unil => (owned_to_unowned l2)
  | ucons a l1' => (ucons a (append l1' l2))
  end.

Function length(^l1:owned).unowned :=
  match l1 with
    unil => Z
  | ucons a l1' => (S (length l1'))
  end.

Global main :=
  let s = (read_all stdin) in
  let t = (append (inspect s) (inspect s)) in
  let l = (length (inspect t)) in
  do (dec ulist s)
     (dec ulist t)
     (dec nat l)
     tt
  end.

Function sublist(^n:owned)(!l:owned).<owned l> :=
  match n with
    Z => (clone_owned l)
  | S n' => match l with
              nil => abort
            | cons A a l' => 
                 let r = @ (sublist n' l') in
                 do (consume_owned A a) 
                    (consume_owned list l')
                    r
                 end                    
            end
  end.