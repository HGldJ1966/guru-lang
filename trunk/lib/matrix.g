Include "llist.g".

Include "rat.g".

Inductive matrix : Fun(m n:nat).type :=
  mkmatrix : Fun(m n:nat)(l:<llist <llist rat n> m>).<matrix m n>.

Define mdata := fun(m n:nat)(M:<matrix m n>).
   match M by x y return <llist <llist rat n> m> with
     mkmatrix m' n' l' => 
       cast l' by
         trans cong <llist <llist rat *> m'> symm inj <matrix ** *> y
               cong <llist <llist rat n> *> symm inj <matrix * **> y
   end.

Set "print_parsed".
%Set "comment_vars".

Define madd := 
  fun (m n:nat)(M1 M2 : <matrix m n>).
    (mkmatrix m n 
      (fun outer(m:nat)(m1 m2 : <llist <llist rat n> m>) 
           : <llist <llist rat n> m>.
         abbrev G = <llist <llist rat n> m> in
         match m1 by x1 y1 return G with
           llistn A' => 
             cast (llistn <llist rat n>)
             by cong <llist <llist rat n> *> symm inj <llist ** *>
                                                  y1
         | llistc A' a' m' l' => 
           match m2 by x2 y2 return G with
             llistn A'' => abort G % cannot happen
           | llistc A'' a'' m'' l'' =>
               (llistc <llist rat n> 
                  abort <llist rat n>
                  m'
                  (outer m' 
                     cast l' by cong <llist * m'> 
                                  symm inj <llist * **> y1
                     cast l'' by trans cong <llist * m''> 
                                          symm inj <llist * **> y2
                                       cong <llist <llist rat n> *>
                                         inj <llist ** (S *)>
                                            symm trans symm y1 y2))
           end
         end
       (mdata m n M1)
       (mdata m n M2))).