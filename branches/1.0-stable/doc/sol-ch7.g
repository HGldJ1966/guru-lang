Include "../guru-lang/lib/minmax.g".

Inductive slist : Fun(n:nat).type :=
  snil : <slist Z>
| scons : Fun(n n':nat)(l:<slist n'>)(u:{ (le n' n) = tt}).
          <slist n>.

Define insert : Fun(x n:nat)(l:<slist n>).<slist (max x n)> :=
  fun insert(x n:nat)(l:<slist n>):<slist (max x n)>.
    match l with
      snil => 
        cast (scons x Z snil [Z_le x])
        by cong <slist *>
             symm  
             trans cong (max x *) inj <slist *> l_Eq
             trans [max_comm x Z]
                   join (max Z x) x
    | scons _ n' l' u => 
        match (le x n) by q1 ign with
          ff => 
            cast (scons x n l [le_ff_implies_le x n q1])
            by cong <slist *>
                 symm
                  trans [max_comm x n]
                        [max_le n x [le_ff_implies_le x n q1]] 
        | tt => 
            cast
            (scons n (max x n') (insert x n' l')
              [max_bound x n' n q1 u])
            by
              cong <slist *>
                symm [max_le x n q1]
        end
    end.