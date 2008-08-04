Include "../lib/minus.g".

Inductive mvec : Fun(n:nat).type :=
  mvecn : <mvec Z>
| mvecc : Fun(spec n:nat)(x:nat)(l:<mvec n>).
            <mvec (minus x n)>.

Inductive mvec_append_t : type :=
  mk_mvec_append_t : Fun(spec n:nat)(l:<mvec n>).mvec_append_t.

Define spec mvec_append :=
fun mvec_append(spec n m:nat)(l1 : <mvec n>)(l2 : <mvec m>):
              mvec_append_t.
    match l1 with
      mvecn => (mk_mvec_append_t m l2)
    | mvecc n' x l1' => 
       match (mvec_append n' m l1' l2) with
         mk_mvec_append_t o r =>
         (mk_mvec_append_t (minus x o) (mvecc o x r))
         end
    end.

Define mvec_append_tot :=
  induction(n m:nat)(l1:<mvec n>) 
  return Forall(l2:<mvec m>). 
          Exists(r:mvec_append_t). { (mvec_append l1 l2) = r} with
    mvecn => foralli(l2:<mvec m>). 
            existsi (mk_mvec_append_t m l2) { (mvec_append l1 l2) = *}
            hypjoin (mvec_append l1 l2) (mk_mvec_append_t l2)
            by l1_eq end
  | mvecc n' x l1' =>
    foralli(l2:<mvec m>). 
    existse [l1_IH n' m l1' l2]
    foralli(r:mvec_append_t)
           (ur:{ (mvec_append l1' l2) = r}).
    case r with
     mk_mvec_append_t n'm l1'2 =>
     abbrev ret = (mk_mvec_append_t 
                     terminates (minus x n'm) by minus_tot
                     (mvecc n'm x l1'2)) in
     existsi ret
       { (mvec_append l1 l2) = *} 
       hypjoin (mvec_append l1 l2) ret
       by l1_eq ur r_eq end
    end
  end.

Define mvec_append_assoc
 : Forall(n1 : nat)(l1 : <mvec n1>)
         (n2 n3 : nat)(l2 : <mvec n2>)(l3 : <mvec n3>)
         (n12 n23:nat)(l12:<mvec n12>)(l23:<mvec n23>)
         (u1:{ (mvec_append l1 l2) = (mk_mvec_append_t l12)})
         (u2:{ (mvec_append l2 l3) = (mk_mvec_append_t l23)}).
     { (mvec_append l12 l3) = (mvec_append l1 l23) } :=
  induction(n1:nat)(l1:<mvec n1>) 
  return Forall(n2 n3 : nat)(l2 : <mvec n2>)(l3 : <mvec n3>)
               (n12 n23:nat)(l12:<mvec n12>)(l23:<mvec n23>)
               (u1:{ (mvec_append l1 l2) = (mk_mvec_append_t l12)})
               (u2:{ (mvec_append l2 l3) = (mk_mvec_append_t l23)}).
          { (mvec_append l12 l3) = (mvec_append l1 l23) } with
    mvecn => foralli(n2 n3 : nat)(l2 : <mvec n2>)(l3 : <mvec n3>)
               (n12 n23:nat)(l12:<mvec n12>)(l23:<mvec n23>)
               (u1:{ (mvec_append l1 l2) = (mk_mvec_append_t l12)})
               (u2:{ (mvec_append l2 l3) = (mk_mvec_append_t l23)}).

            abbrev P12 = inj (mk_mvec_append_t *)
                          trans symm u1
                                hypjoin (mvec_append l1 l2) 
                                        (mk_mvec_append_t l2) 
                                by l1_eq end in
            trans cong (mvec_append * l3) P12
            trans u2 
                  hypjoin (mk_mvec_append_t l23)
                          (mvec_append l1 l23)
                  by l1_eq end

   | mvecc n1' x l1' => 
      foralli(n2 n3 : nat)(l2 : <mvec n2>)(l3 : <mvec n3>)
             (n12 n23:nat)(l12:<mvec n12>)(l23:<mvec n23>)
             (u1:{ (mvec_append l1 l2) = (mk_mvec_append_t l12)})
             (u2:{ (mvec_append l2 l3) = (mk_mvec_append_t l23)}).
        existse cinv (mvec_append n1' n2 l1' l2) 
                   trans symm eval (mvec_append (mvecc x l1') l2)
                   trans cong (mvec_append * l2) symm l1_eq 
                         u1 
        foralli(r:mvec_append_t)
               (ur:{(mvec_append l1' l2) = r}).

        case r with
         mk_mvec_append_t n1'2 l1'2 =>

         abbrev t1'2_3 = terminates (mvec_append n1'2 n3 l1'2 l3) 
                         by mvec_append_tot in

         case t1'2_3 with
           mk_mvec_append_t n1'2_3 l1'2_3 =>
           abbrev I = 
             [l1_IH n1' l1' n2 n3 l2 l3 n1'2 n23 l1'2 l23
               trans ur r_eq u2] in
           abbrev P1 = inj (mk_mvec_append_t *)
                       trans hypjoin (mk_mvec_append_t (mvecc x l1'2))
                                     (mvec_append l1 l2)
                             by l1_eq ur r_eq end
                         u1 in
           trans 
           hypjoin (mvec_append l12 l3) (mk_mvec_append_t (mvecc x l1'2_3))
           by P1 t1'2_3_eq end


           hypjoin (mk_mvec_append_t (mvecc x l1'2_3)) (mvec_append l1 l23)
           by l1_eq trans symm I t1'2_3_eq end


        end
      end
  end.
