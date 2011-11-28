Include trusted "list.g".

Define erase :=
  fun erase(A:type)(eqA:Fun(^#owned x1 x2:A).bool)
           (^#owned x:A)(^#owned l:<list A>) : <list A>.
  match l with
    nil _ => (owned_to_unowned <list A> l)
  | cons _ y l' =>
      match (eqA (clone_owned A x) (clone_owned A y)) with
        ff => (cons A (owned_to_unowned A y) (erase A eqA x l'))
      | tt => (erase A eqA x l')
      end
  end.

Define erase_total :=
  foralli(A:type)
         (eqA:Fun(x1 x2:A).bool)
         (eqA_total:Forall(a b:A).Exists(z:bool).{(eqA a b) = z})
         (x:A).
  induction(l:<list A>) return Exists(l2:<list A>).{ (erase eqA x l) = l2 }
  with
    nil _ => existsi (nil A) { (erase eqA x l) = * }
               hypjoin (erase eqA x l) nil by l_eq end
  | cons _ y l' =>
    existse [l_IH l']
      foralli(l2':<list A>)(l2'_pf:{ (erase eqA x l') = l2' }).
    existse [eqA_total x y]
      foralli(z:bool)(z_pf:{ (eqA x y) = z }).
    case z by z_eq z_Eq with
      ff =>
        existsi (cons A y l2') { (erase eqA x l) = * }
          hypjoin (erase eqA x l) (cons A y l2') by l_eq z_pf z_eq l2'_pf end
    | tt =>
        existsi l2' { (erase eqA x l) = * }
          hypjoin (erase eqA x l) l2' by l_eq z_pf z_eq l2'_pf end
    end
  end.

Define member_ff_erase :
  Forall(A:type)(eqA:Fun(x1 x2:A).bool)
        (eqA_total:Forall(a b:A).Exists(z:bool).{(eqA a b) = z})
        (a:A)(l:<list A>)
        (u:{ (member a l eqA) = ff }).
    { (erase eqA a l) = l }
  :=
  foralli(A:type)(eqA:Fun(x1 x2:A).bool)
         (eqA_total:Forall(a b:A).Exists(z:bool).{(eqA a b) = z})
         (a:A).
  induction(l:<list A>) return
    Forall(u:{ (member a l eqA) = ff }).
      { (erase eqA a l) = l }
  with
    nil _ =>
      foralli(u:{ (member a l eqA) = ff }).
      hypjoin (erase eqA a l) l
        by l_eq end
  | cons _ a' l' =>
      foralli(u:{ (member a l eqA) = ff }).
      existse [eqA_total a a']
        foralli(z:bool)(z_pf:{ (eqA a a') = z }).
      case z with
        ff =>
          abbrev u' = % (member a (cons a' l') eqA) = ff
            trans cong (member a * eqA) symm l_eq
                  u
          in
          abbrev p = % (member a l' eqA) = ff
            [member_cons_ff_member A eqA eqA_total a a' l' u']
          in
          trans hypjoin (erase eqA a l)
                        (erase eqA a (cons a' l'))
                  by l_eq z_pf z_eq end
                hypjoin (erase eqA a (cons a' l'))
                        l
                  by l_eq z_pf z_eq [l_IH l' p] end
      | tt =>
          existse [member_total A a l' eqA eqA_total]
            foralli(z1:bool)(z1_pf:{ (member a l' eqA) = z1 }).
          contra
            trans symm u
            trans hypjoin (member a l eqA)
                          (or tt z1)
                    by l_eq z_pf z_eq z1_pf end
            trans [ortt_i1 tt z1 join tt tt]
                  clash tt ff
            { (erase eqA a l) = l }
      end
  end.

Define append_erase :
  Forall(A:type)(eqA:Fun(x1 x2:A).bool)
        (eqA_total:Forall(a b:A).Exists(z:bool).{(eqA a b) = z})
        (a:A)(l1 l2:<list A>).
    { (append A (erase A eqA a l1) (erase A eqA a l2))
      = (erase A eqA a (append A l1 l2)) }
  :=
  foralli(A:type)(eqA:Fun(x1 x2:A).bool)
         (eqA_total:Forall(a b:A).Exists(z:bool).{(eqA a b) = z})
         (a:A).
  induction(l1:<list A>) return
    Forall(l2:<list A>).
      { (append A (erase A eqA a l1) (erase A eqA a l2))
        = (erase A eqA a (append A l1 l2)) }
  with
    nil _ =>
      foralli(l2:<list A>).
      hypjoin (append A (erase A eqA a l1) (erase A eqA a l2))
              (erase A eqA a (append A l1 l2))
        by l1_eq end
  | cons _ a' l1' =>
      foralli(l2:<list A>).
      existse [eqA_total a a']
        foralli(z:bool)(z_pf:{ (eqA a a') = z }).
      case z with
        ff =>
          hypjoin (append A (erase A eqA a l1) (erase A eqA a l2))
                  (erase A eqA a (append A l1 l2))
            by l1_eq z_pf z_eq [l1_IH l1' l2] end
      | tt =>
          hypjoin (append A (erase A eqA a l1) (erase A eqA a l2))
                  (erase A eqA a (append A l1 l2))
            by l1_eq z_pf z_eq [l1_IH l1' l2] end
      end
  end.

