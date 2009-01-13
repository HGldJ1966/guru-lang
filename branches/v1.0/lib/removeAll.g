Include "list.1.29.g".

Define neqcons : Fun(A:type)(eqfun: Fun(owned p q:A).bool)(n:A)(owned a:A)(l:<list A>).<list A> :=
  fun (A:type)(eqfun: Fun(owned p q:A).bool)(n:A)(owned a:A)(l:<list A>).
      match (eqfun n a) by ep et return <list A> with
        ff => (cons A a l)
      | tt => l
      end.

Define neqconsTot : Forall(A:type)(eqfun: Fun(p q:A).bool)(eqfunTot: Forall(p q:A).Exists(b:bool).{(eqfun p q) = b})(n a:A)(l:<list A>).Exists(ll:<list A>).{(neqcons A eqfun n a l) = ll} :=
  foralli(A:type)(eqfun: Fun(p q:A).bool)(eqfunTot: Forall(p q:A).Exists(b:bool).{(eqfun p q) = b})(n a:A)(l:<list A>).
    existse [eqfunTot n a]
      induction(b:bool) by bp bt IH return Forall(u:{(eqfun n a) = b}).Exists(ll:<list A>).{(neqcons A eqfun n a l) = ll} with
        ff => foralli(u:{(eqfun n a) = b}).
                existsi (cons A a l) {(neqcons A eqfun n a l) = *}
                  hypjoin (neqcons A eqfun n a l) (cons A a l) by trans u bp end
      | tt => foralli(u:{(eqfun n a) = b}).
                existsi l {(neqcons A eqfun n a l) = *}
                  hypjoin (neqcons A eqfun n a l) l by trans u bp end
      end.

Define neqconsPartialAppTot :
  Forall(A:type)
        (eqfun: Fun(p q:A).bool)
        (eqfunTot: Forall(p q:A).Exists(b:bool).{(eqfun p q) = b})
        (n:A).
  Exists(f: Fun(owned a:A)(l:<list A>).<list A>).{(neqcons A eqfun n) = f} :=
  foralli(A:type)
         (eqfun: Fun(p q:A).bool)
         (eqfunTot: Forall(p q:A).Exists(b:bool).{(eqfun p q) = b})
         (n:A).
  existse [neqconsTot A eqfun eqfunTot n n (nil A)]
    foralli(ll:<list A>)(u:{(neqcons A eqfun n n (nil A)) = ll}).
      cinv (neqcons A eqfun n)
        trans cong (* n nil) symm eval (neqcons A eqfun n)  u.

Define neqconsPartialFunTot :
  Forall(A:type)
        (eqfun: Fun(p q:A).bool)
        (eqfunTot: Forall(p q:A).Exists(b:bool).{(eqfun p q) = b})
        (n:A)
        (f: Fun(owned a:A)(l:<list A>).<list A>)
        (u:{(neqcons A eqfun n) = f})
        (a:A)
        (l:<list A>).
  Exists(ll:<list A>).{(f a l) = ll} :=
  foralli(A:type)
         (eqfun: Fun(p q:A).bool)
         (eqfunTot: Forall(p q:A).Exists(b:bool).{(eqfun p q) = b})
         (n:A)
         (f: Fun(owned a:A)(l:<list A>).<list A>)
         (u:{(neqcons A eqfun n) = f})
         (a:A)
         (l:<list A>).
  existse [neqconsTot A eqfun eqfunTot n a l]
    foralli(ll:<list A>)(u1:{(neqcons A eqfun n a l) = ll}).
      existsi ll {(f a l) = *}
        trans cong (* a l) symm u
        trans join ((neqcons A eqfun n) a l) (neqcons A eqfun n a l)
          u1.

Define removeAll :
  Fun(A:type)
     (eqfun: Fun(owned p q:A).bool)
     (a:A)
     (l:<list A>).<list A> :=
  fun(A:type)
     (eqfun: Fun(owned p q:A).bool)
     (a:A)
     (l:<list A>).
  (foldr A <list A> (neqcons A eqfun a) (nil A) l).

Define removeAllTot : Forall(A:type)(eqfun:Fun(p q:A).bool)(eqfunTot: Forall(p q:A).Exists(b:bool).{(eqfun p q) = b})(n:A)(l:<list A>).Exists(ll:<list A>).{(removeAll A eqfun n l) = ll} :=
  foralli(A:type)(eqfun:Fun(p q:A).bool)(eqfunTot: Forall(p q:A).Exists(b:bool).{(eqfun p q) = b})(n:A)(l:<list A>).
    existse [neqconsPartialAppTot A eqfun eqfunTot n]
      foralli(f:Fun(owned a:A)(l':<list A>).<list A>)(u:{(neqcons A eqfun n) = f}).
          abbrev u1 = [neqconsPartialFunTot A eqfun eqfunTot n f u] in
                existse [foldrTot A <list A> f u1 (nil A) l]
                  foralli(ll':<list A>)(u1:{(foldr A <list A> f (nil A) l) = ll'}).
                    existsi ll' {(removeAll A eqfun n l) = *}
                      trans join (removeAll A eqfun n l) (foldr A <list A> (neqcons A eqfun n) (nil A) l)
                      trans cong (foldr A <list A> * (nil A) l) u
                            u1.



Define removeAll_comm :
  Forall(A:type)
        (eqfun:Fun(p q:A).bool)
        (eqfunTot: Forall(p q:A).Exists(b:bool).{(eqfun p q) = b})
        (x y:A)
        (l:<list A>).
        {(removeAll A eqfun x (removeAll A eqfun y l)) = 
         (removeAll A eqfun y (removeAll A eqfun x l))} :=
  foralli(A:type)
         (eqfun:Fun(p q:A).bool)
         (eqfunTot: Forall(p q:A).Exists(b:bool).{(eqfun p q) = b})
         (x y:A).
    induction(l:<list A>) by lp lt IH_l
      return {(removeAll A eqfun x (removeAll A eqfun y l)) =
              (removeAll A eqfun y (removeAll A eqfun x l))} with
      nil A' =>
        symm trans cong (removeAll A eqfun y (removeAll A eqfun x *)) lp
        symm trans cong (removeAll A eqfun x (removeAll A eqfun y *)) lp
        join (removeAll A eqfun x (removeAll A eqfun y (nil A)))
             (removeAll A eqfun y (removeAll A eqfun x (nil A)))
    | cons A' a' l' =>
      abbrev ca = cast a' by inj <list *> symm lt in
      abbrev cl = cast l' by symm lt in
      existse [eqfunTot x ca]
      induction(b1:bool) by b1p b1t IH_b1 return Forall(u1:{(eqfun x a') = b1}).{(removeAll A eqfun x (removeAll A eqfun y l)) = (removeAll A eqfun y (removeAll A eqfun x l))} with
        ff =>
          foralli(u1:{(eqfun x a') = b1}).
          existse [eqfunTot y ca]
          induction(b2:bool) by b2p b2t IH_b2
            return Forall(u2:{(eqfun y a') = b2}).
                   {(removeAll A eqfun x (removeAll A eqfun y l)) =
                    (removeAll A eqfun y (removeAll A eqfun x l))} with
            ff => 
              foralli(u2:{(eqfun y a') = b2}).
              trans cong (removeAll A eqfun x (removeAll A eqfun y *)) lp
              trans cong (removeAll A eqfun x *)
                         hypjoin (removeAll A eqfun y (cons A' a' l'))
                                 (cons A' a' (removeAll A eqfun y l'))
                                   by lp trans u2 b2p end
              trans existse [removeAllTot A eqfun eqfunTot y cl]
                    foralli(ll:<list A>)(llu:{(removeAll A eqfun y l') = ll}).
                    symm trans cong (cons A a' (removeAll A eqfun x *)) llu
                    symm trans cong (removeAll A eqfun x (cons A' a' *)) llu
                    hypjoin (removeAll A eqfun x (cons A' a' ll))
                            (cons A a' (removeAll A eqfun x ll))
                              by lp trans u1 b1p end
              trans cong (cons A a' *) [IH_l cl]
              trans existse [removeAllTot A eqfun eqfunTot x cl]
                    foralli(ll:<list A>)(llu:{(removeAll A eqfun x l') = ll}).
                    trans cong (cons A a' (removeAll A eqfun y *)) llu
                    symm trans cong (removeAll A eqfun y (cons A' a' *)) llu
                    hypjoin (removeAll A eqfun y (cons A' a' ll))
                            (cons A a' (removeAll A eqfun y ll))
                              by lp trans u2 b2p end
              trans cong (removeAll A eqfun y *)
                         hypjoin (cons A' a' (removeAll A eqfun x l'))
                                 (removeAll A eqfun x (cons A' a' l'))
                                   by lp trans u1 b1p end
                    cong (removeAll A eqfun y (removeAll A eqfun x *)) symm lp
          | tt =>
              foralli(u2:{(eqfun y a') = b2}).
              trans cong (removeAll A eqfun x (removeAll A eqfun y *)) lp
              trans cong (removeAll A eqfun x *)
                         hypjoin (removeAll A eqfun y (cons A' a' l'))
                                 (removeAll A eqfun y l')
                                   by lp trans u2 b2p end
              trans [IH_l cl]
              trans existse [removeAllTot A eqfun eqfunTot x cl]
                    foralli(ll:<list A>)(llu:{(removeAll A eqfun x l') = ll}).
                    trans cong (removeAll A eqfun y *) llu
                    symm trans cong (removeAll A eqfun y (cons A' a' *)) llu
                    hypjoin (removeAll A eqfun y (cons A' a' ll))
                            (removeAll A eqfun y ll)
                              by lp trans u2 b2p end
              trans cong (removeAll A eqfun y *)
                         hypjoin (cons A' a' (removeAll A eqfun x l'))
                                 (removeAll A eqfun x (cons A' a' l'))
                                   by lp trans u1 b1p end
                    cong (removeAll A eqfun y (removeAll A eqfun x *)) symm lp
          end
      | tt =>
          foralli(u1:{(eqfun x a') = b1}).
          existse [eqfunTot y ca]
          induction(b2:bool) by b2p b2t IH_b2
            return Forall(u2:{(eqfun y a') = b2}).
                   {(removeAll A eqfun x (removeAll A eqfun y l)) =
                    (removeAll A eqfun y (removeAll A eqfun x l))} with
            ff =>
              foralli(u2:{(eqfun y a') = b2}).
              trans cong (removeAll A eqfun x (removeAll A eqfun y *)) lp
              trans cong (removeAll A eqfun x *)
                         hypjoin (removeAll A eqfun y (cons A' a' l'))
                                 (cons A' a' (removeAll A eqfun y l'))
                                   by lp trans u2 b2p end
              trans existse [removeAllTot A eqfun eqfunTot y cl]
                    foralli(ll:<list A>)(llu:{(removeAll A eqfun y l') = ll}).
                    symm trans cong (removeAll A eqfun x *) llu
                    symm trans cong (removeAll A eqfun x (cons A' a' *)) llu
                    hypjoin (removeAll A eqfun x (cons A' a' ll))
                            (removeAll A eqfun x ll)
                              by lp trans u1 b1p end
              trans [IH_l cl]
              trans cong (removeAll A eqfun y *)
                         hypjoin (removeAll A eqfun x l') 
                                 (removeAll A eqfun x (cons A' a' l'))
                                   by lp trans u1 b1p end
                    cong (removeAll A eqfun y (removeAll A eqfun x *)) symm lp
          | tt =>
              foralli(u2:{(eqfun y a') = b2}).
              trans cong (removeAll A eqfun x (removeAll A eqfun y *)) lp
              trans cong (removeAll A eqfun x *)
                         hypjoin (removeAll A eqfun y (cons A' a' l'))
                                 (removeAll A eqfun y l')
                                   by lp trans u2 b2p end
              trans [IH_l cl]
              trans cong (removeAll A eqfun y *)
                         hypjoin (removeAll A eqfun x l')
                                 (removeAll A eqfun x (cons A' a' l'))
                                   by lp trans u1 b1p end
                    cong (removeAll A eqfun y (removeAll A eqfun x *)) symm lp
          end
      end
  end.

Define removeAll_idem :
  Forall(A:type)
        (eqfun:Fun(p q:A).bool)
        (eqfunTot: Forall(p q:A).Exists(b:bool).{(eqfun p q) = b})
        (n:A)
        (l:<list A>).
        {(removeAll A eqfun n (removeAll A eqfun n l)) = 
         (removeAll A eqfun n l)} :=
  foralli(A:type)
         (eqfun:Fun(p q:A).bool)
         (eqfunTot: Forall(p q:A).Exists(b:bool).{(eqfun p q) = b})
         (n:A).
  induction(l:<list A>) by lp lt IH_l return {(removeAll A eqfun n (removeAll A eqfun n l)) = (removeAll A eqfun n l)} with
    nil A =>
      cong (removeAll A eqfun n *)
           trans cong (removeAll A eqfun n *) lp 
           trans join (removeAll A eqfun n (nil A)) (nil A)
                 symm lp
  | cons A' a ll =>
      abbrev ca = cast a by inj <list *> symm lt in
      abbrev cl = cast ll by symm lt in
      abbrev t_rAenl = terminates (removeAll A eqfun n cl) by [removeAllTot A eqfun eqfunTot n cl] in
      existse [eqfunTot n ca]
      induction(b:bool) by bp bt IH_b return Forall(u:{(eqfun n a) = b}).{(removeAll A eqfun n (removeAll A eqfun n l)) = (removeAll A eqfun n l)} with
        ff =>
          foralli(u:{(eqfun n a) = b}).
          trans cong (removeAll A eqfun n (removeAll A eqfun n *)) lp
          trans cong (removeAll A eqfun n *)
                     hypjoin (removeAll A eqfun n (cons A' a ll)) (cons A a (removeAll A eqfun n ll)) by trans u bp end
          trans hypjoin (removeAll A eqfun n (cons A' a t_rAenl))
                        (cons A' a (removeAll A eqfun n t_rAenl)) by lp trans u bp end
          %% The above 2 lines are much cleaner!
          %trans existse [removeAllTot A eqfun eqfunTot n cl]
          %      foralli(lll:<list A>)(lllu:{(removeAll A eqfun n ll) = lll}).
          %      symm trans cong (cons A' a (removeAll A eqfun n *)) lllu
          %      symm trans cong (removeAll A eqfun n (cons A' a *)) lllu
          %      hypjoin (removeAll A eqfun n (cons A' a lll))
          %              (cons A' a (removeAll A eqfun n lll))
          %                by lp trans u bp end
          trans cong (cons A' a *) [IH_l cl]
          trans hypjoin (cons A' a (removeAll A eqfun n ll)) (removeAll A eqfun n (cons A' a ll)) by trans u bp end
                cong (removeAll A eqfun n *)
                     symm lp
      | tt =>
          foralli(u:{(eqfun n a) = b}).
          trans cong (removeAll A eqfun n (removeAll A eqfun n *)) lp
          trans cong (removeAll A eqfun n *)
                     hypjoin (removeAll A eqfun n (cons A' a ll)) (removeAll A eqfun n ll) by lp trans u bp end
          trans [IH_l cl]
          trans hypjoin (removeAll A eqfun n ll) (removeAll A eqfun n (cons A' a ll)) by lp trans u bp end
                cong (removeAll A eqfun n *)
                     symm lp
      end
  end.
      
Define removeAll_appendf :
  Forall(A:type)
        (eqfun:Fun(p q:A).bool)
        (eqfunTot: Forall(p q:A).Exists(b:bool).{(eqfun p q) = b})
        (n:A)
        (l1 l2:<list A>).
        {(foldr A <list A> (neqcons A eqfun n) l1 l2) = 
          (appendf A (removeAll A eqfun n l2) l1)} :=
  foralli(A:type)
         (eqfun:Fun(p q:A).bool)
         (eqfunTot: Forall(p q:A).Exists(b:bool).{(eqfun p q) = b})
         (n:A)
         (l1:<list A>).
  induction(l2:<list A>) by l2p l2t IH_l2 return {(foldr A <list A> (neqcons A eqfun n) l1 l2) = (appendf A (removeAll A eqfun n l2) l1)} with
    nil A =>
      trans cong (foldr A <list A> (neqcons A eqfun n) l1 *) l2p
      trans join (foldr A <list A> (neqcons A eqfun n) l1 (nil A)) (appendf A (nil A) l1)
      trans cong (appendf A * l1)
                 join (nil A) (removeAll A eqfun n (nil A))
            cong (appendf A (removeAll A eqfun n *) l1) symm l2p
  | cons A a ll =>
      abbrev ca = cast a by inj <list *> symm l2t in
      abbrev cl = cast ll by symm l2t in
      existse [eqfunTot n ca]
      induction(b:bool) by bp bt IH_b return Forall(u:{(eqfun n a) = b}).{(foldr A <list A> (neqcons A eqfun n) l1 l2) = (appendf A (removeAll A eqfun n l2) l1)} with
        ff =>
          foralli(u:{(eqfun n a) = b}).
          trans cong (foldr A <list A> (neqcons A eqfun n) l1 *) l2p
          trans hypjoin (foldr A <list A> (neqcons A eqfun n) l1 (cons A a ll)) ((neqcons A eqfun n) a (foldr A <list A> (neqcons A eqfun n) l1 ll)) by trans u bp end
          trans cong ((neqcons A eqfun n) a *) [IH_l2 cl]
          trans hypjoin ((neqcons A eqfun n) a (appendf A (removeAll A eqfun n ll) l1)) (appendf A ((neqcons A eqfun n) a (removeAll A eqfun n ll)) l1) by trans u bp end
          trans cong (appendf A * l1)
                     hypjoin ((neqcons A eqfun n) a (removeAll A eqfun n ll)) (removeAll A eqfun n ((neqcons A eqfun n) a ll)) by trans u bp end
          trans cong (appendf A * l1)
                     hypjoin (removeAll A eqfun n ((neqcons A eqfun n) a ll)) (removeAll A eqfun n (cons A a ll)) by trans u bp end
                cong (appendf A * l1)
                     cong (removeAll A eqfun n *) symm l2p
      | tt =>
          foralli(u:{(eqfun n a) = b}).
          trans cong (foldr A <list A> (neqcons A eqfun n) l1 *) l2p
          trans hypjoin (foldr A <list A> (neqcons A eqfun n) l1 (cons A a ll)) ((neqcons A eqfun n) a (foldr A <list A> (neqcons A eqfun n) l1 ll)) by trans u bp end
          trans cong ((neqcons A eqfun n) a *) [IH_l2 cl]
          trans hypjoin ((neqcons A eqfun n) a (appendf A (removeAll A eqfun n ll) l1)) (appendf A ((neqcons A eqfun n) a (removeAll A eqfun n ll)) l1) by trans u bp end
          trans cong (appendf A * l1)
                     hypjoin ((neqcons A eqfun n) a (removeAll A eqfun n ll)) (removeAll A eqfun n ((neqcons A eqfun n) a ll)) by trans u bp end
          trans cong (appendf A * l1)
                     hypjoin (removeAll A eqfun n ((neqcons A eqfun n) a ll)) (removeAll A eqfun n (cons A a ll)) by trans u bp end
                cong (appendf A * l1)
                     cong (removeAll A eqfun n *) symm l2p
      end
  end.
