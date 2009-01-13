
Define trie_lookup_interp :
  Forall(A:type)(t:<trie A>)(s:string)(a:A)
        (u:{ (trie_lookup t s) = (something a) }).
        Exists(l1 l2:<list <pair string A>>).
        { (trie_interp t) = (append l1 (cons (mkpair s a) l2)) } :=
  foralli(A:type)(t:<trie A>)(s:string)(a:A)
         (u:{ (trie_lookup t s) = (something a) }). 
    [induction(n:nat)
       return Forall(t:<trie A>)
                    (un: { (le size t n) = tt })
                    (s:string)
                    (u:{ (trie_lookup t s) = (something a) }). 
               Exists(l1 l2:<list <pair string A>>).
                 { (trie_interp t) = (append l1 (cons (mkpair s a) l2)) }
     with
       Z =>
         foralli(t:<trie A>)
                (un: { (le size t n) = tt })
                (s:string)
                (u:{ (trie_lookup t s) = (something a) }). 
          abbrev F = Exists(l1 l2:<list <pair string A>>).
                      { (trie_interp t) = (append l1 (cons (mkpair s a) l2)) } 
          in
          abbrev tZ = [le_Z1 size t trans cong (le size t *) symm n_eq un] in
           case t with
             trie_none A' => 
               contra
                 trans trans hypjoin (S Z) size t by t_eq end 
                       tZ
                       clash Z (S Z)
               F
           | trie_exact A' s a' => 
               contra
                 trans trans hypjoin (S (plus size s size a'))
                                     size t by t_eq end 
                       tZ
                       clash Z (S terminates (plus size s size a') 
                                  by plus_total)
               F
           | trie_next A' o' l' =>
               contra
                 trans trans hypjoin (S (plus size o' size l'))
                                     size t by t_eq end 
                       tZ
                       clash Z (S terminates (plus size o' size l') 
                                  by plus_total)
               F
           end
     | S n' => 
         foralli(t:<trie A>)
                (un: { (le size t n) = tt })
                (s:string)
                (u:{ (trie_lookup t s) = (something a) }). 
         abbrev F = Exists(l1 l2:<list <pair string A>>).
                     { (trie_interp t) = (append l1 (cons (mkpair s a) l2)) } 
         in
           case t with
             trie_none A' => 
             contra
               trans
                 trans hypjoin nothing (trie_lookup t s) by t_eq end
                       u 
                 clash (something a) nothing
               F
           | trie_exact A' s' a' => 
              abbrev iseq = terminates (stringeq s s') 
                            by [eqlist_total char s s'] in
              case iseq with
                ff => 
                contra
                  trans
                    trans hypjoin nothing (trie_lookup t s) by t_eq iseq_eq end
                          u 
                    clash (something a) nothing 
                  F
              | tt => existsi (nil <pair string A>)
                      Exists(l2:<list <pair string A>>).
                        { (trie_interp t) = (append * (cons (mkpair s a) l2)) }
                     existsi (nil <pair string A>)
                        { (trie_interp t) = (append nil (cons (mkpair s a) *))}
                      hypjoin (trie_interp t) 
                              (append nil (cons (mkpair s a) nil))
                      by t_eq iseq_eq [stringeqEq s s' iseq_eq]
                         inj (something *) hypjoin (something a) 
                                                   (something a')
                                           by u t_eq iseq_eq end end
              end
           | trie_next A' o' l' => 
             abbrev P = symm inj <trie *> t_Eq in
             abbrev o = cast o' by cong <option *> P in
             abbrev l = cast l' by cong <charvec <trie *>> P in
             case s with
               nil B => 
                 case o with
                   nothing A'' =>
                     contra
                       trans trans hypjoin nothing (trie_lookup t s)
                                   by t_eq s_eq o_eq end
                               u
                         clash (something a) nothing
                     F
                | something A' a' =>
                  abbrev ca' = cast a' by symm inj <option *> o_Eq in
                  abbrev T = <pair string A> in
                  abbrev cS = (cvfold l (mk_trie_interp_i2 trie_interp) 
                                 trie_interp_h2 nil) in
                  existse [trie_interp_charvec_tot A l]
                  foralli(r:<list T>)
                         (ur:{ cS = r}).
                  existsi (nil T)
                    Exists(l2:<list T>).
                     { (trie_interp t) = (append * (cons (mkpair s a) l2))}
                  existsi r
                    { (trie_interp t) = (append nil (cons (mkpair s a) *))}
                    trans cong (trie_interp *)
                            t_eq
                    trans evalto (trie_interp (trie_next o' l'))
                          let S = cS in
                            match o' with
                              nothing => S
                            | something a' => (cons (mkpair nil a') S)
                            end
                    trans cong let S = * in
                                match o' with
                                  nothing => S
                                | something a' => (cons (mkpair nil a') S)
                                end
                            ur
                    trans cong let S = r in 
                                match * with
                                  nothing => S
                                | something a' => (cons (mkpair nil a') S)
                                end
                           o_eq
                    trans join let S = r in 
                             match (something a') with
                               nothing => S
                             | something a' => (cons (mkpair nil a') S)
                             end
                           (cons (mkpair nil a') r)
                    trans cong (cons (mkpair * a') r)
                            symm s_eq
                    trans cong (cons (mkpair s *) r)
                            symm 
                            inj (something *)
                              trans
                                symm u
                                hypjoin (trie_lookup t s) (something a')
                                by t_eq o_eq s_eq end
                       join (cons (mkpair s a) r) 
                            (append nil (cons (mkpair s a) r)) 
                end
             | cons B b s2' => 
               abbrev P = symm inj <list *> s_Eq in
               abbrev c = cast b by P in
               abbrev s2 = cast s2' by symm s_Eq in
               abbrev tnc = terminates (which_char c) by to_nat_tot in
               existse [vec_get_sztot <trie A> num_chars l tnc 
                         [chars_bounded c]]
               foralli(a:<trie A>)(sa:{(lt size a size l) = tt})
                      (ua:{(vec_get l' tnc) = a}).
               show
                 trans hypjoin (trie_lookup t s) 
                               (trie_lookup (vec_get l tnc) s2)
                       by t_eq s_eq end
                     cong (trie_lookup * s2)
                       ua
               end

             end
          end
     end
    size t t join size t size t s u].































         foralli(t:<trie A>)
                (u:{ (trie_lookup t s) = (something a) }). 
         case t with
           trie_none A'' => 
             contra
               trans
                 trans hypjoin nothing (trie_lookup t s) by t_eq end
                       u 
                 clash (something a) nothing
               Exists(l1 l2:<list <pair string A>>).
                 { (trie_interp t) = (append l1 (cons (mkpair s a) l2)) }
         | trie_exact A' s' a' =>
           abbrev iseq = terminates (stringeq s s') 
                         by [eqlist_total char s s'] in
           case iseq with
             ff => 
             contra
               trans
                 trans hypjoin nothing (trie_lookup t s) by t_eq iseq_eq end
                       u 
                 clash (something a) nothing 
               Exists(l1 l2:<list <pair string A>>).
                 { (trie_interp t) = (append l1 (cons (mkpair s a) l2)) }
           | tt => existsi (nil <pair string A>)
                     Exists(l2:<list <pair string A>>).
                       { (trie_interp t) = (append * (cons (mkpair s a) l2)) }
                   existsi (nil <pair string A>)
                      { (trie_interp t) = (append nil (cons (mkpair s a) *)) }
                      hypjoin (trie_interp t) 
                              (append nil (cons (mkpair s a) nil))
                      by t_eq iseq_eq [stringeqEq s s' iseq_eq]
                         inj (something *) hypjoin (something a) 
                                                   (something a')
                                           by u t_eq iseq_eq end end
           end
        | trie_next A' o' l' => 
          
         end
    | cons A' a' l' =>
      truei
    end
  s t u].









Define shiftl :=
  fun(b:bool)(n:nat).
    match b with
      ff => Z
    | tt => (pow2 n)
    end.

Define bit :=
  fun bit(n x : nat):bool.
    match x with
      Z => (mod2 n)
    | S x' => (bit (div2 n) x')
    end.



%- 

Define read_all :=
  fun read_all (unique stdin : stdin_t)(l : <list char>) : <list char>.
    match (next_char stdin) with
      getc_none => l
    | getc_char a stdin' => 

-%

Inductive cvget_t : Fun(A:type).type :=
  mk_cvget_t : Fun(A:type)(unique a:A)(l:<vec A num_chars>)


