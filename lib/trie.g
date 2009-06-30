Include "qcharray.g".
Include "string.g".
Include "option.g".
Include "pair.g".

%- <trie A> is the type for tries storing elts of type A. 

   trie_next holds data in "o" if the empty string maps to
   that data. -%
Inductive trie : Fun(A:type).type :=
  trie_none : Fun(spec A:type).#unique <trie A>
| trie_exact : Fun(A:type)(s:string)(a:A).#unique <trie A>
| trie_next : Fun(A:type)(o:<option A>)
                 (#unique l:<qcharray <trie A> stringn>). 
              #unique <trie A>.

Inductive trie_insert_i : Fun(A:type).type :=
  mk_trie_insert_i : Fun(A:type).<trie_insert_i A>.

% insert (s,a) into t, discarding any previous value stored for s.
Define trie_insert : Fun(A:type)(s:string)(a:A)(#unique t:<trie A>).
                         #unique <trie A> :=
  fun trie_insert(A:type)(s:string)(a:A)(#unique t:<trie A>) : #unique <trie A> .
    match t with
      trie_none _ => (trie_exact A s a)
    | trie_exact _ s' a' =>
  
      %- insert (s',a') into a new blank trie_next, then
         insert (s,a) into the result. -%

      let cookie = Z in
      let v = (qcharray_new <trie A> nat cookie
                 fun(^#owned cookie:nat) : #unique <trie A>.
                     (trie_none A)) in
      do 
        (dec nat cookie)
        (trie_insert A s a
        (trie_insert A s' a' (trie_next A (nothing A) v)))
      end
    | trie_next _ o l' => 
        match s with
          unil _ => do (dec <option A> o) 
                      (trie_next A (something A a) l')
                   end
        | ucons _ c s' => 
          match (qcharray_out <trie A> c stringn l' join (string_mem c stringn) ff) with
            mk_qcharray_mod _ a' _ _ l'' =>
              let r = (trie_insert A s' a a') in 
                (trie_next A o 
                   (qcharray_in1 <trie A> c r l''))
          end
        end
    end.
          
Define trie_remove : Fun(spec A:type)(^#owned s:string)(#unique t:<trie A>).
                         #unique <trie A> :=
  fun trie_remove(spec A:type)(^#owned s:string)(#unique t:<trie A>) : #unique <trie A>.
    match t with
      trie_none _ => (trie_none A)
    | trie_exact A' s' a' =>
        match (stringeq s s') with
          ff => (trie_exact A' s' a')
        | tt => do (dec A' a')
                   (dec string s')
                   (trie_none A)
                end
        end
    | trie_next A' o l' => 
        match s with
          unil _ => do (dec <option A> o) 
                      (trie_next A' (nothing A) l')
                   end
        | ucons _ c s' => 
          match (qcharray_out <trie A> c stringn l' join (string_mem c stringn) ff) with
            mk_qcharray_mod _ a' _ _ l'' =>
              let r = (trie_remove A s' a') in 
                (trie_next A' o 
                   (qcharray_in1 <trie A> c r l''))
          end
        end
    end.

Define trie_lookup : Fun(A:type)(^#unique_owned t:<trie A>)(owned s:string).
                        <option A> :=
  fun trie_lookup(A:type)(unique_owned t:<trie A>)(owned s:string)
      : <option A> .
    match t with
      trie_none A' => (nothing A)
    | trie_exact A' s' a' => 
        match (stringeq s s') with
          ff => (nothing A)
        | tt => (something A 
                   cast inc a' by symm inj <trie *> t_Eq)
        end
    | trie_next A' o' l' =>
      abbrev P = symm inj <trie *> t_Eq in
      abbrev cl' = cast l' by cong <charvec <trie *>> P in
        match s with
          nil B => inc cast o' by cong <option *> P
        | cons B b s' => 
          abbrev PB = symm inj <list *> s_Eq in
          abbrev cb = cast b by PB in
          abbrev ss = cast s' by cong <list *> PB in
          (trievec_get A cl' cb <trie_lookup_i A> <option A> 
            (mk_trie_lookup_i A trie_lookup inc ss)
            (trie_lookup_h A))
        end
     end.

Inductive trie_interp_i1 : Fun(A:type).type :=
  mk_trie_interp_i1 : Fun(A:type)
                        (c:char).
                        <trie_interp_i1 A>.

Define trie_interp_h1 :=
  fun(spec A':type)
     (owned cookie:<trie_interp_i1 A'>)(owned p:<pair string A'>).
    match cookie with
     mk_trie_interp_i1 A'' c =>
       match p with
       mkpair p1T p2T p1 p2 =>
        abbrev PA'' = inj <trie_interp_i1 *> cookie_Eq in
        abbrev s = cast p1 by symm inj <pair * **> p_Eq in
        abbrev a = cast p2 
                   by trans symm inj <pair ** *> p_Eq  
                            PA'' in
        cast (mkpair string A'' (stringc c inc s) inc a)
        by symm cong <pair string *> PA''
      end
    end.

Inductive trie_interp_i2 : Fun(A:type).type :=
  mk_trie_interp_i2 : Fun(A:type)
                         (r:Fun(A:type)(unique_owned t:<trie A>).
                               <list <pair string A>>).
                         <trie_interp_i2 A>.

Define trie_interp_h2 :=
  fun(spec A:type)(owned cookie:<trie_interp_i2 A>)(c:char)
     (unique_owned t:<trie A>)(p:<list <pair string A>>).
    match cookie with
      mk_trie_interp_i2 A' r =>
        abbrev T' = <pair string A'> in
        abbrev PA = inj <trie_interp_i2 *> cookie_Eq in
        let i = (r A' cast t by cong <trie *> PA) in
        let cookie = (mk_trie_interp_i1 A' c) in
        let tmp = (map T' T' <trie_interp_i1 A'> cookie 
                    (trie_interp_h1 A') i) in
        dec cookie dec i 
        let ret = 
        cast 
         (append T' tmp
          cast p by cong <list <pair string *>> PA)
        by cong <list <pair string *>> symm PA in
        dec tmp ret
    end.

Define trie_interp_h2_sztot
  : Forall(A:type)
          (l:<charvec <trie A>>)
          (r:Fun(A:type)(t:<trie A>).
               <list <pair string A>>)
          (rTot: Forall(A:type)(t:<trie A>)(st:{(lt size t size l) = tt}).
                   Exists(l:<list <pair string A>>).
                     { (r t) = l })
          (c:char)
          (a:<trie A>)
          (u:{ (lt size a size l) = tt})
          (b:<list <pair string A>>).
      Exists(l:<list <pair string A>>).
        {(trie_interp_h2 (mk_trie_interp_i2 r) c a b) = l} :=
  foralli(A:type)
         (l:<charvec <trie A>>)
         (r:Fun(A:type)(t:<trie A>). <list <pair string A>>)
         (rTot: Forall(A:type)(t:<trie A>)(st:{(lt size t size l) = tt}).
                  Exists(l:<list <pair string A>>).
                    { (r t) = l })
         (c:char)
         (a:<trie A>)
         (u:{ (lt size a size l) = tt})
         (b:<list <pair string A>>). 
  abbrev T = <pair string A> in
  existse [map_total T T <trie_interp_i1 A> (mk_trie_interp_i1 A c)
           (trie_interp_h1 A)
           foralli(a:<pair string A>).
             case a with
               mkpair A' B' a' b' =>
                 existsi (mkpair string A 
                           (stringc c cast a' by symm inj <pair * **> a_Eq)
                           cast b' by symm inj <pair ** *> a_Eq)
                   { (trie_interp_h1 (mk_trie_interp_i1 c) a) = * }
                   hypjoin (trie_interp_h1 (mk_trie_interp_i1 c) a)
                      (mkpair (stringc c a') b')
                   by a_eq end
             end
           terminates (r A a) by [rTot A a u]] 
  foralli(l2 : <list <pair string A>>)
         (ul2: { (map (mk_trie_interp_i1 c) trie_interp_h1 (r a)) = l2 }).
    existsi terminates (append T l2 b) by appendTot
      { (trie_interp_h2 (mk_trie_interp_i2 r) c a b) = * }
       hypjoin (trie_interp_h2 (mk_trie_interp_i2 r) c a b)
               (append l2 b)
       by ul2 end.
    
Define trie_interp_h2_tot
  : Forall(A:type)
          (r:Fun(A:type)(t:<trie A>). <list <pair string A>>)
          (rTot: Forall(A:type)(t:<trie A>).
                   Exists(l:<list <pair string A>>). { (r t) = l })
          (c:char)
          (a:<trie A>)
          (b:<list <pair string A>>).
      Exists(l:<list <pair string A>>).
        {(trie_interp_h2 (mk_trie_interp_i2 r) c a b) = l} :=
  foralli(A:type)
         (r:Fun(A:type)(t:<trie A>). <list <pair string A>>)
         (rTot: Forall(A:type)(t:<trie A>).
                  Exists(l:<list <pair string A>>). { (r t) = l })
         (c:char)
         (a:<trie A>)
         (b:<list <pair string A>>).
   abbrev l = terminates (mkvec <trie A> a num_chars) by mkvec_tot in
   case num_chars with
     Z => contra
            trans symm num_chars_eq num_chars_not_Z
          Exists(l:<list <pair string A>>).
           {(trie_interp_h2 (mk_trie_interp_i2 r) c a b) = l} 
   | S n' =>
     [trie_interp_h2_sztot A l r 
        foralli(A:type)(t:<trie A>)(st:{(lt size t size l) = tt}).
          [rTot A t]
        c a trans cong (lt size a size (mkvec a *))
                    num_chars_eq
                  [mkvec_sz <trie A> a n']
        b]
   end.
    
Define trie_interp :=
  fun trie_interp(A:type)(unique_owned t:<trie A>) : <list <pair string A>> .
  abbrev T = <pair string A> in
    match t with
      trie_none A' => (nil T)
    | trie_exact A' s' a' => 
        (cons T (mkpair string A inc s' 
                   inc cast a' by symm inj <trie *> t_Eq)
           (nil T))
    | trie_next A' o' l' => 
        abbrev P = symm inj <trie *> t_Eq in
        abbrev o = cast o' by cong <option *> P in
        abbrev l = cast l' by cong <charvec <trie *>> P in
        let cookie = (mk_trie_interp_i2 A trie_interp) in
        let S = 
           (cvfold <trie A> <list T> <trie_interp_i2 A> l
              cookie (trie_interp_h2 A) (nil T)) in
        dec cookie
        match o with
          nothing A' => S
        | something A' a' => 
           abbrev P2 = symm inj <option *> o_Eq in
           (cons T (mkpair string A (nil char) inc cast a' by P2) S)
        end          
    end.

%Set "debug_eval".

Define trie_interp_tot : Forall(A:type)(t:<trie A>).
                          Exists(l:<list <pair string A>>).
                           { (trie_interp t) = l } :=
  foralli(A:type)(t:<trie A>).
  [induction(n:nat) 
    return Forall(A:type)(t:<trie A>)(u:{ (le size t n) = tt }).
             Exists(l:<list <pair string A>>).
               { (trie_interp t) = l }
    with
      Z =>
      foralli(A:type)(t:<trie A>)(u:{ (le size t n) = tt }).
        abbrev T = <pair string A> in
        abbrev P = [le_Z1 size t trans cong (le size t *) symm n_eq u] in
        abbrev F = Exists(l:<list T>).{ (trie_interp t) = l } in
          case t with
            trie_none A' => 
              contra
                trans trans hypjoin (S Z) size t by t_eq end 
                      P
                      clash Z (S Z)
              F
          | trie_exact A' s a' => 
              contra
                trans trans hypjoin (S (plus size s size a'))
                                    size t by t_eq end 
                      P
                      clash Z (S terminates (plus size s size a') 
                                 by plus_total)
              F
          | trie_next A' o' l' =>
              contra
                trans trans hypjoin (S (plus size o' size l'))
                                    size t by t_eq end 
                      P
                      clash Z (S terminates (plus size o' size l') 
                                 by plus_total)
              F
          end
    | S n' => 
      foralli(A:type)(t:<trie A>)(u:{ (le size t n) = tt }).
        abbrev T = <pair string A> in
        case t with
          trie_none A' => 
            existsi (nil T) { (trie_interp t) = * }
              hypjoin (trie_interp t) nil by t_eq end
        | trie_exact A' s' a' => 
          abbrev r = (cons T
                       (mkpair string A s' cast a' by symm inj <trie *> t_Eq)
                       (nil T)) in
            existsi r
              { (trie_interp t) = * }
              hypjoin (trie_interp t) r by t_eq end
        | trie_next A' o' l' => 
          abbrev P = symm inj <trie *> t_Eq in
          abbrev o = cast o' by cong <option *> P in
          abbrev l = cast l' by cong <charvec <trie *>> P in
          abbrev cookie = (mk_trie_interp_i2 A trie_interp) in
          existse 
            [cvfold_sztot <trie A> <list T> <trie_interp_i2 A> l cookie
               (trie_interp_h2 A) 
               [trie_interp_h2_sztot A l trie_interp
                 foralli(A:type)(t1:<trie A>)(st:{(lt size t1 size l) = tt}).
                   [n_IH n' A t1 
                     [lt_implies_le size t1 n'
                     [ltle_trans size t1 size l n'
                        st 
                        [lt_pred n' (S n') size l' join (S n') (S n')
                           trans cong (lt size l' *) symm n_eq
                             [ltle_trans size l' size t n
                               trans cong (lt size l' *)
                                       hypjoin size t
                                              (S (plus size o' size l'))
                                       by t_eq end
                                 [lt_Splus2 size o' size l']
                               u]]]]]]
                 (nil T)]
          abbrev cS = (cvfold l cookie trie_interp_h2 nil) in
          foralli(l:<list <pair string A>>)
                 (ul:{ cS = l}).
          abbrev P1 = 
             trans cong (trie_interp *) t_eq
             trans evalto (trie_interp (trie_next o' l')) 
                     let S = cS in 
                       match o with nothing => S
                         | something a' => (cons (mkpair nil a') S)
                       end
                cong let S = * in 
                       match o with nothing => S
                         | something a' => (cons (mkpair nil a') S)
                       end
                  ul in
          case o with
            nothing A' => 
              existsi l { (trie_interp t) = * }
                trans P1 
                trans cong let S = l in 
                             match * with nothing => S
                               | something a' => (cons (mkpair nil a') S)
                             end
                        o_eq
                   join let S = l in 
                          match nothing with nothing => S
                           | something a' => (cons (mkpair nil a') S)
                          end
                        l
          | something A' a' => 
              existsi (cons T (mkpair string A (nil char) 
                                 cast a' by symm inj <option *> o_Eq) l)
                { (trie_interp t) = * }
                trans P1 
                trans cong let S = l in 
                             match * with nothing => S
                               | something a' => (cons (mkpair nil a') S)
                             end
                        o_eq
                  join let S = l in 
                          match (something a') with nothing => S
                           | something a' => (cons (mkpair nil a') S)
                          end
                        (cons (mkpair nil a') l)
          end
        end
    end
   size t A t [x_le_x size t]].

Total trie_interp trie_interp_tot.

%- Now that we have termination of trie_interp, we can get a much more
   convenient lemma for dealing with the call to cvfold inside trie_interp. -%
Define trie_interp_charvec_tot :
  Forall(A:type)(l:<charvec <trie A>>).
   Exists(r:<list <pair string A>>).
    {  (cvfold l (mk_trie_interp_i2 trie_interp) trie_interp_h2 nil) = r } :=
  foralli(A:type)(l:<charvec <trie A>>).
    [cvfold_sztot <trie A> <list <pair string A>> <trie_interp_i2 A>
       l (mk_trie_interp_i2 A trie_interp) 
       (trie_interp_h2 A)
       [trie_interp_h2_sztot A l trie_interp
        foralli(A:type)(t:<trie A>)(st:{(lt size t size l) = tt}).
          [trie_interp_tot A t]]
       (nil <pair string A>)].

Define trie_lookup_interp_charvec :
  Forall(A:type)
        (l:<charvec <trie A>>)
        (t:<trie A>)
        (c:char)
        (s:string)
        (a:A)
        (l1 l2:<list <pair string A>>)
        (u1: { (trie_interp t) = (append l1 (cons (mkpair s a) l2))})
        (u2: { (vec_get l (which_char c)) = t}).
   Exists(L1 L2:<list <pair string A>>).
     { (cvfold_h l Cc0 (mk_trie_interp_i2 trie_interp) trie_interp_h2 nil) =
         (append L1 (cons (mkpair (stringc c s) a) L2)) } :=
  foralli(A:type)
         (l:<charvec <trie A>>)
         (t:<trie A>)
         (c:char)
         (s:string)
         (a:A)
         (l1 l2:<list <pair string A>>)
         (u1: { (trie_interp t) = (append l1 (cons (mkpair s a) l2))})
         (u2: { (vec_get l (which_char c)) = t}).        
  abbrev tCc0 = terminates (which_char Cc0) by to_nat_tot in
  abbrev tnc = terminates (which_char c) by to_nat_tot in
  abbrev T = <pair string A> in
  abbrev cvcookie = (mk_trie_interp_i2 trie_interp) in
  abbrev p = (mkpair string A (stringc c s) a) in
  [induction(n:nat) 
    return Forall(start:char)
                 (m:{(minus (which_char c) (which_char start)) = n}).
            Exists(L1 L2:<list T>).
              { (cvfold_h l start
                   (mk_trie_interp_i2 trie_interp) trie_interp_h2 nil) =
                 (append L1 (cons (mkpair (stringc c s) a) L2)) } with
      Z => 
      foralli(start:char)
             (m:{(minus (which_char c) (which_char start)) = n}).
      abbrev tstart = terminates (which_char start) by to_nat_tot in
      abbrev start' = terminates (char_inc start) by char_inc_tot in
      abbrev start_eq = [minus_which_char_Z c start trans m n_eq] in
      abbrev cookie = (mk_trie_interp_i1 A c) in
      abbrev M1 = terminates
                    (map T T <trie_interp_i1 A> cookie (trie_interp_h1 A)
                       l1)
                  by map_total in
      abbrev M2 = terminates
                    (map T T <trie_interp_i1 A> cookie (trie_interp_h1 A)
                       l2)
                  by map_total in
      abbrev li = (cons T (mkpair string A s a) l2) in
      abbrev lic = (cons T (mkpair string A (stringc c s) a) M2) in
      abbrev ma = [map_append T T
                     <trie_interp_i1 A> cookie (trie_interp_h1 A) 
                     l1 li] in
        case start' with
          mk_char_inc_t next carry =>
          case carry with
            ff =>
            existse [cvfold_h_tot 
                      <trie A> <list T> <trie_interp_i2 A> l
                      next (mk_trie_interp_i2 A trie_interp)
                     (trie_interp_h2 A) 
                     [trie_interp_h2_tot A trie_interp trie_interp_tot]
                     (nil T)]
            foralli(r:<list T>)
                   (ur:{ (cvfold_h l next cvcookie trie_interp_h2 nil) = r}).
            abbrev lic = (cons T p M2) in
            existsi M1 
               Exists(L2:<list T>).
                 { (cvfold_h l start cvcookie trie_interp_h2 nil) =
                   (append * (cons p L2)) }
            existsi terminates (append T M2 r) by appendTot
                 { (cvfold_h l start cvcookie trie_interp_h2 nil) =
                   (append M1 (cons p *)) }

            trans hypjoin (cvfold_h l start cvcookie
                            trie_interp_h2 nil)
                          (append (map cookie trie_interp_h1 (trie_interp t))
                             r)
                  by carry_eq start'_eq u2 ur start_eq end
            trans cong (append (map cookie trie_interp_h1 *) r) u1
            trans cong (append * r) ma
            trans cong (append (append M1 *) r)
                    join (map cookie trie_interp_h1 li) lic
            trans [append_assoc T M1 lic r]
                  join
                   (append M1 (append lic r))
                   (append M1 (cons p (append M2 r)))
            | tt => 
              existsi M1 
                 Exists(L2:<list T>).
                   { (cvfold_h l start cvcookie trie_interp_h2 nil) =
                     (append * (cons p L2)) }
              existsi M2
                   { (cvfold_h l start cvcookie trie_interp_h2 nil) =
                     (append M1 (cons p *)) }

              trans hypjoin (cvfold_h l start cvcookie trie_interp_h2 nil)
                            (append (map cookie trie_interp_h1 (trie_interp t))
                              nil)
                    by carry_eq start'_eq u2 start_eq end
              trans cong (append (map cookie trie_interp_h1
                                  *) nil)
                    u1
              trans cong (append * nil) ma
              trans cong (append (append M1 *) nil)
                      join (map cookie trie_interp_h1 li) lic
                    [append_nil T 
                       terminates (append T M1 lic) by appendTot]
            end
      end
   | S n' => 
     foralli(start:char)
            (m:{(minus (which_char c) (which_char start)) = n}).
     abbrev tstart = terminates (which_char start) by to_nat_tot in
     abbrev r = terminates (char_inc start) by char_inc_tot in
     abbrev ltstartc = [minus_S_lt tnc tstart n' trans m n_eq] in
       case r with
         mk_char_inc_t next carry =>
         abbrev cookie = (mk_trie_interp_i1 A start) in
         abbrev carry_ff = [char_inc_notfull start next carry
                              [ltle_trans tstart tnc 
                                 terminates (which_char CLast) by to_nat_tot
                                 ltstartc
                                 [chars_bounded2 c]]
                              r_eq] in
         abbrev tnext = terminates (which_char next) by to_nat_tot in
           existse [vec_get_tot <trie A> num_chars l tstart
                      [chars_bounded start]]
           foralli(t2:<trie A>)
                  (ut2:{(vec_get l tstart) = t2}).
           abbrev U = terminates 
                        (map T T <trie_interp_i1 A>
                            cookie (trie_interp_h1 A)
                              (trie_interp A t2))
                      by map_total in
             existse
               [n_IH n' next 
                 [minus_char_inc c start next n' carry trans m n_eq r_eq]]
             foralli(L1 L2:<list T>)
                    (q:{ (cvfold_h l next cvcookie trie_interp_h2 nil) =
                           (append L1 (cons p L2)) }).
             existsi terminates (append T U L1) by appendTot
                Exists(L2:<list T>).
                   { (cvfold_h l start cvcookie trie_interp_h2 nil) =
                     (append * (cons p L2)) }
             existsi L2
                { (cvfold_h l start cvcookie trie_interp_h2 nil) =
                  (append (append U L1) (cons p *)) }
               trans hypjoin (cvfold_h l start cvcookie trie_interp_h2 nil)
                             (append U
                                 (cvfold_h l next cvcookie trie_interp_h2 nil))
                     by carry_ff r_eq ut2 end
               trans cong (append U *) q
                 symm [append_assoc T U L1 (cons T p L2)]
       end
                           
   end tnc Cc0 trans cong (minus (which_char c) *) 
                       join (which_char Cc0) Z
                     [minusZ tnc] ].


Define trie_lookup_interp :
  Forall(A:type)(t:<trie A>)(s:string)(a:A)
        (u:{ (trie_lookup t s) = (something a) }).
        Exists(l1 l2:<list <pair string A>>).
        { (trie_interp t) = (append l1 (cons (mkpair s a) l2)) } :=
  foralli(A:type)(t:<trie A>)(s:string)(a:A)
         (u:{ (trie_lookup t s) = (something a) }). 
  abbrev T = <pair string A> in
  abbrev case_none = 
    foralli(s:string)
           (t:<trie A>)
           (u1 : { t = trie_none})
           (u:{ (trie_lookup t s) = (something a) }). 
    abbrev F = Exists(l1 l2:<list <pair string A>>).
                 { (trie_interp t) = (append l1 (cons (mkpair s a) l2)) } in
     contra
        trans
         trans hypjoin nothing (trie_lookup t s) by u1 end
               u 
         clash (something a) nothing
        F
  in
  abbrev case_exact =
   foralli(s:string)
          (t:<trie A>)
          (s':string)
          (a a':A)
          (u1 : { t = (trie_exact s' a')})
          (u2 : {(trie_lookup t s) = (something a)}).
    abbrev F = Exists(l1 l2:<list <pair string A>>).
                 { (trie_interp t) = (append l1 (cons (mkpair s a) l2)) } in
    abbrev iseq = terminates (stringeq s s') 
                  by [stringeqTot s s'] in
     case iseq with
       ff => 
         contra
           trans
            trans hypjoin nothing (trie_lookup t s) by u1 iseq_eq end
                  u2 
           clash (something a) nothing 
         F
     | tt => existsi (nil <pair string A>)
             Exists(l2:<list <pair string A>>).
               { (trie_interp t) = (append * (cons (mkpair s a) l2)) }
             existsi (nil <pair string A>)
               { (trie_interp t) = (append nil (cons (mkpair s a) *))}
             hypjoin (trie_interp t) 
                     (append nil (cons (mkpair s a) nil))
             by u1 iseq_eq [stringeqEq s s' iseq_eq]
               inj (something *) hypjoin (something a) 
                                         (something a')
                                 by u1 u2 iseq_eq end 
             end
     end in
    [induction(s:string)
       return Forall(t:<trie A>)
                    (u:{ (trie_lookup t s) = (something a) }). 
               Exists(l1 l2:<list <pair string A>>).
                 { (trie_interp t) = (append l1 (cons (mkpair s a) l2)) }
     with
     nil B => 
       foralli(t:<trie A>)
              (u:{ (trie_lookup t s) = (something a) }). 
         case t with
           trie_none A' => 
             [case_none s t t_eq u]
         | trie_exact A' s' a' => 
             [case_exact s t s' a cast a' by symm inj <trie *> t_Eq t_eq u]
         | trie_next A' o' l' => 
           abbrev F = Exists(l1 l2:<list <pair string A>>).
                       { (trie_interp t) = 
                            (append l1 (cons (mkpair s a) l2)) } in
           abbrev P = symm inj <trie *> t_Eq in
           abbrev o = cast o' by cong <option *> P in
           abbrev l = cast l' by cong <charvec <trie *>> P in
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
         end
   | cons B b s2' => 
     abbrev P = symm inj <list *> s_Eq in
     abbrev c = cast b by P in
     abbrev s2 = cast s2' by symm s_Eq in
     abbrev tnc = terminates (which_char c) by to_nat_tot in
     foralli(t:<trie A>)
            (u:{ (trie_lookup t s) = (something a) }). 
       case t with
         trie_none A' => 
           [case_none s t t_eq u]
       | trie_exact A' s' a' => 
           [case_exact s t s' a cast a' by symm inj <trie *> t_Eq t_eq u]
       | trie_next A' o' l' => 
         abbrev P2 = symm inj <trie *> t_Eq in
         abbrev o = cast o' by cong <option *> P2 in
         abbrev l = cast l' by cong <charvec <trie *>> P2 in
         existse [vec_get_tot <trie A> num_chars l tnc 
                   [chars_bounded c]]
         foralli(t2:<trie A>)
                (ut2:{(vec_get l' tnc) = t2}).
         existse
           [s_IH s2 t2
             symm
             trans symm u
             trans hypjoin (trie_lookup t s) 
                           (trie_lookup (vec_get l tnc) s2)
                   by t_eq s_eq end
              cong (trie_lookup * s2)
                ut2]
           foralli(l1 l2 : <list <pair string A>>)
                  (us2:{(trie_interp t2) = 
                           (append l1 (cons (mkpair s2 a) l2))}).
           abbrev cS = (cvfold_h l' Cc0 (mk_trie_interp_i2 trie_interp)
                          trie_interp_h2 nil) in
             existse
               [trie_lookup_interp_charvec 
                  A l t2 c s2 a l1 l2 us2 ut2]
               foralli(L1 L2 : <list <pair string A>>)
                      (R:{cS = 
                           (append L1 (cons (mkpair (stringc b s2') a) L2)) }).
               abbrev R2 = trans R
                             cong (append L1 (cons (mkpair * a) L2)) 
                               symm s_eq in
               case o with
                 nothing A' =>
                 existsi L1
                   Exists(l2:<list T>).
                     { (trie_interp t) = (append * (cons (mkpair s a) l2))}
                 existsi L2
                      { (trie_interp t) = (append L1 (cons (mkpair s a) *))} 
                   trans cong (trie_interp *)
                          t_eq
                   trans evalto (trie_interp (trie_next o' l'))
                         let S = cS in
                           match o with
                             nothing => S
                           | something a' => (cons (mkpair nil a') S)
                           end
                   trans cong let S = cS in
                             match * with
                               nothing => S
                             | something a' => (cons (mkpair nil a') S)
                             end
                           o_eq
                   trans cong let S = * in
                            match nothing with
                              nothing => S
                            | something a' => (cons (mkpair nil a') S)
                            end
                           R2
                    join let S = (append L1 (cons (mkpair s a) L2)) in
                           match nothing with
                             nothing => S
                           | something a' => (cons (mkpair nil a') S)
                           end
                         (append L1 (cons (mkpair s a) L2))
               | something A' a' => 
                 existsi (cons T (mkpair string A stringn
                                     cast a' by symm inj <option *> o_Eq) L1)
                   Exists(l2:<list T>).
                     { (trie_interp t) = (append * (cons (mkpair s a) l2))}
                 existsi L2
                     { (trie_interp t) = (append (cons (mkpair stringn a') L1)
                                           (cons (mkpair s a) *))} 
                   trans cong (trie_interp *)
                          t_eq
                   trans evalto (trie_interp (trie_next o' l'))
                         let S = cS in
                           match o with
                             nothing => S
                           | something a' => (cons (mkpair nil a') S)
                           end
                   trans cong let S = cS in
                             match * with
                               nothing => S
                             | something a' => (cons (mkpair nil a') S)
                             end
                           o_eq
                   trans cong let S = * in
                            match (something a') with
                              nothing => S
                            | something a' => (cons (mkpair nil a') S)
                            end
                           R2
                    join let S = (append L1 (cons (mkpair s a) L2)) in
                           match (something a') with
                             nothing => S
                           | something a' => (cons (mkpair nil a') S)
                           end
                         (append (cons (mkpair nil a') L1)
                            (cons (mkpair s a) L2))
               end
       end
   end
   s t u].

Define trusted trie_insert_interp :
  Forall(A:type)(t t':<trie A>)(s:string)(a:A)
        (u:{ (trie_insert s a t) = t'}).
    Exists(l1 l2:<list <pair string A>>).
       { (trie_interp t') = (append l1 (cons (mkpair s a) l2)) } := truei.

Define trusted trie_insert_lookup_interp :
  Forall(A:type)(ta tb t':<trie A>)(s:string)(a a':A)
        (u1:{ (trie_lookup ta s) = (something a')})
        (u2:{ (trie_interp ta) = (trie_interp tb)})
        (u3:{ (trie_insert s a tb) = t'})
        (l1 l2:<list <pair string A>>)
        (u:{ (trie_interp t') = (append l1 (cons (mkpair s a) l2)) }).
     { (trie_interp ta) = (append l1 (cons (mkpair s a') l2)) } := truei.

Define trusted trie_restore_interp :
  Forall(A:type)(t t'a t'b t'':<trie A>)(s:string)(a a':A)
        (u1:{ (trie_lookup t s) = (something a)})
        (u2:{ (trie_insert s a' t) = t'a})
        (u3:{ (trie_interp t'a) = (trie_interp t'b)})
        (u4:{ (trie_insert s a t'b) = t''}).
     { (trie_interp t) = (trie_interp t'') } := truei.

Define trusted trie_insert_new :
  Forall(A:type)(t t':<trie A>)(s:string)(a:A)
        (u1:{ (trie_lookup t s) = nothing})
        (u2:{ (trie_insert s a t) = t'})
        (l1 l2:<list <pair string A>>)
        (u : { (trie_interp t') = (append l1 (cons (mkpair s a) l2)) }).
       { (trie_interp t) = (append l1 l2) } := truei.

Define trie_insert_overwrite :
  Forall(A:type)(t t':<trie A>)(s:string)(a a':A)
        (u1:{ (trie_lookup t s) = (something a') })
        (u2:{ (trie_insert s a t) = t'})
        (l1 l2:<list <pair string A>>)
        (u : { (trie_interp t') = (append l1 (cons (mkpair s a) l2)) }).
       { (trie_interp t) = (append l1 (cons (mkpair s a') l2)) } := 
 foralli(A:type)(t t':<trie A>)(s:string)(a a':A)
        (u1:{ (trie_lookup t s) = (something a') })
        (u2:{ (trie_insert s a t) = t'})
        (l1 l2:<list <pair string A>>)
        (u : { (trie_interp t') = (append l1 (cons (mkpair s a) l2)) }).
  [trie_insert_lookup_interp A t t t' s a a' u1 refl (trie_interp t) u2 l1 l2 u].

Define trusted trie_remove_interp :
  Forall(A:type)(t t':<trie A>)(s:string)(a:A)
        (u:{ (trie_remove s t) = t'})
        (l1 l2:<list <pair string A>>)
        (u : { (trie_interp t) = (append l1 (cons (mkpair s a) l2)) }).
       { (trie_interp t') = (append l1 l2) } := truei.

Define trusted trie_lookup_same_interp :
  Forall(A:type)(t t':<trie A>)(s:string)(o:<option A>)
        (u1:{ (trie_lookup t s) = o})
        (u2:{ (trie_interp t) = (trie_interp t') }).
    { (trie_lookup t' s) = o} := truei.

Define trie_range :=
  fun(A:type)(unique_owned t:<trie A>) : <list A> .
    (map <pair string A> A Unit unit fun(u:Unit).(snd string A) 
       (trie_interp A t)).

% the map function used in trie_range is total.
Define trie_range_map_tot 
  : Forall(A:type)(l1:<list <pair string A>>).
    Exists(l2:<list A>).
     { (map <pair string A> A Unit unit fun(u:Unit).(snd string A) l1) = l2 } :=
   foralli(A:type).
   abbrev hf = fun(u:Unit).(snd string A) in
   [map_total <pair string A> A
     Unit unit hf
     foralli(a : <pair string A>).
       existsi terminates (snd string A a)
               by [sndTot string A]
       { (hf unit a) = *}
          join (hf unit a) (snd a)].

Define trie_range_tot
 : Forall(A:type)(t:<trie A>).
   Exists(l:<list A>). { (trie_range t) = l} := 
   foralli(A:type)(t:<trie A>).
   abbrev ret = 
     terminates (map <pair string A> A Unit unit fun(u:Unit).(snd string A) 
                 (trie_interp A t)) 
     by trie_range_map_tot in
   existsi ret { (trie_range t) = *}
     join (trie_range t) ret.

Define trie_interp_range1
 : Forall(A:type)(t1 t2:<trie A>)
         (u1:{ (trie_interp t1) = (trie_interp t2)}).
       { (trie_range t1) = (trie_range t2) } :=
  foralli(A:type)(t1 t2:<trie A>)
         (u1:{ (trie_interp t1) = (trie_interp t2)}).
  hypjoin (trie_range t1) (trie_range t2)
  by u1 end.

Define trie_interp_range2 :
  Forall(A:type)(t:<trie A>)(s:string)(a:A)
        (l1 l2:<list <pair string A>>)
        (u:{ (trie_interp t) = (append l1 (cons (mkpair s a) l2)) }).
        { (trie_range t) = (append (map unit fun(u:Unit).snd l1)
                              (cons a (map unit fun(u:Unit).snd l2))) } :=
  foralli(A:type)(t:<trie A>)(s:string)(a:A)
         (l1 l2:<list <pair string A>>)
         (u:{ (trie_interp t) = (append l1 (cons (mkpair s a) l2)) }).
  abbrev T = <pair string A> in
  abbrev L1 = terminates (map T A Unit unit fun(u:Unit).(snd string A) l1)
              by [map_total string A l1 snd sndTot] in
  abbrev L2 = terminates (map T A Unit unit fun(u:Unit).(snd string A) l2)
              by [map_total string A l2 snd sndTot] in
        trans join (trie_range t) (map unit fun(u).snd (trie_interp t))
        trans cong (map unit fun(u).snd *) u
        trans [map_append T A Unit unit fun(u:Unit).(snd string A)
                  l1 (cons T (mkpair string A s a) l2)]
              cong (append (map unit fun(u).snd l1) *)
                join (map unit fun(u).snd (cons (mkpair s a) l2))
                     (cons a (map unit fun(u).snd l2)).
