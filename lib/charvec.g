Include "char.g".
Include "list.g".
Include "unit.g".
Include "minus.g".

%Set "print_parsed".

Define spec type_family_abbrev charvec := fun(A:type).<vec A num_chars>.

Define spec mk_charvec := 
  fun (A:type)(a:A):unique <charvec A>.
    (mkvec A a num_chars).

Define spec cvget := 
  fun(A:type)(unique_owned l:<charvec A>)(c:char) : A. 
    (vec_get A num_chars l (which_char c) [chars_bounded c]).

Define spec cvupdate := 
  fun(A:type)(c:char)(a:A)(unique l:<charvec A>)
   : unique <charvec A>.
   (vec_update A num_chars l (which_char c) a [chars_bounded c]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% unique char-indexed arrays
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Define spec mk_ucharvec := 
  fun (A B:type)(owned b:B)(f:Fun(owned b:B).unique A)
      :unique <charvec A>.
    (mkvec A (f b) num_chars).

Define spec ucvupdate := 
  fun(A:type)(c:char)(unique a:A)(unique l:<charvec A>)
   : unique <charvec A>.
   (vec_update A num_chars l (which_char c) a [chars_bounded c]).

Define spec ucvget :=
  fun(A:type)(unique_owned l:<charvec A>)(c:char)(B C : type)
     (b:B)(f:Fun(b:B)(unique_owned a:A).C) : C. 
    (f b (vec_get A num_chars l (which_char c) [chars_bounded c])).

Inductive ucvmod_t : Fun(A:type).type :=
  mk_ucvmod_t : Fun(A:type)(unique a:A)(B:type)(unique b:B)
                   (f:Fun(unique b:B)(unique a:A).
                         unique <charvec A>).
                <ucvmod_t A>.

Inductive ucvmod_t2 : Fun(A:type)(c:char).type :=
  mk_ucvmod_t2 : Fun(A:type)(unique l : <charvec A>)(c:char).
                    <ucvmod_t2 A c>.

Define spec ucvmod :=
  fun(A:type)(unique l:<charvec A>)(c:char) : unique <ucvmod_t A>. 
    (mk_ucvmod_t A 
       (vec_get A num_chars l (which_char c) [chars_bounded c])
       <ucvmod_t2 A c>
       (mk_ucvmod_t2 A l c)
       fun ucvmod_reassemble(unique m:<ucvmod_t2 A c>)(unique a:A)
                        : unique <charvec A>.
         match m with
           mk_ucvmod_t2 A' l' c' =>
             abbrev PA' = symm inj <ucvmod_t2 * **> m_Eq in
             (vec_update A num_chars cast l' by cong <vec * num_chars> PA'
                (which_char c') a [chars_bounded c'])
         end).

Inductive cvfold_i : Fun(A B:type).type :=
  mk_cvfold_i : Fun(A B C:type)(unique_owned l:<charvec A>)
                   (start next : char)
                   (fcookie:C)
                   (f:Fun(owned fcookie:C)(c:char)(unique_owned a:A)(b:B).B)
                   (b:B)
                   (r:Fun(A B C:type)(unique_owned l:<charvec A>)
                         (start : char)
                         (owned fcookie:C)
                         (f:Fun(owned fcookie:C)
                               (c:char)(unique_owned a:A)(b:B).B)
                         (b:B).B). <cvfold_i A B>.

Define cvfold_h :=
  fun cvfold_h(A B C:type)(unique_owned l:<charvec A>)
              (start : char)
              (owned fcookie:C)
              (f:Fun(owned fcookie:C)(c:char)(unique_owned a:A)(b:B).B)
              (b:B):B.
    match (char_inc start) with
      mk_char_inc_t next wrapped =>
        let cookie = 
              match wrapped with
                ff => (mk_cvfold_i A B C l start next inc fcookie f b cvfold_h)
              | tt => (mk_cvfold_i A B C l start next inc fcookie f b 
                         fun(A B C:type)(unique_owned l:<charvec A>)
                            (start : char)
                            (owned fcookie:C)
                            (f:Fun(owned fcookie:C)(c:char)
                                  (unique_owned a:A)(b:B).B)
                            (b:B). b)
                     end in
          (ucvget A l start <cvfold_i A B> B
            cookie
            fun(cookie: <cvfold_i A B>)(unique_owned a:A).
              match cookie with
                mk_cvfold_i A' B' C' l' start' next' fcookie' f' b' r =>
                  abbrev ca = cast a by inj <cvfold_i * **> cookie_Eq in
                  let ret = 
                    cast (f' fcookie' start' ca 
                           (r A' B' C' l' next' fcookie' f' b')) 
                    by symm inj <cvfold_i ** *> cookie_Eq in
                  dec fcookie' ret
              end)
    end.

%Set "comment_vars".

Define minus_char_inc
  : Forall(c d next:char)(n:nat)(carry:bool)
          (u1:{ (minus (which_char c) (which_char d)) = (S n)})
          (u2:{ (char_inc d) = (mk_char_inc_t next carry)}).
       {(minus (which_char c) (which_char next)) = n} :=
 foralli(c d next:char)(n:nat)(carry:bool)
        (u1:{ (minus (which_char c) (which_char d)) = (S n)})
        (u2:{ (char_inc d) = (mk_char_inc_t next carry)}).
 abbrev tnc = terminates (which_char c) by to_nat_tot in
 abbrev tnd = terminates (which_char d) by to_nat_tot in
 abbrev tnnext = terminates (which_char next) by to_nat_tot in
 abbrev ltdc = [minus_S_lt tnc tnd n u1] in
 abbrev carry_ff = [char_inc_lt d c next carry ltdc u2] in
   trans symm
         cong (minus tnc *)
           trans [to_nat_char_inc d next carry u2]
           trans cong (condplus * (pow2 charlen) (to_nat next))
                   carry_ff
              [condplusff terminates (pow2 charlen) by pow_total
                  tnnext]
         inj (S *) trans symm [minusS2 tnc tnd ltdc] u1.

%- prove that cvfolding using a function that is terminating given
   smaller As than l is terminating. -%
Define cvfold_h_sztot 
  : Forall(A B C:type)(l:<charvec A>)
          (start : char)
          (fcookie:C)
          (f:Fun(fcookie:C)(c:char)(a:A)(b:B).B)
          (ftot : Forall(c:char)(a:A)(u:{ (lt size a size l) = tt})
                        (b:B).Exists(r:B).{(f fcookie c a b) = r})
          (b:B).
     Exists(r:B). {(cvfold_h l start fcookie f b) = r} :=
  foralli(A B C:type)(l:<charvec A>)
         (start : char)
         (fcookie:C)
         (f:Fun(fcookie:C)(c:char)(a:A)(b:B).B)
         (ftot : Forall(c:char)(a:A)(u:{ (lt size a size l) = tt})
                       (b:B).Exists(r:B).{(f fcookie c a b) = r})
         (b:B).
  %- the proof is by induction on the distance from start to the last
     character (CLast). -%
  abbrev tCLast = terminates (which_char CLast) by to_nat_tot in
  [induction(n:nat) 
   return Forall(start:char)
                (m:{(minus (to_nat CLast) (to_nat start)) = n }).
            Exists(r:B). { (cvfold_h l start fcookie f b) = r }
   with
     Z => 
     foralli(start:char)
            (m:{ (minus (to_nat CLast) (to_nat start)) = n }).
     existse [vec_get_sztot A num_chars l tCLast [chars_bounded CLast]]
     foralli(r:A)(sr:{ (lt size r size l) = tt})
            (ur:{(vec_get l (which_char CLast)) = r}).
     existse [ftot CLast r sr b]
     foralli(fr:B)(ufr:{(f fcookie CLast r b) = fr}).
       existsi fr
         { (cvfold_h l start fcookie f b) = * }
         trans hypjoin (cvfold_h l start fcookie f b)
                       (f fcookie CLast (vec_get l (which_char CLast)) b)
               by [minus_which_char_Z CLast start trans m n_eq] end
         trans cong (f fcookie CLast * b) ur
               ufr
   | S n' => 
     foralli(start:char)
            (m:{ (minus (to_nat CLast) (to_nat start)) = n }).
     abbrev tstart = terminates (which_char start) by to_nat_tot in
     abbrev r = terminates (char_inc start) by char_inc_tot in
     abbrev ltstartlast = [minus_S_lt tCLast tstart n' trans m n_eq] in
       case r with
         mk_char_inc_t next carry =>
         abbrev carry_ff = [char_inc_notfull start next carry
                              ltstartlast
                              r_eq] in
         abbrev tnext = terminates (which_char next) by to_nat_tot in
           existse [vec_get_sztot A num_chars l tstart [chars_bounded start]]
           foralli(a:A)(sa:{ (lt size a size l) = tt})
              (ua:{(vec_get l (which_char start)) = a}).
           existse
             [n_IH n' next 
               [minus_char_inc CLast start next n' carry trans m n_eq r_eq]]
             foralli(cvfr:B)(ucvfr: { (cvfold_h l next fcookie f b) = cvfr }).
               existse [ftot start a sa cvfr]
               foralli(q:B)(uq:{(f fcookie start a cvfr) = q}).
               existsi q { (cvfold_h l start fcookie f b) = *}
                 trans
                   hypjoin (cvfold_h l start fcookie f b) 
                           (f fcookie start (vec_get l (which_char start)) 
                              (cvfold_h l next fcookie f b))
                     by r_eq carry_ff end
                 trans
                   cong (f fcookie start * (cvfold_h l next fcookie f b))
                     ua
                 trans
                   cong (f fcookie start a *)
                     ucvfr
                   uq
       end
   end
  abbrev tstart = terminates (which_char start) by to_nat_tot in
  terminates (minus tCLast tstart) 
    by [minus_tot2 tstart tCLast [chars_bounded2 start]]
  start join (minus tCLast (which_char start))
             (minus tCLast (which_char start))].
  
%- We fold the given function over all elements of the array.  Element
   0 is folded last: (f 0 a0 (f 1 a1 ...)). -%
Define cvfold := 
  fun(A B C:type)(unique_owned l:<charvec A>)
     (owned cookie:C)
     (f:Fun(owned cookie:C)(c:char)(unique_owned a:A)(b:B).B)
     (b:B).
    (cvfold_h A B C l Cc0 %- first character -% cookie f b).

Define cvfold_sztot 
  : Forall(A B C:type)(l:<charvec A>)
          (fcookie:C)
          (f:Fun(fcookie:C)(c:char)(a:A)(b:B).B)
          (ftot : Forall(c:char)(a:A)(u:{ (lt size a size l) = tt})
                        (b:B).Exists(r:B).{(f fcookie c a b) = r})
          (b:B).
     Exists(r:B). {(cvfold l fcookie f b) = r} :=
  foralli(A B C:type)(l:<charvec A>)
         (fcookie:C)
         (f:Fun(fcookie:C)(c:char)(a:A)(b:B).B)
         (ftot : Forall(c:char)(a:A)(u:{ (lt size a size l) = tt})
                       (b:B).Exists(r:B).{(f fcookie c a b) = r})
         (b:B).
  existse [cvfold_h_sztot A B C l Cc0 fcookie f ftot b]
  foralli(q:B)(uq:{(cvfold_h l Cc0 fcookie f b) = q}).
    existsi q
      {(cvfold l fcookie f b) = *}
      trans evalto (cvfold l fcookie f b) (cvfold_h l Cc0 fcookie f b)
            uq.

Define cvfold_h_tot 
  : Forall(A B C:type)(l:<charvec A>)
          (start : char)
          (fcookie:C)
          (f:Fun(fcookie:C)(c:char)(a:A)(b:B).B)
          (ftot : Forall(c:char)(a:A)
                        (b:B).Exists(r:B).{(f fcookie c a b) = r})
          (b:B).
     Exists(r:B). {(cvfold_h l start fcookie f b) = r} :=
  foralli(A B C:type)(l:<charvec A>)
         (start : char)
         (fcookie:C)
         (f:Fun(fcookie:C)(c:char)(a:A)(b:B).B)
         (ftot : Forall(c:char)(a:A)
                       (b:B).Exists(r:B).{(f fcookie c a b) = r})
         (b:B).
  [cvfold_h_sztot A B C l start fcookie f 
     foralli(c:char)(a:A)(u:{ (lt size a size l) = tt})
            (b:B). [ftot c a b]
     b].