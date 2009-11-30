%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% char-indexed arrays of unique data
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Include trusted "vec.g".
Include trusted "string.g".
Include trusted "minus.g".
Include trusted "unique_owned.g".
Include "unit.g".
Include "charray.g".

% the string tells which characters' values are checked out right now.

Define primitive type_family_abbrev qcharray := fun(A:type)(s:string).<vec A num_chars> <<END
#define gdelete_qcharray(x) 
END.

Define primitive qcharray_new 
  : Fun(spec A B:type)(^#owned b:B)(f:Fun(^#owned b:B).#unique A).#unique <qcharray A stringn>
 := fun(A B:type)(b:B)(f:Fun(b:B).A).
      (mkvec A (f b) num_chars) <<END
typedef void *(*funtp_gmk_qcharray)(void *);

void *gqcharray_new(void *b, funtp_gmk_qcharray f) {
  void **h = (void **)guru_malloc(sizeof(void *)*128);
  int c;
  for (c = 0; c <= 127; c++)
    h[c] = f(b);
  return h;
}
END.

Define primitive qcharray_empty 
  : Fun(A:type).#unique <qcharray A all_chars> <<END
void *gqcharray_empty(int A) {
  return (void **)guru_malloc(sizeof(void *)*128);
}
END.

Inductive qcharray_mod_t : Fun(A:type)(c:char)(s:string).type :=
  mk_qcharray_mod : Fun(A:type)(#unique a:A)(spec c:char)(spec s:string)
                       (#unique l:<qcharray A (stringc c s)>).#unique <qcharray_mod_t A c s>.

% check out the unique value for c, assuming c is not already checked out.

Define primitive qcharray_out 
  : Fun(A:type)(#untracked c:char)(spec s : string)(#unique l:<qcharray A s>)
       (u : { (string_mem c s) = ff}).
    #unique <qcharray_mod_t A c s>
 := fun(A:type)(c:char)(spec s:string)(l:<qcharray A s>)(u:{(string_mem c s) = ff}).
      (mk_qcharray_mod A (vec_get A num_chars l (which_char c) [chars_bounded c]) c s l) <<END
 void *gqcharray_out(int A, int c, void *l) {
   return gmk_qcharray_mod(A,((void **)l)[c],l);
 }
END.

Define primitive qcharray_in
  : Fun(spec A:type)(#untracked c:char)(#unique a:A)(spec s1 s2:string)
       (#unique l:<qcharray A (string_app s1 (stringc c s2))>). 
    #unique <qcharray A (string_app s1 s2)>
:= fun(A:type)(c:char)(a:A)(spec s1 s2:string)
      (l:<qcharray A (string_app s1 (stringc c s2))>). 
    (vec_update A num_chars l (which_char c) a [chars_bounded c]) <<END
 void *gqcharray_in(int c, void *a, void *l) {
   ((void **)l)[c] = a;
   return l;
 }
END.

% simpler interface to qcharray_in, for when you have checked out the
% value for just one character.
Define qcharray_out1 : Fun(A:type)(#untracked c:char)
                          (#unique l:<qcharray A stringn>). 
                          #unique <qcharray_mod_t A c stringn> :=
  fun(A:type)(#untracked c:char)(#unique l:<qcharray A stringn>)
    : #unique <qcharray_mod_t A c stringn>.
    (qcharray_out A c stringn l join (string_mem c stringn) ff).

% simpler interface to qcharray_in, for when you have checked out the
% value for just one character.
Define qcharray_in1 : Fun(spec A:type)(#untracked c:char)(#unique a:A)
                         (#unique l:<qcharray A (stringc c stringn)>). 
                       #unique <qcharray A stringn> :=
  fun(spec A:type)(#untracked c:char)(#unique a:A)
     (#unique l:<qcharray A (stringc c stringn)>): #unique <qcharray A stringn>.
     cast
     (qcharray_in A c a stringn stringn
        cast l
        by cong <qcharray A *> 
             join (stringc c stringn) (string_app stringn (stringc c stringn)))
     by cong <qcharray  A *> join (string_app stringn stringn) stringn.

% read-only access
Define primitive qcharray_read
 : Fun(spec A:type)(#untracked c:char)
      (! #unique_owned l:<qcharray A stringn>). 
    #<unique_owned l> A :=
  fun(spec A:type)(c:char)(l:<qcharray A stringn>).
    (vec_get A num_chars l (which_char c) [chars_bounded c]) <<END
inline void *gqcharray_read(int c, void **a) { return a[c]; }
END.

Define primitive qcharray_free
   : Fun(spec A C:type)(^ #unique l:<qcharray A stringn>)
        (^#owned cookie:C)
        (delA : Fun(^#owned cookie:C)(^#unique a:A).void).void :=
  fun(spec A C:type)(l:<qcharray A stringn>)
     (cookie:C)
     (delA : Fun(cookie:C)(a:A).void).voidi <<END
typedef void (*ucvfree_fun_t)(void *cookie, void *a);

void gqcharray_free(void *l, void *cookie, ucvfree_fun_t delA) {
  int c;
  for (c = 0; c <= 127; c++) 
    delA(cookie,((void **)l)[c]);
  carraway_free(l);
}
END.

%Set "debug_classify_term_apps".
%Set "debug_refine_cases".

Define spec qcharray_fold :=
	fun qcharray_fold (A B C:type)(l:<qcharray A stringn>)(cookie:C)
		(f:Fun(cookie:C)(c:char)(a:A)(b:B).B)
		(b:B) : B.
	match l with
		vecn A' => b
	|	vecc A' n' a' l' => (f cookie Cc0 a' (qcharray_fold A B C l' cookie f b))
	end.
%-
-%

Define spec qcharray_fold :=
	fun qcharray_fold(A B:type)(c:char)(spec n:nat)
                (inv1 : { (plus (to_nat c) n) = num_chars}) 
		(f:Fun(c:char)(a:A)(b:B).B)
		(b:B)
                (l:<vec A n>) : B.
	match l with
		vecn _ => b
	|	vecc _ n' a' l' => 
                   match l' with
                     vecn _ => b 
                   | vecc _ n'' _ _ =>
                      (f c a' (qcharray_fold A B (char_inc1 c missing_proof1) n' missing_proof2 l' f b))
                   end
	end.
%-
Inductive cvfold_i : Fun(A B:type).type :=
  mk_cvfold_i : Fun(A B C:type)(#unique_owned l:<charray A>)
                   (start next : char)
                   (fcookie:C)
                   (f:Fun(#owned fcookie:C)(c:char)(#unique_owned a:A)(b:B).B)
                   (b:B)
                   (r:Fun(A B C:type)(#unique_owned l:<charray A>)
                         (start : char)
                         (#owned fcookie:C)
                         (f:Fun(#owned fcookie:C)
                               (c:char)(#unique_owned a:A)(b:B).B)
                         (b:B).B). <cvfold_i A B>.
Define cvfold_h :=
  fun cvfold_h(A B C:type)(#unique_owned l:<qcharray A>)
              (start : char)
              (#owned fcookie:C)
              (f:Fun(#owned fcookie:C)(c:char)(#unique_owned a:A)(b:B).B)
              (b:B):B.
    match (char_inc start) with
      mk_char_inc_t next wrapped =>
        let cookie = 
              match wrapped with
                ff => (mk_cvfold_i A B C l start next (inc C fcookie) f b cvfold_h)
              | tt => (mk_cvfold_i A B C l start next (inc C fcookie) f b 
                         fun(A B C:type)(#unique_owned l:<charray A>)
                            (start : char)
                            (#owned fcookie:C)
                            (f:Fun(#owned fcookie:C)(c:char)
                                  (#unique_owned a:A)(b:B).B)
                            (b:B). b)
                     end in
%		  (qcharray_out A start 
		  (ucvget A l start <cvfold_i A B> B
            cookie
            fun(cookie: <cvfold_i A B>)(#unique_owned a:A).
              match cookie with
                mk_cvfold_i A' B' C' l' start' next' fcookie' f' b' r =>
                  abbrev ca = cast a by inj <cvfold_i * **> cookie_Eq in
                  let ret = 
                    cast (f' fcookie' start' ca 
                           (r A' B' C' l' next' fcookie' f' b')) 
                    by symm inj <cvfold_i ** *> cookie_Eq in
                  do (dec C' fcookie')
					 ret
				  end
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
  : Forall(A B C:type)(l:<charray A>)
          (start : char)
          (fcookie:C)
          (f:Fun(fcookie:C)(c:char)(a:A)(b:B).B)
          (ftot : Forall(c:char)(a:A)(u:{ (lt size a size l) = tt})
                        (b:B).Exists(r:B).{(f fcookie c a b) = r})
          (b:B).
     Exists(r:B). {(cvfold_h l start fcookie f b) = r} :=
  foralli(A B C:type)(l:<charray A>)
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
  fun(A B C:type)(unique_owned l:<charray A>)
     (owned cookie:C)
     (f:Fun(owned cookie:C)(c:char)(unique_owned a:A)(b:B).B)
     (b:B).
    (cvfold_h A B C l Cc0 %- first character -% cookie f b).

Define cvfold_sztot 
  : Forall(A B C:type)(l:<charray A>)
          (fcookie:C)
          (f:Fun(fcookie:C)(c:char)(a:A)(b:B).B)
          (ftot : Forall(c:char)(a:A)(u:{ (lt size a size l) = tt})
                        (b:B).Exists(r:B).{(f fcookie c a b) = r})
          (b:B).
     Exists(r:B). {(cvfold l fcookie f b) = r} :=
  foralli(A B C:type)(l:<charray A>)
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
  : Forall(A B C:type)(l:<charray A>)
          (start : char)
          (fcookie:C)
          (f:Fun(fcookie:C)(c:char)(a:A)(b:B).B)
          (ftot : Forall(c:char)(a:A)
                        (b:B).Exists(r:B).{(f fcookie c a b) = r})
          (b:B).
     Exists(r:B). {(cvfold_h l start fcookie f b) = r} :=
  foralli(A B C:type)(l:<charray A>)
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

-%
