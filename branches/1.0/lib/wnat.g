Include "word.g".
Include "list.g".

% least significant word comes first

Define wnat := <list word>.
Define WNn := (nil word).
Define WNc := (cons word).

Define wnat_inc :=
  fun wnat_inc(N:wnat):wnat.
    match N with
      nil A => 
        match (word_inc word0) with
          mk_word_inc_t w carry => (WNc w WNn) % we know carry = ff
        end
    | cons A w' N' => 
      abbrev P = symm inj <list *> N_Eq in
      abbrev w = cast w' by P in
      abbrev cN' = cast N' by cong <list *> P in
      match (word_inc w) with
        mk_word_inc_t w' carry => 
          match carry with
            ff => (WNc w' cN')
          | tt => (WNc w' (wnat_inc cN'))
          end
        end
    end.

Define spec wnat_to_nat : Fun(N:wnat).nat :=
  fun(N:wnat).
    let r = (vec_cat2 bool wordlen N) in
    match r with
      mk_vec_cat2_t A l v =>
        (to_nat l cast v by cong <vec * l> symm inj <vec_cat2_t *> r_Eq)
      end.

%Set "debug_def_eq".
%Set "debug_ordered_rewrite".
    	
Define to_nat_wnat_inc : 
  Forall(N:wnat). 
     { (wnat_to_nat (wnat_inc N)) = (S (wnat_to_nat N)) } :=
  induction(N:wnat) 
     return { (wnat_to_nat (wnat_inc N)) = (S (wnat_to_nat N)) } with
    nil A => hypjoin (wnat_to_nat (wnat_inc N))
                     (S (wnat_to_nat N))
             by N_eq end
  | cons A w N' => 
    abbrev P = symm inj <list *> N_Eq in
    abbrev cw = cast w by P in
    abbrev cN' = cast N' by cong <list *> P in
    abbrev iw = terminates (word_inc cw) by word_inc_tot in

%-
    abbrev vN = terminates (vec_cat2 bool wordlen N) by vec_cat2_total in
    case vN with
    mk_vec_cat2_t A l v =>
-%
      case iw with
        mk_word_inc_t w' carry =>
          case carry with
            ff => 

	    %- TUTORIAL: there is an interesting piece of reasoning
	    here, because we do not want to compute 2 to the power
	    wordlen.  Hence, we must join carefully.  We use
	    universal abstraction to avoid accidentally computing
	    2 to the wordlen. -%
            abbrev P2 = 
              trans [word_to_nat_inc cw w' carry iw_eq] 
              trans cong (condplus * (pow2 wordlen) (word_to_nat w'))
                      carry_eq
                    [foralli(x y:nat). join (condplus ff x y) y
                       terminates (pow2 wordlen) by pow_total 
                       terminates (word_to_nat w') by word_to_nat_tot] in
            

            show

              P2

              trans
                cong (wnat_to_nat *)
                  hypjoin (wnat_inc N) (WNc w' N')
                  by N_eq carry_eq iw_eq end
                join (wnat_to_nat (WNc w' N'))
                     (to_nat (vec_append w' N'))
    
            end

             
          | tt => truei
          end
      end
  end.
