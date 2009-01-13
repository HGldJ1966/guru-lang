Include "wnat.g".
Include "list.g".

% least significant wnat comes first

Define bignat := <list wnat>.
Define BNn := (nil wnat).
Define BNc := (cons wnat).

Define bignat_inc :=
  fun bignat_inc(N:bignat):bignat.
    match N with
      nil A => 
        match (wnat_inc wnat0) with
          mk_wnat_inc_t w carry => (BNc w BNn) % we know carry = ff
        end
    | cons A w' N' => 
      abbrev P = symm inj <list *> N_Eq in
      abbrev w = cast w' by P in
      abbrev cN' = cast N' by cong <list *> P in
      match (wnat_inc w) with
        mk_wnat_inc_t w' carry => 
          match carry with
            ff => (BNc w' cN')
          | tt => (BNc w' (bignat_inc cN'))
          end
        end
    end.

Define spec bignat_to_nat : Fun(N:bignat).nat :=
  fun(N:bignat).
    let r = (vec_cat2 bool wordlen N) in
    match r with
      mk_vec_cat2_t A l v =>
        (to_nat l cast v by cong <vec * l> symm inj <vec_cat2_t *> r_Eq)
      end.

%Set "debug_def_eq".
%Set "debug_ordered_rewrite".
    	
Define to_nat_bignat_inc : 
  Forall(N:bignat). 
     { (bignat_to_nat (bignat_inc N)) = (S (bignat_to_nat N)) } :=
  induction(N:bignat) 
     return { (bignat_to_nat (bignat_inc N)) = (S (bignat_to_nat N)) } with
    nil A => hypjoin (bignat_to_nat (bignat_inc N))
                     (S (bignat_to_nat N))
             by N_eq end
  | cons A w N' => 
    abbrev P = symm inj <list *> N_Eq in
    abbrev cw = cast w by P in
    abbrev cN' = cast N' by cong <list *> P in
    abbrev iw = terminates (wnat_inc cw) by wnat_inc_tot in

%-
    abbrev vN = terminates (vec_cat2 bool wordlen N) by vec_cat2_total in
    case vN with
    mk_vec_cat2_t A l v =>
-%
      case iw with
        mk_wnat_inc_t w' carry =>
          case carry with
            ff => 

	    %- TUTORIAL: there is an interesting piece of reasoning
	    here, because we do not want to compute 2 to the power
	    wordlen.  Hence, we must join carefully.  We use
	    universal abstraction to avoid accidentally computing
	    2 to the wordlen. -%
            abbrev P2 = 
              trans [wnat_to_nat_inc cw w' carry iw_eq] 
              trans cong (condplus * (pow2 wordlen) (wnat_to_nat w'))
                      carry_eq
                    [foralli(x y:nat). join (condplus ff x y) y
                       terminates (pow2 wordlen) by pow_total 
                       terminates (wnat_to_nat w') by wnat_to_nat_tot] in
            

            show

              P2

              trans
                cong (bignat_to_nat *)
                  hypjoin (bignat_inc N) (BNc w' N')
                  by N_eq carry_eq iw_eq end
                join (bignat_to_nat (BNc w' N'))
                     (to_nat (vec_append w' N'))
    
            end

             
          | tt => truei
          end
      end
  end.
