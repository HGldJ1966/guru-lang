Include "mult.g".

Define pow : Fun(base exp : nat). nat :=
   fun pow(base exp : nat) : nat.
   	match exp by x y return nat with
		Z => (S Z)
		| S exp' => (mult base (pow base exp'))
	end.  

Define first_power : Forall ( x : nat).{ (pow x (S Z)) = x} :=
	induction (x :nat) by x1 x2 IH return 	{ (pow x (S Z)) = x} with
	Z => trans cong (pow * (S Z)) x1
		trans join (pow Z (S Z)) (mult Z (pow Z Z))
		trans join (mult Z (pow Z Z)) (mult Z (S Z))
		trans [mult_comm Z (S Z)]
		trans join (mult (S Z) Z) Z
		symm x1
	|S x' => trans cong (pow * (S Z)) x1
		trans join (pow (S x') (S Z)) (mult (S x') (pow (S x') Z))
		trans join (mult (S x') (pow (S x') Z)) (mult (S x') (S Z))
		trans [multOne (S x')]
		symm x1
	end.

Define pow_total : Forall(b e : nat).Exists(z:nat).{(pow b e) = z} :=
	foralli(b:nat).induction(e:nat) by x1 x2 IH return Exists(z:nat).{(pow b e) = z} with
	Z => existsi one {(pow b e) = *}
		trans cong (pow b *) x1
		join (pow b Z) one
	| S e' => existse [IH e'] foralli(z':nat)(u:{(pow b e') = z'}).
		existse [mult_total b z'] foralli(z:nat)(u':{(mult b z') = z}).
		existsi z {(pow b e) = *}
		trans cong (pow b *) x1
		trans join (pow b (S e')) (mult b (pow b e'))
		trans cong (mult b *) u
		u'
	end.

Total pow pow_total.


Define pow_not_zero : Forall(b e : nat)(u:{ b != Z }).{(pow b e) != Z} :=
	foralli(b:nat).induction(e:nat) by x1 x2 IH return Forall(u:{ b != Z }).{(pow b e) != Z} with
	Z => 	foralli(u:{ b != Z }).
		trans cong (pow b *) x1
		trans join (pow b Z) one
		clash one Z
	| S e' => foralli(u:{ b != Z }). 
		trans cong (pow b *) x1
		trans join (pow b (S e')) (mult b (pow b e'))
		existse [pow_total b e'] foralli(z:nat)(v:{(pow b e') = z}).
		trans cong (mult b *) v
		[mult_not_zero b z u trans symm v [IH e' u]]
		
	end.
	
Define pow_mult : Forall(y b x:nat). { (mult (pow b x) (pow b y)) = (pow b (plus x y))} :=
	foralli(y b :nat).induction (x:nat) by x1 x2 IH return { (mult (pow b x) (pow b y)) = (pow b (plus x y))} with
	Z =>  trans cong (mult (pow b *) (pow b y)) x1
	      trans join (mult (pow b Z) (pow b y)) (mult one (pow b y))
	      existse [pow_total b y] foralli(a:nat)(a':{(pow b y) = a}).
	      trans cong (mult one *) a'
	      trans [multOne2 a]
	      trans symm a'
	      trans join (pow b y) (pow b (plus Z y))
	      cong (pow b (plus * y)) symm x1
	| S x' => trans cong (mult (pow b *) (pow b y)) x1
		trans join (mult (pow b (S x')) (pow b y)) (mult (mult b (pow b x')) (pow b y))
		existse [pow_total b x'] foralli(f:nat)(f':{(pow b x') = f}).
		existse [pow_total b y] foralli(g:nat)(g':{(pow b y) = g}).
		trans cong (mult (mult b *) (pow b y)) f'
		trans cong (mult (mult b f) *) g'
		trans [mult_assoc b f g]
		trans cong (mult b (mult * g)) symm f'
		trans cong (mult b (mult (pow b x') *)) symm g'
		trans cong (mult b *) [IH x']
		trans join (mult b (pow b (plus x' y))) (pow b (S (plus x' y)))
		trans join (pow b (S (plus x' y))) (pow b (plus (S x') y))
		cong (pow b (plus * y)) symm x1
	end.

Define pow2 := (pow (S (S Z))).

Set "debug_def_eq".

Define pow2_add : Forall (e : nat).{(plus (pow2 e) (pow2 e)) = (pow2 (S e))} :=
	induction (e : nat) return {(plus (pow2 e) (pow2 e)) = (pow2 (S e))} with
	Z => hypjoin (plus (pow2 e) (pow2 e)) (pow2 (S e))
             by e_eq end
	| S e' => trans cong (plus (pow two *) (pow two *)) e_eq
		trans join (plus (pow two (S e')) (pow two (S e'))) (plus (mult two (pow two e')) (mult two (pow two e')))
		existse [pow_total two e'] foralli(a:nat)(a':{(pow two e') = a}).
		trans cong (plus (mult two *) (mult two *)) a'
		trans symm [mult_dist two a a]
		trans cong  (mult two (plus * *)) symm a'
		trans cong  (mult two *) [e_IH e']
		trans cong (mult * (pow two (S e'))) symm [first_power two]
		trans [pow_mult (S e') two one]
		trans cong (pow two *) symm [plus_comm (S e') (S Z)]
		trans cong (pow two (plus * (S Z))) symm e_eq
		trans cong (pow two *) [plusS e Z]
		cong (pow two (S *)) [plusZ e]
	end.

% return ff if even, tt if odd.
Define mod2 :=
  fun mod2(n:nat):bool. 
    match n with
      Z => ff
    | S n' => (not (mod2 n'))
    end.

Define mod2_total_h : Forall(x y:nat)(u:{(le y x) = tt}). 
                      Exists(r:bool). {(mod2 y) = r} :=
  induction(x:nat) by ux ign IH
  return Forall(y:nat)(u:{(le y x) = tt}). 
         Exists(r:bool). {(mod2 y) = r} with
    Z => foralli(y:nat)(u:{(le y x) = tt}).
           existsi ff { (mod2 y) = * } 
             hypjoin (mod2 y) ff
             by [le_Z1 y symm trans symm u cong (le y *) ux] end
  | S x1 => 
       induction(y:nat) by uy ign ign 
       return Forall(u:{(le y x) = tt}).Exists(r:bool). {(mod2 y) = r} with
         Z => foralli(u:{(le y x) = tt}).
                existsi ff { (mod2 y) = *} hypjoin (mod2 y) ff by uy end
       | S y' => 
         foralli(u:{(le y x) = tt}).
         [induction(x'':nat) by ux'' ign ign 
          return Forall(uy':{y' = x''}).
                 Exists(r:bool).{(mod2 y) = r} with
            Z => foralli(uy':{y' = x''}).
                 existsi tt { (mod2 y) = * } 
                   hypjoin (mod2 y) tt by uy trans uy' ux'' end
          | S y'' => 
            foralli(uy':{y' = x''}).
            existse [IH x1 y'' 
                      [le_S2 y'' x1
                        symm trans symm u 
                             trans cong (le * x) 
                                     trans uy 
                                       cong (S *) 
                                         trans uy' ux''
                             trans cong (le (S (S y'')) *) ux 
                                   [S_le_S (S y'') x1 ]]]
            foralli(r1:bool)(ur1:{ (mod2 y'') = r1}).
            existsi (not (not r1)) { (mod2 y) = * }
              trans cong (mod2 *) uy
              trans cong (mod2 (S *)) trans uy' ux''
              trans join (mod2 (S (S y''))) (not (not (mod2 y'')))
                    cong (not (not *)) ur1
          end y' refl y']
       end
   end.

Define mod2_total : Forall(x:nat). Exists(r:bool). {(mod2 x) = r} :=
  foralli(x:nat).[mod2_total_h x x [x_le_x x]].

Total mod2 mod2_total.

Define mod2_SS : Forall(n:nat). { (mod2 (S (S n))) = (mod2 n) } :=
  foralli(n:nat). 
  case n with
    Z => trans cong (mod2 (S (S *))) n_eq
         trans join (mod2 (S (S Z))) (mod2 Z)
               symm cong (mod2 *) n_eq
  | S n' => trans cong (mod2 (S (S *))) n_eq
            trans join (mod2 (S (S (S n')))) (not (not (mod2 (S n'))))
            trans [not_not (mod2 (S n'))]
                  symm cong (mod2 *) n_eq
  end.

Define div2 :=
  fun div2(x:nat):nat.
    match x with 
      Z => Z
    | S x' => match x' with
                Z => Z
              | S x'' => (S (div2 x''))
              end
    end.

Define div2_total_h
  : Forall(x y:nat)(u:{(le y x) = tt}). Exists(r:nat). {(div2 y) = r} :=
  induction(x:nat) by ux ign IH 
  return Forall(y:nat)(u:{(le y x) = tt}). Exists(r:nat). {(div2 y) = r} with
    Z => foralli(y:nat)(u:{(le y x) = tt}).
           existsi Z { (div2 y) = * } 
             hypjoin (div2 y) Z 
             by [le_Z1 y symm trans symm u cong (le y *) ux] end
  | S x1 => 
       induction(y:nat) by uy ign ign 
       return Forall(u:{(le y x) = tt}).Exists(r:nat). {(div2 y) = r} with
         Z => foralli(u:{(le y x) = tt}).
                existsi Z { (div2 y) = *} hypjoin (div2 y) Z by uy end
       | S y' => 
         foralli(u:{(le y x) = tt}).
         [induction(x'':nat) by ux'' ign ign 
          return Forall(uy':{y' = x''}).
                 Exists(r:nat).{(div2 y) = r} with
            Z => foralli(uy':{y' = x''}).
                 existsi Z { (div2 y) = * } 
                   hypjoin (div2 y) Z by uy trans uy' ux'' end
          | S y'' => 
            foralli(uy':{y' = x''}).
            existse [IH x1 y'' 
                      [le_S2 y'' x1
                        symm trans symm u 
                             trans cong (le * x) 
                                     trans uy 
                                       cong (S *) 
                                         trans uy' ux''
                             trans cong (le (S (S y'')) *) ux 
                                   [S_le_S (S y'') x1 ]]]
            foralli(r:nat)(ur:{(div2 y'') = r}).
            existsi (S r) { (div2 y) = * }
              hypjoin (div2 y) (S r) by uy trans uy' ux'' ur end
           end y' join y' y']
       end 
end.

Define div2_total := foralli(x:nat). [div2_total_h x x [x_le_x x]].

Define div2_le_h : Forall(n n':nat)(u:{(le n' n) = tt}).
                    {(le (div2 (S n')) n') = tt} :=
 induction(n:nat) by un ign IH
 return Forall(n':nat)(u:{(le n' n) = tt}).
          {(le (div2 (S n')) n') = tt} with
   Z => foralli(n':nat)(u:{(le n' n) = tt}).
          hypjoin (le (div2 (S n')) n') tt
          by [le_Z1 n' symm trans symm u cong (le n' *) un] end
 | S n1 => induction(n':nat) by un' ign ign
           return Forall(u:{(le n' n) = tt}).
                   {(le (div2 (S n')) n') = tt} with
             Z => foralli(u:{(le n' n) = tt}).
                    hypjoin (le (div2 (S n')) n') tt by un' end
           | S n1' => 
             foralli(u:{(le n' n) = tt}).
             [induction(i:nat) by ui ign ign 
              return Forall(un1':{n1' = i}). {(le (div2 (S n')) n') = tt} with
                Z => foralli(un1':{n1' = i}).
                       hypjoin (le (div2 (S n')) n') tt 
                       by un' trans un1' ui end
              | S n1'' => 
                foralli(un1':{n1' = i}).
                trans cong (le (div2 (S *)) *) 
                       trans un' cong (S *) trans un1' ui
                trans cong (le * (S (S n1'')))
                        join (div2 (S (S (S n1'')))) (S (div2 (S n1'')))
                abbrev d2 = terminates (div2 (S n1'')) by div2_total in
                trans [S_le_S d2 (S n1'')]
                      [le_S3 d2 n1''
                        [IH n1 n1''
                          [le_S2 n1'' n1
                            symm trans symm u
                                 trans cong (le * n)
                                         trans un'
                                           cong (S *) trans un1' ui
                                 trans cong (le (S (S n1'')) *) un
                                        [S_le_S (S n1'') n1]]]] 
              end n1' join n1' n1']
            end
 end.
  
Define div2_le := foralli(n:nat).[div2_le_h n n [x_le_x n]].

Define mult2 := (mult (S (S Z))).

Define mult2_S : Forall(n:nat). { (mult2 (S n)) = (S (S (mult2 n))) } :=
  foralli(n:nat). trans [multS (S (S Z)) n]
                        join (plus (S (S Z)) (mult2 n)) (S (S (mult2 n))).

%-
Define mult2_total : Forall(x:nat).Exists(y:nat).{(mult2 x) = y} :=
  foralli(x:nat). [mult_total (S (S Z)) x].
-%

Define lt_S_mult2 : Forall(x y:nat)
                          (u:{(lt (mult2 x) (mult2 y)) = tt}).
                    { (lt (S (mult2 x)) (mult2 y)) = tt} :=
  induction(x:nat)
  return Forall(y:nat)
               (u:{(lt (mult2 x) (mult2 y)) = tt}).
           { (lt (S (mult2 x)) (mult2 y)) = tt} with
    Z => foralli(y:nat)
                (u:{(lt (mult2 x) (mult2 y)) = tt}).
         case y with
           Z => contra
                  trans
                    trans symm u
                          hypjoin (lt (mult2 x) (mult2 y)) ff
                          by x_eq y_eq end
                    clash ff tt
                  { (lt (S (mult2 x)) (mult2 y)) = tt }
         | S y' => trans cong (lt (S *) (mult2 y))
                          hypjoin (mult2 x) Z by x_eq end
                   trans cong (lt (S Z) *)
                           trans cong (mult2 *) y_eq
                                 [mult2_S y']
                         join (lt (S Z) (S (S (mult2 y')))) tt
         end
  | S x' =>
    foralli(y:nat)
           (u:{(lt (mult2 x) (mult2 y)) = tt}).
    case y with
      Z => contra
             trans
               trans symm u
                     hypjoin (lt (mult2 x) (mult2 y)) ff
                     by x_eq y_eq end
               clash ff tt
             { (lt (S (mult2 x)) (mult2 y)) = tt }
    | S y' => 
      abbrev Px = trans cong (mult2 *) x_eq [mult2_S x'] in
      abbrev Py = trans cong (mult2 *) y_eq [mult2_S y'] in
      abbrev ty' = terminates (mult2 y') by mult_total in
      abbrev tx' = terminates (mult2 x') by mult_total in
      trans cong (lt (S *) (mult2 y)) Px
      trans cong (lt (S (S (S (mult2 x')))) *) Py
      trans [S_lt_S (S (S tx')) (S ty')]
      trans [S_lt_S (S tx') ty']
            [x_IH x' y' 
               symm
               trans symm u
               trans cong (lt * (mult2 y)) Px
               trans cong (lt (S (S (mult2 x'))) *) Py
               trans [S_lt_S (S tx') (S ty')]
                     [S_lt_S tx' ty']]
    end
  end.

Define mult2_mult_pow2
   : Forall(n m:nat). { (mult2 (mult (pow2 n) m)) = (mult (pow2 (S n)) m) } :=
   induction(n:nat)
     return Forall(m:nat).
             { (mult2 (mult (pow2 n) m)) = (mult (pow2 (S n)) m) } with
     Z => foralli(m:nat).
            hypjoin (mult2 (mult (pow2 n) m)) (mult (pow2 (S n)) m)
            by n_eq [plusZ m] end
   | S n' => foralli(m:nat).
               abbrev a = terminates (pow2 n') by pow_total in
               abbrev b = terminates (pow2 (S n')) by pow_total in
               trans
                 hypjoin (mult2 (mult (pow2 n) m)) 
                         (mult2 (mult (mult2 (pow2 n')) m))
                 by n_eq end
               trans
                 cong (mult2 *) 
                   trans [mult_assoc (S (S Z)) a m]
                   [n_IH n' m]
               trans
                 symm [mult_assoc (S (S Z)) b m]
               hypjoin (mult (mult2 b) m)
                       (mult (pow2 (S n)) m)
               by n_eq end
   end.

Define condS := fun(b:bool)(n:nat). match b with ff => n | tt => (S n) end.

Define condS_tot := 
  induction(b:bool) by ub ign ign 
  return Forall(n:nat).Exists(m:nat).{ (condS b n) = m } with
    ff => foralli(n:nat).
            existsi n { (condS b n) = * } 
              hypjoin (condS b n) n by ub end
  | tt => foralli(n:nat).
            existsi (S n) { (condS b n) = * } 
              hypjoin (condS b n) (S n) by ub end
  end.

Total condS condS_tot.

Define condS_Z1 : Forall(b:bool)(n:nat)(u:{(condS b n) = Z}).{b = ff} :=
  induction(b:bool) by ub ign ign 
  return Forall(n:nat)(u:{(condS b n) = Z}).{b = ff} with
    ff => foralli(n:nat)(u:{(condS b n) = Z}). ub
  | tt => foralli(n:nat)(u:{(condS b n) = Z}).
          contra
            trans
              trans hypjoin (S n) (condS b n) by ub end
                    u
              clash Z (S n)
            { b = ff }
  end.

Define condS_Z2 : Forall(b:bool)(n:nat)(u:{(condS b n) = Z}).{n = Z} :=
  induction(b:bool) by ub ign ign 
  return Forall(n:nat)(u:{(condS b n) = Z}).{n = Z} with
    ff => foralli(n:nat)(u:{(condS b n) = Z}). 
          symm trans symm u
                     hypjoin (condS b n) n by ub end
  | tt => foralli(n:nat)(u:{(condS b n) = Z}).
          contra
            trans
              trans hypjoin (S n) (condS b n) by ub end
                    u
              clash Z (S n)
            { n = Z }
  end.

Define condS_plus : Forall(a:bool)(n m:nat).
                      { (condS a (plus n m)) = (plus (condS a n) m) } :=
  induction(a:bool) 
    return Forall(n m:nat).
            { (condS a (plus n m)) = (plus (condS a n) m) } with
    ff => foralli(n m:nat).
          hypjoin (condS a (plus n m)) 
                  (plus (condS a n) m)
          by a_eq end
  | tt => foralli(n m:nat).
          hypjoin (condS a (plus n m)) 
                  (plus (condS a n) m)
          by a_eq end
  end.

Define div2_mult2 : Forall(b:bool)(n:nat).{(div2 (condS b (mult2 n))) = n} :=
  foralli(b:bool)(n:nat).
  trans cong (div2 (condS b *)) [mult_comm (S (S Z)) n]
    [induction(n:nat) by un ign IH
     return Forall(b:bool).{(div2 (condS b (mult n (S (S Z))))) = n} with
       Z => induction(b:bool) by ub ign ign 
            return {(div2 (condS b (mult n (S (S Z))))) = n} with
              ff => hypjoin (div2 (condS b (mult n (S (S Z))))) n
                    by ub un end
            | tt => hypjoin (div2 (condS b (mult n (S (S Z))))) n
                    by ub un end
            end
      | S n' => 
        foralli(b:bool).
        abbrev q = (mult n' (S (S Z))) in
        trans cong (div2 (condS b *))
                hypjoin (mult n (S (S Z))) (S (S q))
                by un end
        trans cong (div2 *)
                [induction(b':bool) by ub' ign ign
                 return Forall(ub:{b = b'}).
                        { (condS b (S (S q))) = (S (S (condS b q))) } with
                   ff => foralli(ub:{b = b'}).
                         hypjoin (condS b (S (S q))) (S (S (condS b q)))
                         by trans ub ub' end
                 | tt => foralli(ub:{b = b'}).
                         hypjoin (condS b (S (S q))) (S (S (condS b q)))
                         by trans ub ub' end
                 end b join b b]
        trans join (div2 (S (S (condS b q)))) (S (div2 (condS b q)))
        trans cong (S *) [IH n' b]
              symm un
    end n b].

Define mod2_mult2 : Forall(b:bool)(n:nat). { (mod2 (condS b (mult2 n))) = b} :=
  foralli(b:bool)(n:nat).
  trans cong (mod2 (condS b *)) [mult_comm (S (S Z)) n]
    [induction(n:nat) by un ign IH
     return Forall(b:bool).{(mod2 (condS b (mult n (S (S Z))))) = b} with
       Z => induction(b:bool) by ub ign ign 
            return {(mod2 (condS b (mult n (S (S Z))))) = b} with
              ff => hypjoin (mod2 (condS b (mult n (S (S Z))))) b
                    by ub un end
            | tt => hypjoin (mod2 (condS b (mult n (S (S Z))))) b
                    by ub un end
            end
      | S n' => 
        foralli(b:bool).
        abbrev q = (mult n' (S (S Z))) in
        trans cong (mod2 (condS b *))
                hypjoin (mult n (S (S Z))) (S (S q))
                by un end
        trans cong (mod2 *)
                [induction(b':bool) by ub' ign ign
                 return Forall(ub:{b = b'}).
                        { (condS b (S (S q))) = (S (S (condS b q))) } with
                   ff => foralli(ub:{b = b'}).
                         hypjoin (condS b (S (S q))) (S (S (condS b q)))
                         by trans ub ub' end
                 | tt => foralli(ub:{b = b'}).
                         hypjoin (condS b (S (S q))) (S (S (condS b q)))
                         by trans ub ub' end
                 end b join b b]
        trans join (mod2 (S (S (condS b q)))) (not (not (mod2 (condS b q))))
        trans [not_not (mod2 (condS b q))]
              [IH n' b]
    end n b].
  
Define condplus := fun(b:bool)(n m:nat). 
                     match b with ff => m
                                | tt => (plus n m) end.

Define condplus_tot : Forall(b:bool)(n m:nat). Exists(r:nat). 
                            { (condplus b n m) = r } :=
  induction(b:bool) return Forall(n m:nat). Exists(r:nat). 
                              { (condplus b n m) = r } with
    ff => foralli(n m:nat). 
            existsi m { (condplus b n m) = *}
              hypjoin (condplus b n m) m
              by b_eq end
  | tt => foralli(n m:nat).
            existsi terminates (plus n m) by plus_total
              { (condplus b n m) = *}
              hypjoin (condplus b n m) (plus n m)
              by b_eq end
  end.
   
Define mult2_plus : Forall(n m:nat).
                      { (mult2 (plus n m)) = (plus (mult2 n) (mult2 m)) } :=
  foralli(n m:nat). [ mult_plus2 (S (S Z)) n m].  

Define mult2_condplus
  : Forall(b:bool)(n m : nat).
       { (mult2 (condplus b n m)) = (condplus b (mult2 n) (mult2 m)) } :=
    induction(b:bool) return
      Forall(n m : nat).
         { (mult2 (condplus b n m)) = (condplus b (mult2 n) (mult2 m)) } with
      ff => foralli(n m : nat).
              hypjoin (mult2 (condplus b n m)) (condplus b (mult2 n) (mult2 m))
              by b_eq end
    | tt => foralli(n m : nat).
              hypjoin (mult2 (condplus b n m)) (condplus b (mult2 n) (mult2 m))
              by b_eq [mult2_plus n m] end
    end.
  
Define condplusff : Forall(n m:nat). { (condplus ff n m) = m } := 
 foralli(n m:nat). 
   join (condplus ff n m) m.

