%Set "print_parsed".
%Set "print_ref_annos".

Include "bool.g".
Include "owned.g".
Include "comparator.g".

Inductive nat : type :=
  Z : nat
| S : Fun(x:nat).nat.

Define zero := Z.

Define isZ := fun(x:nat). match x with Z => tt | S x' => ff end.

Define one : nat := (S Z).
Define two : nat := (S one).
Define three := (S two).
Define four := (S three).
Define five := (S four).
Define six := (S five).
Define seven := (S six).
Define eight := (S seven).
Define nine := (S eight).

Define S_exists : Forall (n:nat).Exists(m:nat).{ (S n) = m} :=
	induction(n:nat) by x1 x2 IH return Exists(m:nat).{ (S n) = m} with
	Z => existsi (S Z) {(S n) = *}
		cong (S *) x1
	|S n' => existse [IH n'] foralli(m:nat)(u:{(S n') = m}).
		existsi (S m) {(S n) = *}
			trans cong (S *) x1
			cong (S *) u
	end.

Define S_not_zero : Forall (n:nat).{(S n) != Z} :=
	induction(n:nat) by x1 x2 IH return {(S n) != Z} with
	Z => trans cong (S *) x1
		clash (S Z) Z
	| S n' => trans cong (S *) x1
		existse [S_exists n'] foralli(m : nat)(u:{(S n') = m}).
		trans cong (S *) u
		clash (S m) Z
	end.

Define eqnat : Fun(^ #owned n m:nat).bool :=
  fun eqnat(^ #owned n m:nat):bool.
    match ! n with
      Z => match ! m with
             Z => tt
           | S m' => ff
           end
   | S n' => match ! m with
               Z => ff
             | S m' => (eqnat n' m')
             end
   end
.

Define eqnatTot : Forall(n m:nat).Exists(x:bool). { (eqnat n m) = x } :=
  induction(n:nat) by x1 x2 IH return
      Forall(m:nat).Exists(x:bool). { (eqnat n m) = x } with
  Z => induction(m:nat) by y1 y2 u return
           Exists(x:bool). { (eqnat n m) = x } with
       Z => existsi tt { (eqnat n m) = * }
              trans cong (eqnat * m) x1
              trans cong (eqnat Z *) y1
                    join (eqnat Z Z) tt
     | S m' => existsi ff { (eqnat n m) = * }
              trans cong (eqnat * m) x1
              trans cong (eqnat Z *) y1
                    join (eqnat Z (S m')) ff
     end
| S n' => induction(m:nat) by y1 y2 u return
            Exists(x:bool). { (eqnat n m) = x } with
          Z => existsi ff { (eqnat n m) = * }
              trans cong (eqnat * m) x1
              trans cong (eqnat (S n') *) y1
                    join (eqnat (S n') Z) ff
        | S m' => existse [IH n' m'] foralli(x:bool)(u:{(eqnat n' m') = x}).
                    existsi x {(eqnat n m) = *}
                      trans cong (eqnat * m) x1
                      trans cong (eqnat (S n') *) y1
                      trans join (eqnat (S n') (S m'))
                                 (eqnat n' m')
                            u
        end
end.

Total eqnat eqnatTot.

%Set "comment_vars".

Define eqnatTot_test
 : Forall(n:nat).Exists(f:Fun(m:nat).bool). {(eqnat n) = f} :=
 foralli(n:nat).
   existse [eqnatTot n n] foralli(z:bool)(u:{(eqnat n n) = z}).
     cinv (eqnat n) trans cong (* n) symm eval (eqnat n) u.

Define eqnatEq : Forall(n m:nat)(u:{(eqnat n m) = tt}). { n = m } :=
  induction(n:nat) by x1 x2 IH return 
      Forall(m:nat)(u:{(eqnat n m) = tt}). { n = m } with
  Z => induction(m:nat) by y1 y2 u return
           Forall(u:{(eqnat n m) = tt}). { n = m } with
       Z => foralli(u:{(eqnat n m) = tt}). trans x1 symm y1
     | S m' => foralli(u:{(eqnat n m) = tt}). 
                 contra
                 trans
                  % {tt = ff}
                   trans symm u
                   trans cong (eqnat * m) x1
                   trans cong (eqnat Z *) y1
                         join (eqnat Z (S m')) ff
                  % {ff != tt}
                   clash ff tt
                 { n = m }
     end
| S n' => induction(m:nat) by y1 y2 u return
             Forall(u:{(eqnat n m) = tt}). { n = m } with
          Z => foralli(u:{(eqnat n m) = tt}). 
                 contra
                 trans
                  % {tt = ff}
                   trans symm u
                   trans cong (eqnat * m) x1
                   trans cong (eqnat (S n') *) y1
                         join (eqnat (S n') Z) ff
                  % {ff != tt}
                   clash ff tt
                 { n = m }
        | S m' => foralli(u:{(eqnat n m) = tt}). 
                  trans x1
                  trans cong (S *)
                          [IH n' m' 
                            % {(eqnat n' m') = tt}
                            symm
                            trans symm u
                            trans cong (eqnat * m) x1
                            trans cong (eqnat (S n') *) y1
                                  join (eqnat (S n') (S m')) (eqnat n' m')]
                        symm y1
        end
end.

Define eqnatNeq : Forall(n m:nat)(u:{(eqnat n m) = ff}). { n != m } :=
  induction(n:nat) by x1 x2 IH return 
      Forall(m:nat)(u:{(eqnat n m) = ff}). { n != m } with
  Z => induction(m:nat) by y1 y2 u return
           Forall(u:{(eqnat n m) = ff}). { n != m } with
       Z => foralli(u:{(eqnat n m) = ff}). 
            contra
              trans
                trans
                   symm trans cong (eqnat * m) x1
                        trans cong (eqnat Z *) y1
                              join (eqnat Z Z) tt
                   u
                clash ff tt
            { n != m }
     | S m' => foralli(u:{(eqnat n m) = ff}). 
               symm trans y1
                          symm
                          trans x1
                                clash Z (S m')
     end
| S n' => induction(m:nat) by y1 y2 u return
            Forall(u:{(eqnat n m) = ff}). { n != m } with
          Z => foralli(u:{(eqnat n m) = ff}). 
               symm trans y1
                          symm
                          trans x1
                                clash (S n') Z
   
        | S m' => foralli(u:{(eqnat n m) = ff}). 
                  symm trans y1
                             symm
                             trans x1
                             ncong (S *) (S n') (S m')
                             [IH n' m' 
                               trans join (eqnat n' m') (eqnat (S n') (S m'))
                               trans hypjoin (eqnat (S n') (S m')) (eqnat n m) 
                                       by x1 y1 end
                               u]
        end
end.

Define neqEqnat : Forall(n m : nat)(u:{n != m}).{ (eqnat n m) = ff } :=
  foralli(n m : nat)(u:{n != m}).
  existse [eqnatTot n m]
  induction(b:bool) by bx i ni return 
     Forall(ub:{(eqnat n m) = b}).{ (eqnat n m) = ff} with
    ff => foralli(ub:{(eqnat n m) = b}).
          trans ub bx
  | tt => foralli(ub:{(eqnat n m) = b}).
          contra
            trans symm [eqnatEq n m trans ub bx]
                  u
          {(eqnat n m) = ff}
  end.

Define eqnat_refl : Forall(x:nat).{ (eqnat x x) = tt } :=
  induction(x:nat) by x1 x2 IH
        return { (eqnat x x) = tt } with
    Z => trans cong (eqnat * *) x1
               join (eqnat Z Z) tt
  | S x' => trans cong (eqnat * *) x1
            trans join (eqnat (S x') (S x'))
                       (eqnat x' x')
                  [IH x']
  end.

Define eqnat_symm : Forall(x y:nat). { (eqnat x y) = (eqnat y x) } :=
  foralli(x y:nat).
  case (eqnat x y) by u ign with
    ff => trans u
                symm [neqEqnat y x symm [eqnatNeq x y u]]
  | tt => trans cong (eqnat * y) [eqnatEq x y u]
                cong (eqnat y *) symm [eqnatEq x y u]
  end.                

Define eqnatDef := eqnatEq.

Define Sneq_neq : Forall(a b:nat)(u:{ (S a) != (S b) }).{ a != b } :=
  foralli(a b:nat)(u:{ (S a) != (S b) }).
    [ induction(z:bool) by zp zt IHz return Forall(zpf:{ (eqnat a b) = z }).{ a != b } with
        ff => % a != b
          foralli(zpf:{ (eqnat a b) = z }).
            [eqnatNeq a b trans zpf zp]
      | tt => % contradiction
          foralli(zpf:{ (eqnat a b) = z }).
            abbrev eqnatp = trans zpf zp in
            contra trans join (S a) (S a)
                   trans cong (S *) [eqnatEq a b eqnatp]
                         symm u
              { a != b }
      end terminates (eqnat a b) by eqnatTot join (eqnat a b) (eqnat a b) ].

Define lt : Fun(^ #owned a b:nat).bool :=
	fun lt(^ #owned a b:nat) : bool.
		match ! a with
		Z => match ! b with
			Z => ff
			| S b' => tt
			end
		| S a' => match ! b with
			Z => ff
			| S b' => (lt a' b')
			end
                end.

Define le : Fun(a b:nat).bool :=
	fun (a b: nat). (or (lt a b) (eqnat a b)).

Define x_lt_x : Forall(a:nat).{ (lt a a) = ff} :=
	induction(a:nat) by x1 x2 IH return {(lt a a) = ff} with
	Z => trans cong (lt * *) x1
		join (lt Z Z) ff
	| S a' => trans cong (lt * *) x1
			trans join (lt (S a') (S a')) (lt a' a')
			[IH a']
	end.

Define x_eqnat_x : Forall(a:nat).{ (eqnat a a) = tt} :=
	induction(a:nat) by x1 x2 IH return {(eqnat a a) = tt} with
	Z => trans cong (eqnat * *) x1
		join (eqnat Z Z) tt
	| S a' => trans cong (eqnat * *) x1
			trans join (eqnat (S a') (S a')) (eqnat a' a')
			[IH a']
	end.

Define eqEqnat : Forall(a b:nat)(u:{ a = b }).{ (eqnat a b) = tt } :=
  foralli(a b:nat)(u:{ a = b }).
    symm trans symm [x_eqnat_x a]
               cong (eqnat a *) u.

Define x_le_x : Forall(a:nat).{ (le a a) = tt} :=
	foralli(a:nat). trans join (le a a) (or (lt a a) (eqnat a a))
			trans cong (or * (eqnat a a)) [x_lt_x a]
			trans join (or ff (eqnat a a)) (eqnat a a)
			[x_eqnat_x a].

Define le_refl := x_le_x.

Define leZ : Forall(a:nat). { (le Z a) = tt } :=
  foralli(a:nat).
  case a with
    default nat => hypjoin (le Z a) tt by a_eq end
  end.

Define lt_total_helper : Forall(b:nat).Exists(q:bool).{(lt Z b) = q} :=
	induction(b:nat) by x1 x2 IH return Exists(q:bool).{(lt Z b) = q} with
	Z => existsi ff {(lt Z b) = *} trans cong (lt Z *) x1 join (lt Z Z) ff
	| S b' => existsi tt {(lt Z b) = *} trans cong (lt Z *) x1 join (lt Z (S b')) tt
	end.

Define lt_total : Forall(a:nat)(b:nat).Exists(q:bool).{ (lt a b) = q} :=
	induction(a :nat) by x1 x2 IH return Forall(b:nat).Exists(q:bool).{ (lt a b) = q } with
	Z =>  foralli(b:nat).
		existse [lt_total_helper b] foralli(q:bool)(u:{ (lt Z b) = q}). existsi q {(lt a b) = *} trans cong (lt * b) x1 u
	| S a' => foralli(b:nat). 
		[induction(c:nat) by y1 y2 IH2 return Forall(u:{c=b}).Exists(q:bool).{ (lt a c) = q } with
			Z => foralli(u:{c=b}).
				existsi ff {(lt a c) = *} trans cong (lt * c) x1 trans cong (lt (S a') *) y1 join (lt (S a') Z) ff
			| S c' => foralli(u:{c=b}).
				existse [IH a' c'] foralli(j:bool)(v:{(lt a' c') = j}).
				existsi j {(lt a c) = *} trans cong (lt * c) x1 trans cong (lt (S a') *) y1 trans join (lt (S a') (S c')) (lt a' c') v
		end b join b b]
	end.	
	
Total lt lt_total.

Define le_total : Forall(x y:nat).Exists(z:bool).{(le x y) = z} :=
	foralli(x y:nat).
		existse [lt_total x y] foralli(ltr:bool)(ltr':{(lt x y) = ltr}).
		existse [eqnatTot x y] foralli(eqr:bool)(eqr':{(eqnat x y) = eqr}).
		existse [or_total ltr eqr] foralli(orr:bool)(orr':{(or ltr eqr) = orr}).
		existsi orr {(le x y) = *}
		trans join (le x y) (or (lt x y) (eqnat x y))
		trans cong (or * (eqnat x y)) ltr'
		trans cong (or ltr *) eqr'
		orr'.
	
Total le le_total.	
		
Define not_zero_implies_lt : Forall(a:nat)(u:{a != Z}).{ (lt Z a) = tt} :=
	induction(a:nat) by x1 x2 IH return Forall(u:{a != Z}).{ (lt Z a) = tt} with
	Z => foralli(u:{a != Z}). contra trans symm x1 u { (lt Z a) = tt} 
	| S a' => foralli(u:{a != Z}). trans cong (lt Z *) x1 join (lt Z (S a')) tt
	end.

Define lt_implies_not_zero : Forall(a b:nat)(u:{(lt a b) = tt}).{b != Z} :=
	foralli(a b:nat)(u:{(lt a b) = tt}).
        case b with
          Z => 
          case a with
            default nat => 
              contra
                 trans symm u
                 trans hypjoin (lt a b) ff by b_eq a_eq end
                       clash ff tt
               { b != Z }
          end
       | S b' => trans b_eq
                       clash (S b') Z
       end.

Define lt_implies_neq : Forall(a b:nat)(u:{ (lt a b) = tt }).{ a != b } :=
  foralli(a b:nat)(u:{ (lt a b) = tt }).
    [ induction(z:bool) by zp zt IHz return Forall(zpf:{ (eqnat a b) = z }).{ a != b } with
        ff =>
          foralli(zpf:{ (eqnat a b) = z }).
            [eqnatNeq a b trans zpf zp]
      | tt =>
          foralli(zpf:{ (eqnat a b) = z }).
            abbrev a_is_b = [eqnatEq a b trans zpf zp] in

            contra symm trans symm [x_lt_x a]
                        trans cong (lt a *)
                                   a_is_b
                        trans u
                              clash tt ff
              { a != b }
      end terminates (eqnat a b) by eqnatTot
          join (eqnat a b) (eqnat a b) ].

Define lt_trans_helper : Forall(b:nat)(c:nat)(u:{(lt Z b) = tt})(v:{(lt b c) = tt}).{(lt Z c) = tt} :=
	induction(b:nat) by x1 x2 IH return Forall(c:nat)(u:{(lt Z b) = tt})(v:{(lt b c) = tt}).{(lt Z c) = tt} with
	Z => foralli(c:nat)(u:{(lt Z b) = tt})(v:{(lt b c) = tt}).
		[induction(d:nat) by y1 y2 IH2 return Forall(x:{d=c}).{(lt Z d) = tt} with
			Z => foralli(x:{d=c}).
				trans cong (lt Z *) x
				[not_zero_implies_lt c [lt_implies_not_zero b c v]]
			| S d' => foralli(x:{d=c}).
				trans cong (lt Z *) y1
				join (lt Z (S d')) tt
		end c join c c]
	| S b' => foralli(c:nat)(u:{(lt Z b) = tt})(v:{(lt b c) = tt}).
		[induction(d:nat) by y1 y2 IH2 return Forall(x:{d=c}).{(lt Z d) = tt} with
			Z => foralli(x:{d=c}).
				trans cong (lt Z *) x
				[not_zero_implies_lt c [lt_implies_not_zero b c v]]
			| S d' => foralli(x:{d=c}).
				trans cong (lt Z *) y1
				join (lt Z (S d')) tt
		end c join c c]
	end.
	
Define lt_trans : Forall(a b c:nat)(u:{(lt a b) = tt})(v:{(lt b c) = tt}).{(lt a c) = tt} :=
	induction(a:nat) by x1 x2 IH return Forall(b:nat)(c:nat)(u:{(lt a b) = tt})(v:{(lt b c) = tt}).{(lt a c) = tt} with
	Z => foralli(b c:nat)(u:{(lt a b) = tt})(v:{(lt b c) = tt}).
		trans cong (lt * c) x1 [lt_trans_helper b c symm trans symm u cong (lt * b) x1   v]
	|S a' => foralli(b c:nat)(u:{(lt a b) = tt})(v:{(lt b c) = tt}).
		 [induction(d:nat) by y1 y2 IH2 return Forall(p:{d=b}).{(lt a c) = tt} with
		 Z => foralli(p:{d=b}).contra trans symm y1 trans p [lt_implies_not_zero a b u] 
		 		{(lt a c) = tt}
		 | S d' => foralli(p:{d=b}).
		 	[induction(e:nat) by z1 z2 IH3 return Forall(q:{e=c}).{(lt a e) = tt} with
			Z => foralli(q:{e=c}).
				contra trans symm z1 trans  q [lt_implies_not_zero b c v]
					{(lt a e) = tt}
			| S e' => foralli(q:{e=c}).
				symm trans symm [IH a' d' e'
					symm trans symm u trans cong (lt a *) symm p trans cong (lt * d) x1 trans cong (lt (S a') *) y1 join (lt (S a') (S d')) (lt a' d')
					symm trans symm v trans cong (lt * c) symm p trans cong (lt d *) symm q trans cong (lt * e) y1 trans cong (lt (S d') *) z1 join (lt (S d') (S e')) (lt d' e')
				]
				trans join (lt a' e') (lt (S a') (S e'))
				trans cong (lt * (S e')) symm x1
				 cong (lt a *) symm z1
			end c join c c]
		 end b join b b]
	end.
	
Define lt_S : Forall(a:nat).{ (lt a (S a)) = tt} :=
	induction(a:nat) by x1 x2 IH return { (lt a (S a)) = tt} with
	Z => trans cong (lt * (S *)) x1 join (lt Z (S Z)) tt
	| S a' => trans cong (lt * (S *)) x1 trans join (lt (S a') (S (S a'))) (lt a' (S a')) [IH a']
	end.

Define Sa_lt_implies_a_lt : Forall(a:nat)(b:nat)(u:{(lt (S a) b) = tt}).{(lt a b) = tt} :=
	induction(a:nat) by x1 x2 IH return Forall(b:nat)(u:{(lt (S a) b) = tt}).{(lt a b) = tt} with
	Z => foralli(b:nat)(u:{(lt (S a) b) = tt}).
			trans cong (lt * b) x1
			[not_zero_implies_lt b [lt_implies_not_zero (S a) b u]]
	| S a' => foralli(b:nat)(u:{(lt (S a) b) = tt}).
		symm trans symm [lt_trans (S a') (S (S a')) b [lt_S (S a')] symm trans symm u cong (lt (S *) b) x1]	
		cong (lt * b) symm x1
	end.	

Define S_lt_S : Forall(a b: nat).{(lt (S a) (S b)) = (lt a b)} :=
	foralli(a b :nat). join (lt (S a) (S b)) (lt a b).

Define lt_S2 : Forall(a b:nat)(u:{ (lt (S a) b) = tt }).{ (lt a b) = tt } :=
  foralli(a b:nat)(u:{ (lt (S a) b) = tt }).
    [ induction(z:bool) by zp zt IHz return Forall(zpf:{ (lt a b) = z }).{ (lt a b) = tt } with
        ff =>
          foralli(zpf:{ (lt a b) = z }).
            % (lt a b) = ff
            abbrev ltp = trans zpf zp in

            % (lt (S a) (S b)) = ff
            abbrev ltSSff = trans join (lt (S a) (S b))
                                       (lt a b)
                                  ltp in

            % (lt b (S b)) = tt
            abbrev ltSSbtt = [lt_S b] in

            % (lt (S a) b) = tt

            symm trans symm [lt_trans (S a) b (S b) u ltSSbtt]
                       [S_lt_S a b]
      | tt =>
          foralli(zpf:{ (lt a b) = z }).
            trans zpf zp
      end terminates (lt a b) by lt_total join (lt a b) (lt a b) ].

Define lt_S3 : Forall(a b:nat)(u:{ (lt a b) = tt }).{ (lt a (S b)) = tt } :=
  foralli(a b:nat)(u:{ (lt a b) = tt }).
    [lt_S2 a (S b) symm trans symm u
                              join (lt a b)
                                   (lt (S a) (S b))].

Define ltff_S2 : Forall(a b:nat)(u:{ (lt a b) = ff }).{ (lt (S a) b) = ff } :=
  foralli(a b:nat)(u:{ (lt a b) = ff }).
    [ induction(z:bool) by zp zt IHz return Forall(zpf:{ (lt (S a) b) = z }).{ (lt (S a) b) = ff } with
        ff =>
          foralli(zpf:{ (lt (S a) b) = z }).
            trans zpf zp
      | tt =>
          foralli(zpf:{ (lt (S a) b) = z }).
            contra trans symm [lt_S2 a b trans zpf zp]
                   trans u
                         clash ff tt
              { (lt (S a) b) = ff }
      end terminates (lt (S a) b) by lt_total
          join (lt (S a) b) (lt (S a) b) ].

Define ltff_S3 : Forall(a b:nat)(u:{ (lt a (S b)) = ff }).{ (lt a b) = ff } :=
  foralli(a b:nat)(u:{ (lt a (S b)) = ff }).
    symm trans symm [ltff_S2 a (S b) u]
               join (lt (S a) (S b))
                    (lt a b).

Define eqnatDef2 : Forall(a b:nat)(u:{(eqnat a b) = ff}).{ a != b} :=
	induction(a:nat) by x1 x2 IH return Forall(b:nat)(u:{(eqnat a b) = ff}).{ a != b} with
		Z=> induction(b:nat) by y1 y2 IH2 return Forall(u:{(eqnat a b) = ff}).{ a != b} with
			Z=> foralli(u:{(eqnat a b) = ff}).
				contra trans symm u trans cong (eqnat a *) trans y1 symm x1 trans [x_eqnat_x a] clash tt ff
				{ a != b}
			| S b'=> foralli(u:{(eqnat a b) = ff}).
				symm trans y1 symm trans x1  clash Z (S b')  
				end
		| S a'=>induction(b:nat) by y1 y2 IH2 return Forall(u:{(eqnat a b) = ff}).{ a != b} with
			Z=> foralli(u:{(eqnat a b) = ff}).
				symm trans y1 symm trans x1 clash (S a') Z
			| S b'=> foralli(u:{(eqnat a b) = ff}).
				 symm trans y1
				 symm trans  x1
				ncong (S *) (S a') (S b')
				 [IH a' b'
				trans join (eqnat a' b') (eqnat (S a') (S b'))
				trans cong (eqnat (S a') *) symm y1
				 trans cong (eqnat * b) symm x1
				 u]
			end
	end.

Define lt_Z : Forall(a:nat).{ (lt a Z) = ff } :=
	induction(a:nat) by x1 x2 IH return {(lt a Z) = ff} with
	Z => trans cong (lt * Z) x1
		join (lt Z Z) ff
	| S a' => trans cong (lt * Z) x1
		join (lt (S a') Z) ff
	end.

Define lt_ltff : Forall(a b:nat)(u:{ (lt a b) = tt }).{ (lt b a) = ff }
  :=
  induction(a b:nat) return Forall(u:{ (lt a b) = tt }).{ (lt b a) = ff }
  with
    Z =>
      foralli(u:{ (lt a b) = tt }).
      contra
      trans symm u
      trans hypjoin (lt a b) ff by [lt_Z a] b_eq end
            clash ff tt
      { (lt b a) = ff }
  | S b' =>
      foralli(u:{ (lt a b) = tt }).
      case a with
        Z => hypjoin (lt b a) ff by [lt_Z b] a_eq end
      | S a' =>
          abbrev u' = hypjoin (lt a' b') tt by u a_eq b_eq end in
          abbrev p1 = [b_IH a' b' u'] in
          hypjoin (lt b a) ff by p1 a_eq b_eq end
      end
  end.

Define lt_lt_impliesEq: Forall(x y:nat)(u: {(lt x y) = ff})(v:{(lt y x) = ff}).{x = y} :=
   induction(x:nat) return Forall(y:nat)(u: {(lt x y) = ff})(v:{(lt y x) = ff}).{x = y} with
	     Z => induction (y:nat) return Forall(u: {(lt x y) = ff})(v:{(lt y x) = ff}).{x = y} with
			
		     Z => foralli(u: {(lt x y) = ff})(v:{(lt y x) = ff}).
			    hypjoin x y by x_eq y_eq end
		   | S y' => foralli(u: {(lt x y) = ff})(v:{(lt y x) = ff}). 
			    contra
			    trans symm u
			    trans hypjoin (lt x y) tt by x_eq y_eq end
			    clash tt ff
			    {x = y}
		   end
	   | S x' => induction (y:nat) return Forall(u: {(lt x y) = ff})(v:{(lt y x) = ff}).{x = y} with
		     Z => foralli(u: {(lt x y) = ff})(v:{(lt y x) = ff}).
			  contra
			  trans symm v
			  trans hypjoin (lt y x) tt by x_eq y_eq end
		 	  clash tt ff
			  {x = y}
		   | S y' => foralli(u: {(lt x y) = ff})(v:{(lt y x) = ff}). 
			  
			  abbrev u' = hypjoin (lt x' y') ff by u v x_eq y_eq end in
			  abbrev v' = hypjoin (lt y' x') ff by u v x_eq y_eq end in
			  
			  
			  abbrev w = hypjoin (S x') (S y') by [x_IH x' y' u' v'] end in
			  hypjoin x y by x_eq y_eq w end
			 			 
			 
		   end
	   end.

Define x_lt_SZ_implies_Z: Forall(x:nat)(u:{(lt x (S Z)) = tt}).{x = Z} :=
   induction(x:nat) return Forall(u:{(lt x (S Z)) = tt}).{x = Z} with
	Z => foralli(u:{(lt x (S Z)) = tt}).
	     x_eq
      | S x' => foralli(u:{(lt x (S Z)) = tt}).
		contra
		trans symm u
		trans cong (lt * (S Z)) x_eq
		trans hypjoin (lt (S x') (S Z)) (lt x' Z) by x_eq end
		trans hypjoin (lt x' Z) ff by [lt_Z x'] end
		clash ff tt
		{x = Z}
		
      end.

Define x_lt_y_SxNEQy_Sx_lt_y : Forall(x y :nat)(u: {(lt x y) = tt})(v: {(eqnat (S x) y) = ff}).
      {(lt (S x) y) = tt} :=
	  induction(x:nat) return Forall(y:nat)(u: {(lt x y) = tt})(v: {(eqnat (S x) y) = ff}).{(lt (S x) y) = tt} with
		Z => foralli(y:nat)(u: {(lt x y) = tt})(v: {(eqnat (S x) y) = ff}).
			case terminates (lt (S x) y) by lt_total by ltp ltt with
			  ff => case terminates (lt y (S x)) by lt_total by ltp2 ltt2 with
				  ff => contra
					abbrev w = hypjoin y (S x) by [lt_lt_impliesEq y (S x) ltp2 ltp] end in
					trans symm hypjoin (eqnat (S x) y) tt by [eqnat_symm y (S x)] [eqEqnat y (S x) w] end
					trans hypjoin (eqnat (S x) y) ff by v end
					clash ff tt
					{(lt (S x) y) = tt}
					
				| tt => contra
					 trans symm u 
					 abbrev u' = hypjoin (lt y (S Z)) tt by x_eq ltp2 end in
					 abbrev yeq = hypjoin y Z by [x_lt_SZ_implies_Z y u' ] end in
					 trans hypjoin (lt x y) ff by yeq x_eq end
					clash ff tt
					{(lt (S x) y) = tt}
				end
			| tt => hypjoin (lt (S x) y) tt by ltp end
			end
	      | S x' => foralli(y:nat)(u: {(lt x y) = tt})(v: {(eqnat (S x) y) = ff}).
			case terminates (lt (S x) y) by lt_total by ltp ltt with
			  ff => case terminates (lt y (S x)) by lt_total by ltp2' ltt2' with
				   ff => contra
					 abbrev w' = hypjoin y (S x) by [lt_lt_impliesEq y (S x) ltp2' ltp] end in
					 trans symm hypjoin (eqnat (S x) y) tt by [eqnat_symm y (S x)] [eqEqnat y (S x) w'] end
					 trans hypjoin (eqnat (S x) y) ff by v end
					 clash ff tt
					 {(lt (S x) y) = tt}
				 | tt => case y with
					    Z => contra
						 trans symm u
						 trans hypjoin (lt x y) ff by x_eq y_eq end
						 clash ff tt
						 {(lt (S x) y) = tt}
					  | S y' => contra
						   abbrev u' = symm trans hypjoin tt (lt (S x') (S y')) by x_eq y_eq u end
						  			  [S_lt_S x' y'] in
						abbrev arg2 = 						
						  abbrev w =    
						    abbrev v'' =   
						      abbrev v' = hypjoin (eqnat (S (S x')) (S y')) ff by v x_eq y_eq end in
							  [eqnatDef2 (S (S x')) (S y') v'] in 
						      [Sneq_neq (S x') y' v''] in 
						    [neqEqnat (S x') y' w] in
						trans symm [x_IH x' y' u' arg2 ] 
			
						trans symm [S_lt_S (S x') y']
						trans hypjoin (lt (S (S x')) (S y')) ff by x_eq y_eq ltp end			
						clash ff tt
						{(lt (S x) y) = tt}
					  end
				 end
			| tt => hypjoin (lt (S x) y) tt by ltp end
			end
	      end.



Define le_Z1 : Forall(x:nat)(u:{(le x Z) = tt}). { x = Z} :=
  foralli(x:nat)(u:{(le x Z) = tt}).
  case x with
    Z => x_eq
  | S x' => 
    contra 
      trans symm u
      trans cong (le * Z) x_eq
      trans join (le (S x') Z) ff
            clash ff tt
    { x = Z }
  end.

Define Z_le : Forall(a:nat).{ (le Z a) = tt} :=
	induction(a:nat) by x1 x2 IH return {(le Z a) = tt} with
	Z => trans cong (le Z *) x1
		join (le Z Z) tt
	| S a'=> trans cong (le Z *) x1
		join (le Z (S a')) tt
	end.

Define le_Z : Forall(a:nat).{ (le a Z) = (eqnat a Z) } :=
  foralli(a:nat).
    trans join (le a Z)
               (or (lt a Z) (eqnat a Z))
    trans cong (or * (eqnat a Z))
               [lt_Z a]
          join (or ff (eqnat a Z))
               (eqnat a Z).

Define le_trans : Forall(a b c :nat)(u:{(le a b) = tt})(v:{(le b c) = tt}).{(le a c) = tt} :=
	induction(a:nat) by x1 y1 IH return  Forall(b c :nat)(u:{(le a b) = tt})(v:{(le b c) = tt}).{(le a c) = tt} with
	Z => foralli(b c :nat)(u:{(le a b) = tt})(v:{(le b c) = tt}).
		trans cong (le * c) x1
		[Z_le c]
	|S a' => foralli(b c :nat)(u:{(le a b) = tt})(v:{(le b c) = tt}).
		[induction(d:nat) by x2 y2 IH2 return Forall(q:{d=b}).{(le a c) = tt} with
			Z=> foralli(q:{d=b}).
				contra trans symm u trans cong (le a *) symm q trans cong (le a *) x2 trans cong (le * Z) x1 trans join (le (S a') Z) ff clash ff tt
				{(le a c) = tt}
			| S d' => foralli(q:{d=b}).
				[induction(e:nat) by x3 y3 IH3 return Forall(r:{e=c}).{(le a e)=tt} with
					Z=> foralli(r:{e=c}).
						contra trans symm v trans cong (le * c) symm q trans cong (le d *) symm r
							trans cong (le * e) x2 trans cong (le (S d') *) x3 trans join (le (S d') Z) ff
							clash ff tt
							 {(le a e)=tt}
					| S e' => foralli(r:{e=c}).
						trans cong (le * e) x1
						trans cong (le (S a') *) x3
						trans join (le (S a') (S e')) (le a' e')
						[IH a' d' e'
							trans join (le a' d') (le (S a') (S d')) trans cong (le * (S d')) symm x1
								trans cong (le a *) symm x2 trans cong (le a *) q u
							trans join (le d' e') (le (S d') (S e')) trans cong (le * (S e')) symm x2
								trans cong (le d *) symm x3 trans cong (le * e) q trans cong (le b *) r v
							]
				end c join c c]
		end b join b b]
	end.

Define S_le_S : Forall(a b:nat).{ (le (S a) (S b)) = (le a b) } :=
  foralli(a b:nat).join (le (S a) (S b)) (le a b).

Define lelt_trans : Forall(a b c:nat)(u:{ (le a b) = tt })(v:{ (lt b c) = tt }).{ (lt a c) = tt } :=
  induction(a:nat) by x1 y1 IH return  Forall(b c:nat)(u:{ (le a b) = tt })(v:{ (lt b c) = tt }).{ (lt a c) = tt } with
    Z =>
      foralli(b c:nat)(u:{ (le a b) = tt })(v:{ (lt b c) = tt }).
        trans cong (lt * c) x1
              [not_zero_implies_lt c [lt_implies_not_zero b c v]]
  | S a' =>
      foralli(b c:nat)(u:{ (le a b) = tt })(v:{ (lt b c) = tt }).
        [ induction(d:nat) by x2 y2 IH2 return Forall(q:{ d = b }).{ (lt a c) = tt } with
            Z =>
              foralli(q:{ d = b }).
                contra trans symm u trans cong (le a *) symm q trans cong (le a *) x2 trans cong (le * Z) x1 trans join (le (S a') Z) ff clash ff tt
                       { (lt a c) = tt }
          | S d' =>
              foralli(q:{ d = b }).
                [ induction(e:nat) by x3 y3 IH3 return Forall(r:{ e = c }).{ (lt a e) = tt } with
                    Z =>
                      foralli(r:{ e = c }).
                        contra trans symm v trans cong (lt * c) symm q trans cong (lt d *) symm r
                               trans cong (lt * e) x2 trans cong (lt (S d') *) x3 trans join (lt (S d') Z) ff
                                     clash ff tt
                               { (lt a e) = tt }
                  | S e' =>
                      foralli(r:{ e = c }).
                        trans cong (lt * e) x1
                        trans cong (lt (S a') *) x3
                        trans join (lt (S a') (S e')) (lt a' e')
                              [IH a' d' e'
                                  trans join (le a' d') (le (S a') (S d')) trans cong (le * (S d')) symm x1
                                        trans cong (le a *) symm x2 trans cong (le a *) q u
                                  trans join (lt d' e') (lt (S d') (S e')) trans cong (lt * (S e')) symm x2
                                        trans cong (lt d *) symm x3 trans cong (lt * e) q trans cong (lt b *) r v]
                  end c join c c ]
          end b join b b ]
  end.

Define le_nz_implies_lt_z : Forall(a b:nat)(u:{ a != Z })(v:{ (le a b) = tt }).{ (lt Z b) = tt } :=
  foralli(a:nat).
    induction(b:nat) by bp bt IHb return Forall(u:{ a != Z })(v:{ (le a b) = tt }).{ (lt Z b) = tt } with
      Z =>
        foralli(u:{ a != Z })(v:{ (le a b) = tt }).
          contra trans symm [le_Z1 a symm trans symm v cong (le a *) bp] u
                 { (lt Z b) = tt }
    | S b' =>
        foralli(u:{ a != Z })(v:{ (le a b) = tt }).
          symm trans join tt (lt Z (S b'))
                     cong (lt Z *) symm bp
    end.

Define ltle_trans : Forall(a b c:nat)(u:{ (lt a b) = tt })(v:{ (le b c) = tt }).{ (lt a c) = tt } :=
  foralli(a b c:nat)(u:{ (lt a b) = tt })(v:{ (le b c) = tt }).
    existse [or_total terminates (lt b c) by lt_total
                      terminates (eqnat b c) by eqnatTot]
      induction(o:bool) by op ot IHo return Forall(w:{ (or (lt b c) (eqnat b c)) = o }).{ (lt a c) = tt } with
        ff =>
          foralli(w:{ (or (lt b c) (eqnat b c)) = o }).
            contra trans symm trans w op
                   trans join (or (lt b c) (eqnat b c))
                              (le b c)
                   trans v
                         clash tt ff
              { (lt a c) = tt }
      | tt =>
          foralli(w:{ (or (lt b c) (eqnat b c)) = o }).
            existse [lt_total b c]
              induction(p:bool) by pp pt IHp return Forall(x:{ (lt b c) = p }).{ (lt a c) = tt } with
                ff =>
                  foralli(x:{ (lt b c) = p }).
                    symm trans symm u
                               cong (lt a *)
                                    [eqnatEq b c symm trans symm trans w op
                                                      trans cong (or * (eqnat b c)) trans x pp
                                                            join (or ff (eqnat b c))
                                                                 (eqnat b c)]
              | tt =>
                  foralli(x:{ (lt b c) = p }).
                    [lt_trans a b c u trans x pp]
              end
      end.

Define lt_implies_le : Forall(a b : nat)(u:{(lt a b) = tt}).{(le a b)= tt} :=
	foralli(a b:nat)(u:{(lt a b) = tt}).
	trans join (le a b) (or (lt a b) (eqnat a b))
		trans cong (or * (eqnat a b)) u
		join (or tt (eqnat a b)) tt.


Define le_S : Forall(a:nat). { (le a (S a)) = tt } :=
  foralli(a:nat).[lt_implies_le a (S a) [lt_S a]].

Define le_S2 : Forall(a b:nat)(u:{ (le (S a) b) = tt }).{ (le a b) = tt } :=
  foralli(a b:nat)(u:{ (le (S a) b) = tt }).
    [ induction(z:bool) by zp zt IHz return Forall(zpf:{ (le a b) = z }).{ (le a b) = tt } with
        ff =>
          foralli(zpf:{ (le a b) = z }).
            % (le a b) = ff
            abbrev lep = trans zpf zp in

            % (le (S a) (S b)) = ff
            abbrev leSSff = trans join (le (S a) (S b))
                                       (le a b)
                                  lep in

            % (le b (S b)) = tt
            abbrev leSSbtt = [lt_implies_le b (S b) [lt_S b]] in

            % (le (S a) b) = tt

            symm trans symm [le_trans (S a) b (S b) u leSSbtt]
                       [S_le_S a b]
      | tt =>
          foralli(zpf:{ (le a b) = z }).
            trans zpf zp
      end terminates (le a b) by le_total join (le a b) (le a b) ].

Define le_S3 : Forall(a b:nat)(u:{ (le a b) = tt }).{ (le a (S b)) = tt } :=
  foralli(a b:nat)(u:{ (le a b) = tt }).
    [le_S2 a (S b) symm trans symm u
                              join (le a b)
                                   (le (S a) (S b))].

Define le_S4 : Forall(a b:nat)(u:{ (le (S a) b) = tt}).
                Exists(c:nat). { b = (S c) } :=
  foralli(a b:nat)(u:{ (le (S a) b) = tt}).
    case b with
      Z => contra 
             trans 
               trans symm u
                     hypjoin (le (S a) b) ff by b_eq end
             clash ff tt
           Exists(c:nat). { b = (S c) }
    | S b' => existsi b' { b = (S *) } b_eq
    end.

Define lt_ff_implies_le : Forall (a b:nat)(u:{(lt a b) = ff}).{(le b a) = tt} :=
	induction(a:nat) by x1 x2 IH return Forall(b:nat)(u:{(lt a b) = ff}).{(le b a) = tt} with
	Z=> foralli(b:nat)(u:{(lt a b) = ff}).
		[induction(c:nat) by y1 y2 IH2 return Forall(q:{c=b}).{(le c a) = tt} with
			Z=> foralli(q:{c=b}).
				trans cong (le * a) y1
				trans cong (le Z *) x1
				join (le Z Z) tt
			|S c'=>foralli(q:{c=b}).
				contra trans symm u
					trans cong (lt a *) symm q
					trans cong (lt * c) x1
					trans cong (lt Z *) y1
					trans join (lt Z (S c')) tt
					clash tt ff
				{(le c a) = tt}
		end b join b b]

	|S a' => foralli(b:nat)(u:{(lt a b) = ff}).
		[induction(c:nat) by y1 y2 IH2 return Forall(q:{c=b}).{(le c a) = tt} with
			Z=> foralli(q:{c=b}). 
				trans cong (le * a) y1
				trans cong (le Z *) x1
				join (le Z (S a')) tt
			|S c'=>foralli(q:{c=b}). 
				trans cong (le * a) y1
				trans cong (le (S c') *) x1
				trans join (le (S c') (S a')) (le c' a')
				[IH a' c' trans join (lt a' c') (lt (S a') (S c')) trans cong (lt (S a') *) trans symm y1 q trans cong (lt * b) symm x1 u]
		end b join b b]
	end.

Define le_bounds : Forall(a b:nat)(u:{ (le a b) = tt })(v:{ (le b a) = tt }).{ a = b } :=
  induction(a:nat) by ap at IHa return Forall(b:nat)(u:{ (le a b) = tt })(v:{ (le b a) = tt }).{ a = b } with
    Z =>
      induction(b:nat) by bp bt IHb return Forall(u:{ (le a b) = tt })(v:{ (le b a) = tt }).{ a = b } with
        Z =>
          foralli(u:{ (le a b) = tt })(v:{ (le b a) = tt }).
            trans ap symm bp
      | S b' =>
          foralli(u:{ (le a b) = tt })(v:{ (le b a) = tt }).
            contra trans symm v
                   trans cong (le * a) bp
                   trans cong (le (S b') *) ap
                   trans join (le (S b') Z) ff
                         clash ff tt
              { a = b }
      end
  | S a' =>
      induction(b:nat) by bp bt IHb return Forall(u:{ (le a b) = tt })(v:{ (le b a) = tt }).{ a = b } with
        Z =>
          foralli(u:{ (le a b) = tt })(v:{ (le b a) = tt }).
            contra trans symm u
                   trans cong (le * b) ap
                   trans cong (le (S a') *) bp
                   trans join (le (S a') Z) ff
                         clash ff tt
              { a = b }
      | S b' =>
          foralli(u:{ (le a b) = tt })(v:{ (le b a) = tt }).
            abbrev u' = symm trans symm u
                             trans cong (le * b) ap
                             trans cong (le (S a') *) bp
                                   join (le (S a') (S b'))
                                        (le a' b') in
            abbrev v' = symm trans symm v
                             trans cong (le * a) bp
                             trans cong (le (S b') *) ap
                                   join (le (S b') (S a'))
                                        (le b' a') in
            trans ap
            trans cong (S *) [IHa a' b' u' v']
                  symm bp
      end
  end.

Define le_tt_implies_lt_ff : Forall(a b:nat)(u:{ (le a b) = tt }).{ (lt b a) = ff } :=
  foralli(a b:nat)(u:{ (le a b) = tt }).
    [ induction(z:bool) by zp zt IHz return Forall(zpf:{ (lt b a) = z }).{ (lt b a) = ff } with
        ff =>
          foralli(zpf:{ (lt b a) = z }).
            trans zpf zp
      | tt =>
          foralli(zpf:{ (lt b a) = z }).
            abbrev ltp = trans zpf zp in
            contra trans symm ltp
                   trans cong (lt * a) symm [le_bounds a b u [lt_implies_le b a ltp]]
                   trans [x_lt_x a]
                         clash ff tt
              { (lt b a) = ff }
      end terminates (lt b a) by lt_total
          join (lt b a) (lt b a) ].

Define le_ff_implies_lt : Forall(a b:nat)(u:{(le a b) = ff}).{(lt b a) = tt} :=
  foralli(a b:nat)(u:{(le a b) = ff}).
  abbrev p1 = hypjoin (or (lt a b) (eqnat a b)) ff by u end in
  abbrev p2 = [or_ff (lt a b) (eqnat a b) p1] in
  abbrev p2' = [lt_ff_implies_le a b p2] in  % (le b a) = tt
  abbrev p3 = [or_ffr (lt a b) (eqnat a b) p1] in
  abbrev p3' = hypjoin (eqnat b a) ff by [eqnat_symm a b] p3 end in % (eqnat b a) = ff
  abbrev p4 = hypjoin (or (lt b a) ff) tt by p2' p3' end in
  hypjoin (lt b a) tt by p4 [or_def2ff (lt b a)] end
  .

Define le_ff_implies_le : Forall (a b:nat)(u:{(le a b) = ff}).{(le b a) = tt} :=
  foralli(a b:nat)(u:{(le a b) = ff}).
    existse 
       [lt_total a b] % Exists(q:bool).{(lt a b) = q}
       foralli(p:bool)(up:{(lt a b) = p}).
          existse [eqnatTot a b]
          foralli(q:bool)(uq:{(eqnat a b) = q}).
            [lt_ff_implies_le a b 
                trans up 
                      [or_eq_ff p q
                         trans cong (or * q) symm up
                         trans cong (or (lt a b) *) symm uq   
                         trans join (or (lt a b) (eqnat a b)) (le a b)
                               u]].

Define le_not_ff_implies_tt : Forall(a b:nat)(p:{ (le a b) != ff}). { (le a b) = tt} :=
	induction(a:nat) by x1 x2 IH return Forall(b:nat)(p:{ (le a b) != ff}). { (le a b) = tt} with
	Z => foralli(b:nat)(p:{ (le a b) != ff}).
		trans cong (le * b) x1 
		[Z_le b]
	|S a' => induction(b:nat) by y1 y2 IH2 return Forall(p:{ (le a b) != ff}).{ (le a b) = tt}  with
		Z => foralli(p:{ (le a b) != ff}).
			contra trans symm trans cong (le * b) x1 trans cong (le (S a') *) y1 join (le (S a') Z) ff p
			{ (le a b) = tt} 
		| S b'=> foralli(p:{ (le a b) != ff}).
			trans cong (le * b) x1
			trans cong (le (S a') *) y1
			trans join (le (S a') (S b')) (or (lt (S a') (S b')) (eqnat (S a') (S b')))
			trans cong (or (lt (S a') (S b')) *) join (eqnat (S a') (S b')) (eqnat a' b')
			trans cong (or * (eqnat a' b')) join (lt (S a') (S b')) (lt a' b')
			trans join (or (lt a' b') (eqnat a' b')) (le a' b')
			[IH a' b' trans join (le a' b') (le (S a') (S b')) trans cong (le * (S b')) symm x1 trans cong (le a *) symm y1 p]
		end
	end.

Define lt_pred : Forall(x y z:nat)(u:{ y = (S x) })(v:{ (lt z y) = tt }).{ (le z x) = tt } :=
  induction(x:nat) by xp xt IHx return Forall(y z:nat)(u:{ y = (S x) })(v:{ (lt z y) = tt }).{ (le z x) = tt } with
    Z =>
      foralli(y:nat).
        induction(z:nat) by zp zt IHz return Forall(u:{ y = (S x) })(v:{ (lt z y) = tt }).{ (le z x) = tt } with
          Z =>
            foralli(u:{ y = (S x) })(v:{ (lt z y) = tt }).
              symm trans symm [Z_le x]
                         cong (le * x) symm zp
        | S z' =>
            foralli(u:{ y = (S x) })(v:{ (lt z y) = tt }).
              contra trans symm v
                     trans cong (lt * y) zp
                     trans cong (lt (S z') *)
                                trans u
                                      cong (S *) xp
                     trans [S_lt_S z' Z]
                     trans [lt_Z z']
                           clash ff tt
                { (le z x) = tt }
        end
  | S x' =>
      induction(y:nat) by yp yt IHy return Forall(z:nat)(u:{ y = (S x) })(v:{ (lt z y) = tt }).{ (le z x) = tt } with
        Z =>
          foralli(z:nat)(u:{ y = (S x) })(v:{ (lt z y) = tt }).
            contra trans symm yp
                   trans u
                         [S_not_zero x]
              { (le z x) = tt }
      | S y' =>
          induction(z:nat) by zp zt IHz return Forall(u:{ y = (S x) })(v:{ (lt z y) = tt }).{ (le z x) = tt } with
            Z =>
              foralli(u:{ y = (S x) })(v:{ (lt z y) = tt }).
                symm trans symm [Z_le x]
                           cong (le * x) symm zp
          | S z' =>
              foralli(u:{ y = (S x) })(v:{ (lt z y) = tt }).
                abbrev u' = inj (S *)
                                trans symm yp
                                trans u
                                      cong (S *) xp in
                abbrev v' = symm trans symm v
                                 trans cong (lt * y) zp
                                 trans cong (lt (S z') *) yp
                                       join (lt (S z') (S y'))
                                            (lt z' y') in
                trans cong (le * x) zp
                trans cong (le (S z') *) xp
                trans join (le (S z') (S x'))
                           (le z' x')
                      [IHx x' y' z' u' v']
          end
      end
  end.

Define lt_pred2 : Forall(x y:nat)(u:{ (lt x (S y)) = tt }).{ (le x y) = tt }
	:=
	foralli(x y:nat)(u:{ (lt x (S y)) = tt }).
	abbrev sy_eq = refl (S y) in
	[lt_pred y (S y) x sy_eq u]
	.

Define le_eq_lt_S : Forall(x y:nat).{ (le x y) = (lt x (S y)) }
	:=
	foralli(x y:nat).
  case (eqnat x y) by q1 _ with
    ff =>
      % p1: (le x y) = (lt x y)
      abbrev p1 = hypjoin (le x y) (lt x y) by q1 [or_def2ff (lt x y)] end in
      case (lt x (S y)) by q2 _ with
        ff => transs p1 [ltff_S3 x y q2] symm q2 end
      | tt => trans [lt_pred2 x y q2] symm q2
      end
  | tt =>
      abbrev p1 = hypjoin (le x y) tt by q1 [or_tt (lt x y)] end in
      abbrev p2 = hypjoin (lt x (S y)) tt by [lt_S x] [eqnatEq x y q1] end in
      trans p1 symm p2
  end.

Define lt_S_le : Forall(x y:nat)(u:{(lt x y) = tt}). { (le (S x) y) = tt }
	:=
	induction(x y:nat) return
	  Forall(u:{(lt x y) = tt}).{ (le (S x) y) = tt }
	with
	  Z =>
	  	foralli(u:{(lt x y) = tt}).
	  	contra
	  		trans symm [lt_Z x]
	  		trans	hypjoin (lt x Z) tt by y_eq u end
	  					clash tt ff
	  		{ (le (S x) y) = tt }
	| S y' =>
	  	foralli(u:{(lt x y) = tt}).
			case x with
				Z => hypjoin (le (S x) y) tt by x_eq y_eq [Z_le y'] end
			| S x' =>
					abbrev u' = hypjoin (lt x' y') tt by u [S_lt_S x' y'] x_eq y_eq end in
					abbrev ih = [y_IH x' y' u'] in
					hypjoin (le (S x) y) tt by ih [S_le_S x' y'] x_eq y_eq end
			end
	end.

Define le_S_lt : Forall(x y:nat)(u:{(le (S x) y) = tt}). { (lt x y) = tt }
	:=
	foralli(x y:nat)(u:{(le (S x) y) = tt}).
	[ltle_trans x (S x) y [lt_S x] u].  

Define ltff_le : Forall(a b:nat)(u:{ (lt a b) = ff }).{ (le b a) = tt } :=
  induction(a:nat) by ap at IHa return Forall(b:nat)(u:{ (lt a b) = ff }).{ (le b a) = tt } with
    Z =>
      induction(b:nat) by bp bt IHb return Forall(u:{ (lt a b) = ff }).{ (le b a) = tt } with
        Z =>
          foralli(u:{ (lt a b) = ff }).
          trans cong (le b *) ap
          trans cong (le * Z) bp
                join (le Z Z)
                     tt
      | S b' =>
          foralli(u:{ (lt a b) = ff }).
            contra trans join tt
                              (lt Z (S b'))
                   trans cong (lt * (S b')) symm ap
                   trans cong (lt a *) symm bp
                   trans u
                         clash ff tt
              { (le b a) = tt }
      end
  | S a' =>
      induction(b:nat) by bp bt IHb return Forall(u:{ (lt a b) = ff }).{ (le b a) = tt } with
        Z =>
          foralli(u:{ (lt a b) = ff }).
            symm trans symm [Z_le a]
                       cong (le * a)
                            symm bp
      | S b' =>
          foralli(u:{ (lt a b) = ff }).
            abbrev u' = symm trans symm u
                                   cong (lt a *) bp in
            [ induction(z:bool) by zp zt IHz return Forall(zpf:{ (eqnat b' a) = z }).{ (le b a) = tt } with
                ff =>
                  foralli(zpf:{ (eqnat b' a) = z }).
                    abbrev lt_b'_a = symm trans symm [IHb b' [ltff_S3 a b' u']]
                                          trans join (le b' a)
                                                     (or (lt b' a) (eqnat b' a))
                                          trans cong (or (lt b' a) *)
                                                     trans zpf zp
                                                [or_def2ff terminates (lt b' a) by lt_total] in

                    symm trans symm [lt_pred a' a b' ap lt_b'_a]
                         trans join (le b' a')
                                    (le (S b') (S a'))
                         trans cong (le * (S a')) symm bp
                               cong (le b *) symm ap
              | tt =>
                  foralli(zpf:{ (eqnat b' a) = z }).
                    contra symm trans symm [lt_S b']
                                trans cong (lt b' *)
                                           symm bp
                                trans cong (lt * b)
                                           [eqnatEq b' a trans zpf zp]
                                trans u
                                      clash ff tt
                      { (le b a) = tt }
              end terminates (eqnat b' a) by eqnatTot
                  join (eqnat b' a) (eqnat b' a) ]
    end
  end.

Define neq_implies_ltgt : Forall(a b:nat)(u:{ a != b }).{ (or (lt a b) (lt b a)) = tt } :=
  induction(a:nat) by ap at IHa return Forall(b:nat)(u:{ a != b }).{ (or (lt a b) (lt b a)) = tt } with
    Z =>
      induction(b:nat) by bp bt IHb return Forall(u:{ a != b }).{ (or (lt a b) (lt b a)) = tt } with
        Z =>
          foralli(u:{ a != b }).
            contra trans ap
                   trans symm bp
                         symm u
              { (or (lt a b) (lt b a)) = tt }
      | S b' =>
          foralli(u:{ a != b }).
            abbrev lt_a_b = symm trans cong (lt * b) ap
                                 trans cong (lt Z *) bp
                                       join (lt Z (S b'))
                                            tt in
            trans cong (or * (lt b a))
                       symm lt_a_b
                  join (or tt (lt b a))
                       tt
      end
  | S a' =>
      induction(b:nat) by bp bt IHb return Forall(u:{ a != b }).{ (or (lt a b) (lt b a)) = tt } with
        Z =>
          foralli(u:{ a != b }).
            abbrev lt_b_a = symm trans cong (lt b *) ap
                                 trans cong (lt * (S a')) bp
                                       join (lt Z (S a'))
                                            tt in
            trans cong (or (lt a b) *)
                       symm lt_b_a
                  [or_def2 terminates (lt a b) by lt_total]
      | S b' =>
          foralli(u:{ a != b }).
            abbrev a'_not_b' = [Sneq_neq a' b'
                                         trans symm ap
                                               symm trans symm bp
                                                          symm u] in
            abbrev or_ih = [IHa a' b' a'_not_b'] in
            [ induction(z:bool) by zp zt IHz return Forall(zpf:{ (lt a' b') = z }).{ (or (lt a b) (lt b a)) = tt } with
                ff =>
                  foralli(zpf:{ (lt a' b') = z }).
                    abbrev lt_a'_b'_ff = trans zpf zp in
                    abbrev lt_b'_a' = symm trans symm or_ih
                                           trans cong (or * (lt b' a'))
                                                      lt_a'_b'_ff
                                                 join (or ff (lt b' a'))
                                                      (lt b' a') in
                    abbrev lt_b_a = symm trans symm lt_b'_a'
                                         trans symm [S_lt_S b' a']
                                         trans cong (lt * (S a')) symm bp
                                               cong (lt b *) symm ap in
                    trans cong (or (lt a b) *)
                               lt_b_a
                          [or_def2 terminates (lt a b) by lt_total]
              | tt =>
                  foralli(zpf:{ (lt a' b') = z }).
                    abbrev lt_a'_b' = trans zpf zp in
                    abbrev lt_a_b = symm trans symm lt_a'_b'
                                         trans symm [S_lt_S a' b']
                                         trans cong (lt * (S b')) symm ap
                                               cong (lt a *) symm bp in
                    trans cong (or * (lt b a))
                               lt_a_b
                          join (or tt (lt b a))
                               tt
              end terminates (lt a' b') by lt_total
                  join (lt a' b') (lt a' b') ]
      end
  end.

Define ltltS_contra : Forall(a b:nat)(u:{ (lt a b) = tt })(v:{ (lt b (S a)) = tt }).{ tt != tt } :=
  induction(a:nat) by ap at IHa return Forall(b:nat)(u:{ (lt a b) = tt })(v:{ (lt b (S a)) = tt }).{ tt != tt } with
    Z =>
      induction(b:nat) by bp bt IHb return Forall(u:{ (lt a b) = tt })(v:{ (lt b (S a)) = tt }).{ tt != tt } with
        Z =>
          foralli(u:{ (lt a b) = tt })(v:{ (lt b (S a)) = tt }).
            trans symm u
            trans cong (lt a *) bp
            trans [lt_Z a]
                  clash ff tt
      | S b' =>
          foralli(u:{ (lt a b) = tt })(v:{ (lt b (S a)) = tt }).
            symm trans symm v
                 trans cong (lt * (S a)) bp
                 trans cong (lt (S b') (S *)) ap
                 trans join (lt (S b') (S Z))
                            (lt b' Z)
                 trans [lt_Z b']
                       clash ff tt
      end
  | S a' =>
      induction(b:nat) by bp bt IHb return Forall(u:{ (lt a b) = tt })(v:{ (lt b (S a)) = tt }).{ tt != tt } with
        Z =>
          foralli(u:{ (lt a b) = tt })(v:{ (lt b (S a)) = tt }).
            trans symm u
            trans cong (lt a *) bp
            trans [lt_Z a]
                  clash ff tt
      | S b' =>
          foralli(u:{ (lt a b) = tt })(v:{ (lt b (S a)) = tt }).
            abbrev u' = trans join (lt a' b')
                                   (lt (S a') (S b'))
                        trans cong (lt * (S b')) symm ap
                        trans cong (lt a *) symm bp
                              u in
            abbrev v' = trans join (lt b' (S a'))
                                   (lt (S b') (S (S a')))
                        trans cong (lt * (S (S a'))) symm bp
                        trans cong (lt b (S *)) symm ap
                              v in
            [IHa a' b' u' v']
      end
  end.

Define ltltSS : Forall(a b:nat)(u:{ (lt a b) = tt })(v:{ (lt b (S (S a))) = tt }).{ b = (S a) } :=
  foralli(a b:nat)(u:{ (lt a b) = tt })(v:{ (lt b (S (S a))) = tt }).
    [ induction(z:bool) by zp zt IHz return Forall(zpf:{ (eqnat b (S a)) = z }).{ b = (S a) } with
        ff =>
          foralli(zpf:{ (eqnat b (S a)) = z }).
            abbrev b_not_Sa = [eqnatNeq b (S a) trans zpf zp] in
            [ induction(zz:bool) by zzp zzt IHzz return Forall(zzpf:{ (lt b (S a)) = zz }).{ b = (S a) } with
                ff =>
                  foralli(zzpf:{ (lt b (S a)) = zz }).
                    abbrev zlt_ff = trans zzpf zzp in

                    % (lt (S a) b) = tt
                    abbrev lt_Sa_b = symm trans symm [neq_implies_ltgt b (S a) [eqnatNeq b (S a) trans zpf zp]]
                                          trans cong (or * (lt (S a) b))
                                                     zlt_ff
                                                join (or ff (lt (S a) b))
                                                     (lt (S a) b) in

                    contra [ltltS_contra (S a) b lt_Sa_b v]
                      { b = (S a) }
              | tt =>
                  foralli(zzpf:{ (lt b (S a)) = zz }).
                    abbrev zlt = trans zzpf zzp in
                    contra [ltltS_contra a b u zlt]
                      { b = (S a) }
              end terminates (lt b (S a)) by lt_total
                  join (lt b (S a)) (lt b (S a)) ]
      | tt =>
          foralli(zpf:{ (eqnat b (S a)) = z }).
            [eqnatEq b (S a) trans zpf zp]
      end terminates (eqnat b (S a)) by eqnatTot
          join (eqnat b (S a)) (eqnat b (S a)) ].

Define eq_le : Forall(x y:nat)(u:{ x = y }).{ (le x y) = tt } :=
  foralli(x y:nat)(u:{ x = y }).
    [ induction(z:bool) by zp zt IHz return Forall(zpf:{ (le x y) = z }).{ (le x y) = tt } with
        ff =>
          foralli(zpf:{ (le x y) = z }).
            trans join (le x y)
                       (or (lt x y) (eqnat x y))
            trans cong (or (lt x y) *)
                       [eqEqnat x y u]
                  [or_def2 terminates (lt x y) by lt_total]
      | tt =>
          foralli(zpf:{ (le x y) = z }).
            trans zpf zp
      end terminates (le x y) by le_total
          join (le x y) (le x y) ].

Define eqnat_le : Forall(x y:nat)(u:{ (eqnat x y) = tt }).{ (le x y) = tt } :=
  foralli(x y:nat)(u:{ (eqnat x y) = tt }).
    [eq_le x y [eqnatEq x y u]].

Define eqnat_implies_le := eqnat_le.

Define eqnat_ff_implies_neq :
	Forall(x y:nat)(u:{(eqnat x y) = ff}).{ x != y }
	:=
 foralli(x y:nat)(u:{(eqnat x y) = ff}).
   diseqi foralli(v:{x = y}).
           contra
             transs symm u
                    cong (eqnat * y) v
                    [eqnat_refl y]
                    clash tt ff
             end
           False.

Define trusted eqnat_ff_implies_lt :
	Forall(x y:nat)(u:{(eqnat x y) = ff})(v:{(le x y) = tt}). {(lt x y) = tt}
	:= truei.

Define neq_Z_implies_lt :
	Forall(x:nat)(u:{ x != Z }).{ (lt Z x) = tt }
	:=
	foralli(x:nat)(u:{ x != Z }).
	case x with
	  Z => contra trans symm x_eq u { (lt Z x) = tt }
	| S x' =>
			abbrev p1 = [Z_le x'] in
			abbrev p2 = hypjoin (lt x' x) tt by x_eq [lt_S x'] end in
			[lelt_trans Z x' x p1 p2]
	end.

Define lt_ff_neq_implies_lt :
	Forall(x y:nat)(u1:{ (lt x y) = ff })(u2:{ x != y }).
		{ (lt y x) = tt }
	:=
	induction(x y:nat) return
		Forall(u1:{ (lt x y) = ff })(u2:{ x != y }).{ (lt y x) = tt }
	with
		Z =>
			foralli(u1:{ (lt x y) = ff })(u2:{ x != y }).
			abbrev u2' = symm trans symm y_eq symm u2 in
			abbrev p1 = [neq_Z_implies_lt x u2'] in
			hypjoin (lt y x) tt by p1 y_eq end
	| S y' =>
			foralli(u1:{ (lt x y) = ff })(u2:{ x != y }).
			case x with
				Z =>
					contra
						trans symm hypjoin (lt x y) tt by x_eq y_eq end
					  trans u1
					  			clash ff tt
					  { (lt y x) = tt }
			| S x' =>
					abbrev p1 = [S_lt_S x' y'] in
					abbrev u1' = hypjoin (lt x' y') ff by u1 x_eq y_eq p1 end in
					abbrev p2 = symm
											trans symm y_eq
														symm trans symm x_eq u2 % (S x') != y
											in
					abbrev u2' = [Sneq_neq x' y' p2] in
					trans hypjoin (lt y x) (lt (S y') (S x')) by x_eq y_eq end
					trans [S_lt_S y' x']
								[y_IH x' y' u1' u2']
			end
	end.

Define nat_comp := (comparator1 nat lt eqnat).

Define S_implies_not_zero : Forall(n n':nat)(u: {n = (S n')}).{n != Z} :=
	foralli(n n':nat)(u: {n = (S n')}).
	[lt_implies_not_zero n' n trans cong (lt n' *) u [lt_S n']].
