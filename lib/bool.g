Inductive bool : type :=
  ff : bool
| tt : bool.

Define or :=
	fun(x y :bool).
	match x return bool with
	ff => y
	| tt => tt
	end.

Define and :=
	fun(x y : bool).
	match x return bool with
	ff => ff
	| tt => y
	end.

Define and3 :=
	fun(x y z : bool).
        (and x (and y z)).

Define not :=
  fun(x:bool).
    match x return bool with
      ff => tt
    | tt => ff
    end.

Define xor :=
	fun(x y :bool).
	match x return bool with
	ff => y
	| tt => (not y)
	end.

Define eqbool :=
  fun(x y:bool).
  match x return bool with
    ff => (not y)
  | tt => y
  end.

Define eqboolEq : Forall(x y:bool)(u:{ (eqbool x y) = tt }).{ x = y } :=
  induction(x:bool) by xp xt IHx return Forall(y:bool)(u:{ (eqbool x y) = tt }).{ x = y } with
    ff =>
      induction(y:bool) by yp yt IHy return Forall(u:{ (eqbool x y) = tt }).{ x = y } with
        ff =>
          foralli(u:{ (eqbool x y) = tt }).
            trans xp symm yp
      | tt =>
          foralli(u:{ (eqbool x y) = tt }).
            contra trans symm u
                   trans hypjoin (eqbool x y) ff by xp yp end
                         clash ff tt
              { x = y }
      end
  | tt =>
      induction(y:bool) by yp yt IHy return Forall(u:{ (eqbool x y) = tt }).{ x = y } with
        ff =>
          foralli(u:{ (eqbool x y) = tt }).
            contra trans symm u
                   trans hypjoin (eqbool x y) ff by xp yp end
                         clash ff tt
              { x = y }
      | tt =>
          foralli(u:{ (eqbool x y) = tt }).
            trans xp symm yp
      end
  end.

Define eqboolNeq : Forall(x y:bool)(u:{ (eqbool x y) = ff }).{ x != y } :=
  induction(x:bool) by xp xt IHx return Forall(y:bool)(u:{ (eqbool x y) = ff }).{ x != y } with
    ff =>
      induction(y:bool) by yp yt IHy return Forall(u:{ (eqbool x y) = ff }).{ x != y } with
        ff =>
          foralli(u:{ (eqbool x y) = ff }).
            contra trans symm u
                   trans hypjoin (eqbool x y) tt by xp yp end
                         clash tt ff
              { x != y }
      | tt =>
          foralli(u:{ (eqbool x y) = ff }).
            trans xp
                  symm trans yp
                             clash tt ff
      end
  | tt =>
      induction(y:bool) by yp yt IHy return Forall(u:{ (eqbool x y) = ff }).{ x != y } with
        ff =>
          foralli(u:{ (eqbool x y) = ff }).
            trans xp
                  symm trans yp
                             clash ff tt
      | tt =>
          foralli(u:{ (eqbool x y) = ff }).
            contra trans symm u
                   trans hypjoin (eqbool x y) tt by xp yp end
                         clash tt ff
              { x != y }
      end
  end.

Define eqEqbool : Forall(x y:bool)(u:{ x = y }).{ (eqbool x y) = tt } :=
  induction(x:bool) by xp xt IHx return Forall(y:bool)(u:{ x = y }).{ (eqbool x y) = tt } with
    ff =>
      induction(y:bool) by yp yt IHy return Forall(u:{ x = y }).{ (eqbool x y) = tt } with
        ff =>
          foralli(u:{ x = y }).
            hypjoin (eqbool x y) tt by xp yp end
      | tt =>
          foralli(u:{ x = y }).
            contra trans symm xp
                   trans u
                   trans yp
                         clash tt ff
              { (eqbool x y) = tt }
      end
  | tt =>
      induction(y:bool) by yp yt IHy return Forall(u:{ x = y }).{ (eqbool x y) = tt } with
        ff =>
          foralli(u:{ x = y }).
            contra trans symm xp
                   trans u
                   trans yp
                         clash ff tt
              { (eqbool x y) = tt }
      | tt =>
          foralli(u:{ x = y }).
            hypjoin (eqbool x y) tt by xp yp end
      end
  end.

Define neqEqbool : Forall(x y:bool)(u:{ x != y }).{ (eqbool x y) = ff } :=
  induction(x:bool) by xp xt IHx return Forall(y:bool)(u:{ x != y }).{ (eqbool x y) = ff } with
    ff =>
      induction(y:bool) by yp yt IHy return Forall(u:{ x != y }).{ (eqbool x y) = ff } with
        ff =>
          foralli(u:{ x != y }).
            contra trans xp
                   trans symm yp
                         symm u
              { (eqbool x y) = ff }
      | tt =>
          foralli(u:{ x != y }).
            hypjoin (eqbool x y) ff by xp yp end
      end
  | tt =>
      induction(y:bool) by yp yt IHy return Forall(u:{ x != y }).{ (eqbool x y) = ff } with
        ff =>
          foralli(u:{ x != y }).
            hypjoin (eqbool x y) ff by xp yp end
      | tt =>
          foralli(u:{ x != y }).
            contra trans xp
                   trans symm yp
                         symm u
              { (eqbool x y) = ff }
      end
  end.

Define not_total : Forall(x:bool).Exists(z:bool).{ (not x) = z } :=
  induction(x:bool) by xp xt IHx return Exists(z:bool).{ (not x) = z } with
    ff => existsi tt { (not x) = * }
                  trans cong (not *) xp
                        join (not ff) tt
  | tt => existsi ff { (not x) = * }
                  trans cong (not *) xp
                        join (not tt) ff
  end.

Define and_tot : Forall(x y:bool).Exists(z:bool). {(and x y) = z} :=
  induction(x:bool) by ux ign ign 
  return Forall(y:bool).Exists(z:bool). {(and x y) = z} with
    ff => foralli(y:bool).
          existsi ff {(and x y) = *} hypjoin (and x y) ff by ux end
  | tt => foralli(y:bool).
          existsi y {(and x y) = *} hypjoin (and x y) y by ux end
  end.
    
Total and and_tot.

Define andtt_e1 : Forall(x y:bool)(u:{ (and x y) = tt }).{ x = tt } :=
  induction(x:bool) by xp xt IHx return Forall(y:bool)(u:{ (and x y) = tt }).{ x = tt } with
    ff =>
      foralli(y:bool)(u:{ (and x y) = tt }).
        contra trans symm u
               trans cong (and * y) xp
               trans join (and ff y) ff
                     clash ff tt
          { x = tt }
  | tt =>
      foralli(y:bool)(u:{ (and x y) = tt }).
        xp
  end.

Define andtt_e2 : Forall(x y:bool)(u:{ (and x y) = tt }).{ y = tt } :=
  induction(x:bool) by xp xt IHx return Forall(y:bool)(u:{ (and x y) = tt }).{ y = tt } with
    ff =>
      foralli(y:bool)(u:{ (and x y) = tt }).
        contra trans symm u
               trans cong (and * y) xp
               trans join (and ff y) ff
                     clash ff tt
          { y = tt }
  | tt =>
      induction(y:bool) by yp yt IHy return Forall(u:{ (and x y) = tt }).{ y = tt } with
        ff =>
          foralli(u:{ (and x y) = tt }).
            contra trans symm u
                   trans cong (and * y) xp
                   trans cong (and tt *) yp
                   trans join (and tt ff) ff
                         clash ff tt
              { y = tt }
      | tt =>
          foralli(u:{ (and x y) = tt }).
            yp
      end
  end.

Define andff_i1 : Forall(x y:bool)(u:{ x = ff }).{ (and x y) = ff } :=
  foralli(x y:bool)(u:{ x = ff }).
    hypjoin (and x y)
            ff
         by u end.

Define andff_i2 : Forall(x y:bool)(u:{ y = ff }).{ (and x y) = ff } :=
  induction(x:bool) by xp xt IHx return Forall(y:bool)(u:{ y = ff }).{ (and x y) = ff } with
    ff =>
      foralli(y:bool)(u:{ y = ff }).
        hypjoin (and x y)
                ff
             by xp u end
  | tt =>
      foralli(y:bool)(u:{ y = ff }).
        hypjoin (and x y)
                ff
             by xp u end
  end.

Define and3_total : Forall(x y z:bool).Exists(zz:bool).{ (and3 x y z) = zz } :=
  foralli(x y z:bool).
    existse [and_tot y z]
      foralli(z2:bool)(z2pf:{ (and y z) = z2 }).
        existse [and_tot x z2]
          foralli(zz:bool)(zzpf:{ (and x z2) = zz }).
            existsi zz
                    { (and3 x y z) = * }
              hypjoin (and3 x y z)
                      zz
                   by symm z2pf
                      symm zzpf end.

Define and3tt_e1 : Forall(x y z:bool)(u:{ (and3 x y z) = tt }).{ x = tt } :=
  foralli(x y z:bool)(u:{ (and3 x y z) = tt }).
    [andtt_e1 x
              terminates (and y z) by and_tot
              symm trans symm u join (and3 x y z) (and x (and y z))].

Define and3tt_e2 : Forall(x y z:bool)(u:{ (and3 x y z) = tt }).{ y = tt } :=
  foralli(x y z:bool)(u:{ (and3 x y z) = tt }).
    [andtt_e1 y z [andtt_e2 x (and y z)
                            symm trans symm u join (and3 x y z) (and x (and y z))]].

Define and3tt_e3 : Forall(x y z:bool)(u:{ (and3 x y z) = tt }).{ z = tt } :=
  foralli(x y z:bool)(u:{ (and3 x y z) = tt }).
    [andtt_e2 y z [andtt_e2 x (and y z)
                            symm trans symm u join (and3 x y z) (and x (and y z))]].

Define and3tt_i : Forall(x y z:bool)(xpf:{ x = tt })(ypf:{ y = tt })(zpf:{ z = tt }).{ (and3 x y z) = tt } :=
  foralli(x y z:bool)(xpf:{ x = tt })(ypf:{ y = tt })(zpf:{ z = tt }).
    hypjoin (and3 x y z)
            tt
         by xpf ypf zpf end.

Define and3ff_i1 : Forall(x y z:bool)(u:{ x = ff }).{ (and3 x y z) = ff } :=
  foralli(x y z:bool)(u:{ x = ff }).
    hypjoin (and3 x y z)
            ff
         by u end.

Define and3ff_i2 : Forall(x y z:bool)(u:{ y = ff }).{ (and3 x y z) = ff } :=
  foralli(x y z:bool)(u:{ y = ff }).
    trans join (and3 x y z)
               (and x (and y z))
          [andff_i2 x (and y z) [andff_i1 y z u]].

Define and3ff_i3 : Forall(x y z:bool)(u:{ z = ff }).{ (and3 x y z) = ff } :=
  foralli(x y z:bool)(u:{ z = ff }).
    trans join (and3 x y z)
               (and x (and y z))
          [andff_i2 x (and y z) [andff_i2 y z u]].

Define iff :=
  fun(a b:bool).
    match a return bool with
      ff => (not b)
    | tt => b
    end.

Define or_total : Forall(x y:bool).Exists(z:bool).{(or x y) = z} :=
	induction(x:bool) by x1 x2 IH return Forall(y:bool).Exists(z:bool).{(or x y) = z} with
	 ff=> foralli(y:bool).
		existsi y {(or x y) = *}
		trans cong (or * y) x1
		join (or ff y) y
	| tt => foralli(y:bool).
		existsi tt {(or x y) = *}
		trans cong (or * y) x1
		join (or tt y) tt
	end.

Define not_tot :=
  induction(x:bool) by a b IH return Exists(y:bool).{(not x) = y} with
    ff => existsi tt {(not x) = *} hypjoin (not x) tt by a end
  | tt => existsi ff {(not x) = *} hypjoin (not x) ff by a end
  end.

Define iff_tot : Forall(x y:bool).Exists(z:bool). {(iff x y) = z} :=
  induction(x:bool) by ux ign ign 
  return Forall(y:bool).Exists(z:bool). {(iff x y) = z} with
    ff => foralli(y:bool).
          existse [not_tot y]
          foralli(r:bool)(u:{(not y) = r}).
            existsi r {(iff x y) = *}
              trans cong (iff * y) ux
              trans join (iff ff y) (not y)
                    u
  | tt => foralli(y:bool).
          existsi y {(iff x y) = *} hypjoin (iff x y) y by ux end
  end.

Define not_tt : Forall(x:bool)(u:{(not x) = tt}). {x = ff} :=
  induction(x:bool) by ux ign ign
  return Forall(u:{(not x) = tt}). {x = ff} with
    ff => foralli(u:{(not x) = tt}).ux
  | tt => foralli(u:{(not x) = tt}).
          contra
            trans
              trans symm u
              trans cong (not *) ux
                    join (not tt) ff
              clash ff tt
          { x = ff }
  end.
            
Define iff_eq : Forall(x y : bool)(u:{(iff x y) = tt}). { x = y } :=
  induction(x:bool) by ux ign ign 
  return Forall(y : bool)(u:{(iff x y) = tt}). { x = y } with
    ff => foralli(y : bool)(u:{(iff x y) = tt}).
          trans ux
                symm [not_tt y
                        symm trans symm u
                                   hypjoin (iff x y) (not y) by ux end]
  | tt => foralli(y : bool)(u:{(iff x y) = tt}).
          trans ux
                trans symm u
                      hypjoin (iff x y) y by ux end
  end.                

Define iff_refl : Forall(x:bool). {(iff x x) = tt} :=
  foralli(x:bool).
  case x with
    default bool => hypjoin (iff x x) tt by x_eq end
  end.

Define and_eq_tt1 : Forall(x y:bool)(u:{(and x y) = tt}).{x = tt} :=
  induction(x:bool) by ux ign ign 
  return Forall(y:bool)(u:{(and x y) = tt}).{x = tt} with
    ff => foralli(y:bool)(u:{(and x y) = tt}).
          contra
            trans
              trans symm u 
                    hypjoin (and x y) ff by ux end
              clash ff tt
          { x = tt }
 | tt => foralli(y:bool)(u:{(and x y) = tt}).
           ux
 end.

Define and_eq_tt2 : Forall(x y:bool)(u:{(and x y) = tt}).{y = tt} :=
  induction(x:bool) by ux ign ign 
  return Forall(y:bool)(u:{(and x y) = tt}).{y = tt} with
    ff => foralli(y:bool)(u:{(and x y) = tt}).
          contra
            trans
              trans symm u 
                    hypjoin (and x y) ff by ux end
              clash ff tt
          { y = tt }
 | tt => foralli(y:bool)(u:{(and x y) = tt}).
           symm trans symm u 
                      hypjoin (and x y) y by ux end
                 
 end.

Define or_tt : Forall(x : bool). {(or x tt) = tt} :=
	induction(x:bool) by x1 x2 IH return {(or x tt) = tt} with
	ff => trans cong (or * tt) x1
		join (or ff tt) tt
	| tt => trans cong (or * tt) x1
		join (or tt tt) tt
	end.

Define or_def2 := or_tt.

Define or_def2ff : Forall(x:bool).{ (or x ff) = x } :=
  induction(x:bool) by xp xt IHx return { (or x ff) = x } with
    ff =>
      trans cong (or * ff) xp
      trans join (or ff ff) ff
            symm xp
  | tt =>
      trans cong (or * ff) xp
      trans join (or tt ff) tt
            symm xp
  end.

Define or_eq_ff : Forall(x y: bool)(u:{(or x y) = ff}).{x = ff} :=
  induction(x:bool) by x1 x2 nIH return Forall(y: bool)(u:{(or x y) = ff}).{x = ff}
  with
  ff => foralli(y:bool)(u:{(or x y) = ff}).
           x1
 | tt => foralli(y: bool)(u:{(or x y) = ff}).
          contra
            trans symm u
            trans cong (or * y) x1
            trans join (or tt y) tt
                  clash tt ff
          {x = ff}
end.

Define or_ff := or_eq_ff.	

Define ortt_i1 : Forall(x y:bool)(u:{ x = tt }).{ (or x y) = tt } :=
  foralli(x y:bool)(u:{ x = tt }).
    hypjoin (or x y)
            tt
         by u end.

Define ortt_i2 : Forall(x y:bool)(u:{ y = tt }).{ (or x y) = tt } :=
  foralli(x y:bool)(u:{ y = tt }).
    hypjoin (or x y)
            tt
         by u [or_def2 x] end.

Define orff_i : Forall(x y:bool)(xpf:{ x = ff })(ypf:{ y = ff }).{ (or x y) = ff } :=
  foralli(x y:bool)(xpf:{ x = ff })(ypf:{ y = ff }).
    hypjoin (or x y)
            ff
         by xpf ypf end.

Define or_comm : Forall(x y:bool).{ (or x y) = (or y x) } :=
  induction(x:bool) by xp xt IHx return Forall(y:bool).{ (or x y) = (or y x) } with
    ff =>
      foralli(y:bool).
        trans cong (or * y) xp
        trans join (or ff y) y
        trans symm [or_def2ff y]
              cong (or y *) symm xp
  | tt =>
      foralli(y:bool).
        trans cong (or * y) xp
        trans join (or tt y) tt
        trans symm [or_def2 y]
              cong (or y *) symm xp
  end.

Define or_assoc : Forall(x y z:bool).{ (or (or x y) z) = (or x (or y z)) } :=
  induction(x:bool) by xp xt IHx return Forall(y z:bool).{ (or (or x y) z) = (or x (or y z)) } with
    ff =>
      foralli(y z:bool).
        hypjoin (or (or x y) z)
                (or x (or y z))
             by xp end
  | tt =>
      foralli(y z:bool).
        hypjoin (or (or x y) z)
                (or x (or y z))
             by xp end
  end.

Define or_ffr : Forall(x y: bool)(u:{(or x y) = ff}).{y = ff} :=
  foralli(x y:bool)(u:{(or x y) = ff}).
    [or_ff y x trans [or_comm y x] u].

Define xor_total : Forall(x y:bool).Exists(z:bool).{ (xor x y) = z } :=
  induction(x:bool) by xp xt IHx return Forall(y:bool).Exists(z:bool).{ (xor x y) = z } with
    ff =>
      foralli(y:bool).
        existsi y
                { (xor x y) = * }
          hypjoin (xor x y)
                  y
               by xp end
  | tt =>
      foralli(y:bool).
        existse [not_total y]
          foralli(z:bool)(zpf:{ (not y) = z }).
            existsi z
                    { (xor x y) = * }
              hypjoin (xor x y)
                      z
                   by xp zpf end
  end.

Define xortt_implies_or : Forall(x y:bool)(u:{ (xor x y) = tt }).{ (or x y) = tt } :=
  induction(x:bool) by xp xt IHx return Forall(y:bool)(u:{ (xor x y) = tt }).{ (or x y) = tt } with
    ff =>
      induction(y:bool) by yp yt IHy return Forall(u:{ (xor x y) = tt }).{ (or x y) = tt } with
        ff =>
          foralli(u:{ (xor x y) = tt }).
            contra trans symm u
                   trans hypjoin (xor x y)
                                 ff
                              by xp yp end
                         clash ff tt
              { (or x y) = tt }
      | tt =>
          foralli(u:{ (xor x y) = tt }).
            hypjoin (or x y)
                    tt
                 by xp yp end
      end
  | tt =>
      foralli(y:bool)(u:{ (xor x y) = tt }).
        hypjoin (or x y)
                tt
             by xp end
  end.

Define xorff_eq : Forall(x y:bool)(u:{ (xor x y) = ff }).{ x = y } :=
  induction(x:bool) by xp xt IHx return Forall(y:bool)(u:{ (xor x y) = ff }).{ x = y } with
    ff =>
      induction(y:bool) by yp yt IHy return Forall(u:{ (xor x y) = ff }).{ x = y } with
        ff =>
          foralli(u:{ (xor x y) = ff }).
            trans xp symm yp
      | tt =>
          foralli(u:{ (xor x y) = ff }).
            contra trans symm u
                   trans hypjoin (xor x y)
                                 tt
                              by xp yp end
                         clash tt ff
              { x = y }
      end
  | tt =>
      induction(y:bool) by yp yt IHy return Forall(u:{ (xor x y) = ff }).{ x = y } with
        ff =>
          foralli(u:{ (xor x y) = ff }).
            contra trans symm u
                   trans hypjoin (xor x y)
                                 tt
                              by xp yp end
                         clash tt ff
              { x = y }
      | tt =>
          foralli(u:{ (xor x y) = ff }).
            trans xp symm yp
      end
  end.

Define eq_xorff : Forall(x y:bool)(u:{ x = y }).{ (xor x y) = ff } :=
  induction(x:bool) by xp xt IHx return Forall(y:bool)(u:{ x = y }).{ (xor x y) = ff } with
    ff =>
      induction(y:bool) by yp yt IHy return Forall(u:{ x = y }).{ (xor x y) = ff } with
        ff =>
          foralli(u:{ x = y }).
            hypjoin (xor x y)
                    ff
                 by xp yp end
      | tt =>
          foralli(u:{ x = y }).
            contra trans symm xp
                   trans u
                   trans yp
                         clash tt ff
              { (xor x y) = ff }
      end
  | tt =>
      induction(y:bool) by yp yt IHy return Forall(u:{ x = y }).{ (xor x y) = ff } with
        ff =>
          foralli(u:{ x = y }).
            contra trans symm xp
                   trans u
                   trans yp
                         clash ff tt
              { (xor x y) = ff }
      | tt =>
          foralli(u:{ x = y }).
            hypjoin (xor x y)
                    ff
                 by xp yp end
      end
  end.

Define not_and : Forall(x y:bool).{ (not (and x y)) = (or (not x) (not y)) } :=
   induction(x:bool) by xp xt IHx return Forall(y:bool).{ (not (and x y)) = (or (not x) (not y)) } with
     ff =>
       foralli(y:bool).
         trans cong (not (and * y)) xp
         trans join (not (and ff y)) (or (not ff) (not y))
               cong (or (not *) (not y)) symm xp
   | tt =>
       foralli(y:bool).
         trans cong (not (and * y)) xp
         trans join (not (and tt y)) (or (not tt) (not y))
               cong (or (not *) (not y)) symm xp
   end.

Define not_or : Forall(x y:bool).{ (not (or x y)) = (and (not x) (not y)) } :=
   induction(x:bool) by xp xt IHx return Forall(y:bool).{ (not (or x y)) = (and (not x) (not y)) } with
     ff =>
       foralli(y:bool).
         trans cong (not (or * y)) xp
         trans join (not (or ff y)) (and (not ff) (not y))
               cong (and (not *) (not y)) symm xp
   | tt =>
       foralli(y:bool).
         trans cong (not (or * y)) xp
         trans join (not (or tt y)) (and (not tt) (not y))
               cong (and (not *) (not y)) symm xp
   end.

Define implies : Fun(x y:bool).bool :=
  fun(x y:bool).
    (or (not x) y).

Define implies_total : Forall(x y:bool).Exists(z:bool).{ (implies x y) = z } :=
  foralli(x y:bool).
    existse [or_total terminates (not x) by not_total y]
      foralli(o:bool)(u:{ (or (not x) y) = o }).
        existsi o { (implies x y) = * }
          trans join (implies x y)
                     (or (not x) y)
                u.

Define mp : Forall(x y:bool)(u:{ (implies x y) = tt })(v:{ x = tt }).{ y = tt } :=
  foralli(x y:bool)(u:{ (implies x y) = tt })(v:{ x = tt }).
    symm trans symm u
         trans cong (implies * y) v
               join (implies tt y) y.

%-

Define test := (not (and tt ff)).

Set "print_parsed".

Interpret test.

-%

