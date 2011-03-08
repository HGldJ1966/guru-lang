% Galois connection theorem
% 3/6/2011 Duckki Oe

%- summary
Galois connection has two definitions.

Def1.
	(u1:Forall(x y:D)(q:{ (ltD x y) = tt }).{ (ltE (a x) (a y)) = tt })
	(u2:Forall(x y:E)(q:{ (ltE x y) = tt }).{ (ltD (c x) (c y)) = tt })
	(u3:Forall(x:D).{ (ltD x (c (a x))) = tt })
	(u4:Forall(y:E).{ (ltE (a (c y)) y) = tt })

Def2.
  (v:Forall(x:D)(y:E).{ (ltE (a x) y) = (ltD x (c y)) })

thm1 proves Def1 implies Def2.
thm2_1 ... thm2_4 proves Def2 implies each of Def1.

More discussion comes at the bottom of this file.
-%

Include "../lib/bool.g".

Define thm1 : Forall
	% basic definitions
	(D E:type)
	(ltD:Fun(x y:D).bool)
	(ltE:Fun(x y:E).bool)
	(a:Fun(x:D).E)
	(c:Fun(y:E).D)

	(ltD_tot:Forall(x y:D).Exists(b:bool).{ (ltD x y) = b })
	(ltD_tra:Forall(x y z:D)(u:{ (ltD x y) = tt })(v:{ (ltD y z) = tt }).{ (ltD x z) = tt })
	(ltE_tot:Forall(x y:E).Exists(b:bool).{ (ltE x y) = b })
	(ltE_tra:Forall(x y z:E)(u:{ (ltE x y) = tt })(v:{ (ltE y z) = tt }).{ (ltE x z) = tt })
	(a_tot:Forall(x:D).Exists(z:E).{ (a x) = z })
	(c_tot:Forall(y:E).Exists(z:D).{ (c y) = z })
	
	% first definition
	(u1:Forall(x y:D)(q:{ (ltD x y) = tt }).{ (ltE (a x) (a y)) = tt })
	(u2:Forall(x y:E)(q:{ (ltE x y) = tt }).{ (ltD (c x) (c y)) = tt })
	(u3:Forall(x:D).{ (ltD x (c (a x))) = tt })
	(u4:Forall(y:E).{ (ltE (a (c y)) y) = tt })
	.
	
	% second definition
	Forall(x:D)(y:E)
	.{ (ltE (a x) y) = (ltD x (c y)) }
	:=
 	foralli
	% basic definitions
	(D E:type)
	(ltD:Fun(x y:D).bool)
	(ltE:Fun(x y:E).bool)
	(a:Fun(x:D).E)
	(c:Fun(y:E).D)

	(ltD_tot:Forall(x y:D).Exists(b:bool).{ (ltD x y) = b })
	(ltD_tra:Forall(x y z:D)(u:{ (ltD x y) = tt })(v:{ (ltD y z) = tt }).{ (ltD x z) = tt })
	(ltE_tot:Forall(x y:E).Exists(b:bool).{ (ltE x y) = b })
	(ltE_tra:Forall(x y z:E)(u:{ (ltE x y) = tt })(v:{ (ltE y z) = tt }).{ (ltE x z) = tt })
	(a_tot:Forall(x:D).Exists(z:E).{ (a x) = z })
	(c_tot:Forall(y:E).Exists(z:D).{ (c y) = z })
	
	% first definition
	(u1:Forall(x y:D)(q:{ (ltD x y) = tt }).{ (ltE (a x) (a y)) = tt })
	(u2:Forall(x y:E)(q:{ (ltE x y) = tt }).{ (ltD (c x) (c y)) = tt })
	(u3:Forall(x:D).{ (ltD x (c (a x))) = tt })
	(u4:Forall(y:E).{ (ltE (a (c y)) y) = tt })
	.
	
	% proof starts
	foralli(x:D)(y:E).
	abbrev ax = terminates (a x) by [a_tot x] in
	abbrev cy = terminates (c y) by [c_tot y] in
	abbrev acy = terminates (a cy) by [a_tot cy] in
	abbrev cax = terminates (c ax) by [c_tot ax] in
	abbrev lhs = terminates (ltE ax y) by [ltE_tot ax y] in
	abbrev rhs = terminates (ltD x cy) by [ltD_tot x cy] in
	case lhs with
		ff =>
			case rhs with
				ff =>
					hypjoin (ltE (a x) y) (ltD x (c y)) by lhs_eq rhs_eq end
			| tt =>
					contra
					abbrev p3 = hypjoin (ltE ax y) ff by lhs_eq end in
					abbrev p1 = hypjoin (ltD x cy) tt by rhs_eq end in
					% p2: (ltE (a x) (a cy)) = tt
					abbrev p2 = [u1 x cy p1] in
					
					% want: (ltE (a (c y)) y) = tt
					abbrev p4 = [u4 y] in
					abbrev p4' = hypjoin (ltE acy y) tt by p4 end in
					abbrev p2' = hypjoin (ltE ax acy) tt by p2 end in
					trans symm [ltE_tra ax acy y p2' p4']
					trans p3
								clash ff tt
					{ (ltE (a x) y) = (ltD x (c y)) }
			end
	| tt =>
			abbrev p1 = hypjoin (ltE ax y) tt by lhs_eq end in
			% p2: (ltD (c ax) (c y)) = tt
			abbrev p2 = [u2 ax y p1] in
			% p3: (ltD x (c (a x))) = tt
			abbrev p3 = [u3 x] in
			abbrev p3' = hypjoin (ltD x cax) tt by p3 end in
			abbrev p2' = hypjoin (ltD cax cy) tt by p2 end in
			abbrev p4 = [ltD_tra x cax cy p3' p2'] in
			hypjoin (ltE (a x) y) (ltD x (c y)) by p4 lhs_eq end
	end
	.

Define thm2_3 : Forall
	% basic definitions
	(D E:type)
	(ltD:Fun(x y:D).bool)
	(ltE:Fun(x y:E).bool)
	(a:Fun(x:D).E)
	(c:Fun(y:E).D)

	(ltD_tot:Forall(x y:D).Exists(b:bool).{ (ltD x y) = b })
	(ltD_rfl:Forall(x:D).{ (ltD x x) = tt })
	(ltE_tot:Forall(x y:E).Exists(b:bool).{ (ltE x y) = b })
	(ltE_rfl:Forall(x:E).{ (ltE x x) = tt })
	(a_tot:Forall(x:D).Exists(z:E).{ (a x) = z })
	(c_tot:Forall(y:E).Exists(z:D).{ (c y) = z })
	
	% second definition
	(u:Forall(x:D)(y:E).{ (ltE (a x) y) = (ltD x (c y)) })
	.

	% first definition (3)
	Forall(x:D).{ (ltD x (c (a x))) = tt }
	:=
 	foralli
	% basic definitions
	(D E:type)
	(ltD:Fun(x y:D).bool)
	(ltE:Fun(x y:E).bool)
	(a:Fun(x:D).E)
	(c:Fun(y:E).D)

	(ltD_tot:Forall(x y:D).Exists(b:bool).{ (ltD x y) = b })
	(ltD_rfl:Forall(x:D).{ (ltD x x) = tt })
	(ltE_tot:Forall(x y:E).Exists(b:bool).{ (ltE x y) = b })
	(ltE_rfl:Forall(x:E).{ (ltE x x) = tt })
	(a_tot:Forall(x:D).Exists(z:E).{ (a x) = z })
	(c_tot:Forall(y:E).Exists(z:D).{ (c y) = z })
	
	% second definition
	(u:Forall(x:D)(y:E).{ (ltE (a x) y) = (ltD x (c y)) })
	.
	
	% proof starts
	foralli(x:D).
	existse [a_tot x] foralli(ax:E)(ax_pf:{ (a x) = ax }).
	abbrev p1 = [u x ax] in
	abbrev p2 = [ltE_rfl ax] in
	hypjoin (ltD x (c (a x))) tt by p1 p2 ax_pf end
	.

Define thm2_4 : Forall
	% basic definitions
	(D E:type)
	(ltD:Fun(x y:D).bool)
	(ltE:Fun(x y:E).bool)
	(a:Fun(x:D).E)
	(c:Fun(y:E).D)

	(ltD_tot:Forall(x y:D).Exists(b:bool).{ (ltD x y) = b })
	(ltD_rfl:Forall(x:D).{ (ltD x x) = tt })
	(ltE_tot:Forall(x y:E).Exists(b:bool).{ (ltE x y) = b })
	(ltE_rfl:Forall(x:E).{ (ltE x x) = tt })
	(a_tot:Forall(x:D).Exists(z:E).{ (a x) = z })
	(c_tot:Forall(y:E).Exists(z:D).{ (c y) = z })
	
	% second definition
	(u:Forall(x:D)(y:E).{ (ltE (a x) y) = (ltD x (c y)) })
	.

	% first definition (4)
	Forall(y:E).{ (ltE (a (c y)) y) = tt }
	:=
 	foralli
	% basic definitions
	(D E:type)
	(ltD:Fun(x y:D).bool)
	(ltE:Fun(x y:E).bool)
	(a:Fun(x:D).E)
	(c:Fun(y:E).D)

	(ltD_tot:Forall(x y:D).Exists(b:bool).{ (ltD x y) = b })
	(ltD_rfl:Forall(x:D).{ (ltD x x) = tt })
	(ltE_tot:Forall(x y:E).Exists(b:bool).{ (ltE x y) = b })
	(ltE_rfl:Forall(x:E).{ (ltE x x) = tt })
	(a_tot:Forall(x:D).Exists(z:E).{ (a x) = z })
	(c_tot:Forall(y:E).Exists(z:D).{ (c y) = z })
	
	% second definition
	(u:Forall(x:D)(y:E).{ (ltE (a x) y) = (ltD x (c y)) })
	.
	
	% proof starts
	foralli(y:E).
	existse [c_tot y] foralli(cy:D)(cy_pf:{ (c y) = cy }).
	abbrev p1 = [u cy y] in
	abbrev p2 = [ltD_rfl cy] in
	hypjoin (ltE (a (c y)) y) tt by p1 p2 cy_pf end
	.

	%Forall(x y:E)(q:{ (ltE x y) = tt }).{ (ltD (c x) (c y)) = tt }

Define thm2_1 : Forall
	% basic definitions
	(D E:type)
	(ltD:Fun(x y:D).bool)
	(ltE:Fun(x y:E).bool)
	(a:Fun(x:D).E)
	(c:Fun(y:E).D)

	(ltD_tot:Forall(x y:D).Exists(b:bool).{ (ltD x y) = b })
	(ltD_rfl:Forall(x:D).{ (ltD x x) = tt })
	(ltD_tra:Forall(x y z:D)(u:{ (ltD x y) = tt })(v:{ (ltD y z) = tt }).{ (ltD x z) = tt })
	(ltE_tot:Forall(x y:E).Exists(b:bool).{ (ltE x y) = b })
	(ltE_rfl:Forall(x:E).{ (ltE x x) = tt })
	(ltE_tra:Forall(x y z:E)(u:{ (ltE x y) = tt })(v:{ (ltE y z) = tt }).{ (ltE x z) = tt })
	(a_tot:Forall(x:D).Exists(z:E).{ (a x) = z })
	(c_tot:Forall(y:E).Exists(z:D).{ (c y) = z })
	
	% second definition
	(u:Forall(x:D)(y:E).{ (ltE (a x) y) = (ltD x (c y)) })
	.

	% first definition (1)
	Forall(x y:D)(q:{ (ltD x y) = tt }).{ (ltE (a x) (a y)) = tt }
	:=
 	foralli
	% basic definitions
	(D E:type)
	(ltD:Fun(x y:D).bool)
	(ltE:Fun(x y:E).bool)
	(a:Fun(x:D).E)
	(c:Fun(y:E).D)

	(ltD_tot:Forall(x y:D).Exists(b:bool).{ (ltD x y) = b })
	(ltD_rfl:Forall(x:D).{ (ltD x x) = tt })
	(ltD_tra:Forall(x y z:D)(u:{ (ltD x y) = tt })(v:{ (ltD y z) = tt }).{ (ltD x z) = tt })
	(ltE_tot:Forall(x y:E).Exists(b:bool).{ (ltE x y) = b })
	(ltE_rfl:Forall(x:E).{ (ltE x x) = tt })
	(ltE_tra:Forall(x y z:E)(u:{ (ltE x y) = tt })(v:{ (ltE y z) = tt }).{ (ltE x z) = tt })
	(a_tot:Forall(x:D).Exists(z:E).{ (a x) = z })
	(c_tot:Forall(y:E).Exists(z:D).{ (c y) = z })
	
	% second definition
	(u:Forall(x:D)(y:E).{ (ltE (a x) y) = (ltD x (c y)) })
	.
	
	% proof starts
	foralli(x y:D)(v:{ (ltD x y) = tt }).
	
	existse [a_tot x] foralli(ax:E)(ax_pf:{ (a x) = ax }).
	existse [a_tot y] foralli(ay:E)(ay_pf:{ (a y) = ay }).
	existse [c_tot ay] foralli(cay:D)(cay_pf:{ (c ay) = cay }).
	abbrev p1 = [u x ay] in
	abbrev p2 = [thm2_3 D E ltD ltE a c ltD_tot ltD_rfl ltE_tot ltE_rfl a_tot c_tot u y] in
	abbrev p2' = hypjoin (ltD y cay) tt by p2 cay_pf ay_pf end in
	abbrev p3 = [ltD_tra x y cay v p2'] in
	hypjoin (ltE (a x) (a y)) tt by p1 p3 ay_pf ax_pf cay_pf end
	.

Define thm2_2 : Forall
	% basic definitions
	(D E:type)
	(ltD:Fun(x y:D).bool)
	(ltE:Fun(x y:E).bool)
	(a:Fun(x:D).E)
	(c:Fun(y:E).D)

	(ltD_tot:Forall(x y:D).Exists(b:bool).{ (ltD x y) = b })
	(ltD_rfl:Forall(x:D).{ (ltD x x) = tt })
	(ltD_tra:Forall(x y z:D)(u:{ (ltD x y) = tt })(v:{ (ltD y z) = tt }).{ (ltD x z) = tt })
	(ltE_tot:Forall(x y:E).Exists(b:bool).{ (ltE x y) = b })
	(ltE_rfl:Forall(x:E).{ (ltE x x) = tt })
	(ltE_tra:Forall(x y z:E)(u:{ (ltE x y) = tt })(v:{ (ltE y z) = tt }).{ (ltE x z) = tt })
	(a_tot:Forall(x:D).Exists(z:E).{ (a x) = z })
	(c_tot:Forall(y:E).Exists(z:D).{ (c y) = z })
	
	% second definition
	(u:Forall(x:D)(y:E).{ (ltE (a x) y) = (ltD x (c y)) })
	.

	% first definition (2)
	Forall(x y:E)(v:{ (ltE x y) = tt }).{ (ltD (c x) (c y)) = tt }
	:=
 	foralli
	% basic definitions
	(D E:type)
	(ltD:Fun(x y:D).bool)
	(ltE:Fun(x y:E).bool)
	(a:Fun(x:D).E)
	(c:Fun(y:E).D)

	(ltD_tot:Forall(x y:D).Exists(b:bool).{ (ltD x y) = b })
	(ltD_rfl:Forall(x:D).{ (ltD x x) = tt })
	(ltD_tra:Forall(x y z:D)(u:{ (ltD x y) = tt })(v:{ (ltD y z) = tt }).{ (ltD x z) = tt })
	(ltE_tot:Forall(x y:E).Exists(b:bool).{ (ltE x y) = b })
	(ltE_rfl:Forall(x:E).{ (ltE x x) = tt })
	(ltE_tra:Forall(x y z:E)(u:{ (ltE x y) = tt })(v:{ (ltE y z) = tt }).{ (ltE x z) = tt })
	(a_tot:Forall(x:D).Exists(z:E).{ (a x) = z })
	(c_tot:Forall(y:E).Exists(z:D).{ (c y) = z })
	
	% second definition
	(u:Forall(x:D)(y:E).{ (ltE (a x) y) = (ltD x (c y)) })
	.
	
	% proof starts
	foralli(x y:E)(v:{ (ltE x y) = tt }).
	
	existse [c_tot x] foralli(cx:D)(cx_pf:{ (c x) = cx }).
	existse [c_tot y] foralli(cy:D)(cy_pf:{ (c y) = cy }).
	existse [a_tot cx] foralli(acx:E)(acx_pf:{ (a cx) = acx }).
	abbrev p1 = [u cx y] in
	abbrev p2 = [thm2_4 D E ltD ltE a c ltD_tot ltD_rfl ltE_tot ltE_rfl a_tot c_tot u x] in
	abbrev p2' = hypjoin (ltE acx x) tt by p2 acx_pf cx_pf end in
	abbrev p3 = [ltE_tra acx x y p2' v] in
	hypjoin (ltD (c x) (c y)) tt by p1 p3 cx_pf cy_pf acx_pf end
	.

%- DISCUSSION
more than half of the proof is for proving each term is a value
using the preconditions that each function/predicate is total.
In Coq/Isabelle, all functions are supposed to be total, so
they won't suffer from this hassel, which obviously makes
mathematical theorem proving more pleasant.
Although Guru does support registering functions total,
it is not applicable for functions passed as arguments or
defined within a function.
So, it may be desirable for new languages to allow registering
functions total within a local scope.

Also, thm2's have lots of redundancies. I'm not sure what is effective way
to prove multiple formulas at once. Maybe we could define a inductive type
that lists all the formulas and prove the existence of such a data.
There might be something better?
-%
