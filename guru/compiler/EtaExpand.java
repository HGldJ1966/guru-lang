package guru.compiler;

import guru.*;
import java.util.*;
import java.io.*;

public class EtaExpand {
    Context src;
    Context dst;

    Const expanding_c;

    protected Position last_pos;

    public Vector all_consts;
    public HashSet in_all_consts;

    public void handleError(Position pos, String msg) {
	if (pos != null) {
	    pos.print(System.out);
	    System.out.print(": ");
	}
	System.out.println("eta-expansion internal error.\n"+msg);
	System.exit(6);
    }

    public EtaExpand(Context src, Context dst) {
	this.src = src;
	this.dst = dst;
	last_pos = null;
	expanding_c = null;
	all_consts = new Vector();
	in_all_consts = new HashSet();
    }

    protected void all_consts_add(Const c) {
	if (!in_all_consts.contains(c)) {
	    if (src.getFlag("debug_eta_expand")) {
		src.w.println("Adding constant "+c.toString(src));
		src.w.flush();
	    }
	    all_consts.add(c);
	    in_all_consts.add(c);
	}
    }

    /* orig is the original term (from src).  _T is the type to use,
       or null if we should call classify ourselves. */
    protected Const addDef(Expr e, Expr orig, Const d, Expr _T) {
	Const c = d;
	Expr T = _T;
	if (T == null) {
	    if (src.getFlag("debug_eta_expand")) {
		src.w.print("Classifying (addDef) ");
		e.print(src.w,src);
		src.w.println("");
		src.w.flush();
	    }
	    T = e.classify(dst,Expr.APPROX_TRIVIAL,false);
	    if (src.getFlag("debug_eta_expand")) {
		src.w.println("done.");
		src.w.flush();
	    }
	}

	Expr e2 = e.dropAnnos(dst);

	if (c != null) {
	    if (dst.isDefined(c))
		return c;

	    if (dst.getFlag("debug_eta_expand")) {
		src.w.print("Defining "+c.name+" : ");
		T.print(src.w, src);
		src.w.print(" := ");
		e.print(src.w,src);
		src.w.println("");
		src.w.flush();
	    }
	    all_consts_add(c);
	    dst.define(c, src.getDefOwnership(c), T, e, e2,
		       src.getDefDelim(c), src.getDefCode(c));
	    return c;
	}
	// come up with a reasonable const to use.
	String basename = null;
	if (e.construct == Expr.FUN_TERM) {
	    FunTerm f = (FunTerm)e;
	    if (f.body.construct == Expr.TERM_APP) {
		TermApp a = (TermApp)f.body;
		if (a.head.construct == Expr.CONST)
		    basename = ((Const)a.head).name;
	    }
	    if (basename != null) 
		basename += "_partial";
	}
	/*	if (basename == null && expanding_c != null)
	  basename = expanding_c.name; */
	if (basename == null)
	    basename = "anon";
	
	Const c2 = dst.define(basename, src.getDefOwnership(c), 
			      T, e, e2, src.getDefDelim(c), src.getDefCode(c));
	all_consts_add(c2);

	if (dst.getFlag("debug_eta_expand")) {
	    src.w.print("Defining "+c2.name+" : ");
	    T.print(src.w, src);
	    src.w.print(" := ");
	    e.print(src.w,src);
	    src.w.println("");
	    src.w.flush();
	}

	return c2;
    }

    // Eta-expand any maximal applications of functional type.
    // Also, perform the following cleanup operations:
    //
    // 1. replace all fun-terms by constants, with appropriate
    //    definitions added to dst.
    // 2. Expand away abbrevs as we go.
    // 3. coalesce nested fun-terms.
    // 4. put all maximal application terms into spine form.
    // 5. drop non-computational arguments and inputs everywhere
    // 6. pull in all needed term and type ctors, and resource types.
    // 7. replace type applications with their heads.
    //
    public Expr expand(Expr e) {

	// pull in all resource types

	Iterator it = src.getResourceTypes().iterator();
	while (it.hasNext()) {
	    Const c = (Const)it.next();
	    Define drop = src.getDropFuncDef(src.getDropFunc(c));
	    dst.addResourceType(c);
	    dst.setDropFunc(c,drop);
	    all_consts_add(c);
	    all_consts_add(drop.c);
	}

	return expand(e, false, null);
    }

    protected Ownership expand(Ownership o) {
	Ownership ret = null;
	switch (o.status) {
	case Ownership.DEFAULT:
	    ret = o;
	    break;
	case Ownership.PINNED: 
	     ret = new Ownership(Ownership.PINNED, (Const)expand(o.e1,false,null),
					  (Var)expand(o.e2,false,null));
	     break;
	case Ownership.SPEC:
	    ret = o;
	    break;
	case Ownership.UNTRACKED:
	    ret = o;
	    break;

	case Ownership.RESOURCE:
	    ret = new Ownership(Ownership.RESOURCE,(Const)expand(o.e1,false,null));
	    break;
	}
	return ret;
    }

    // from_fun is true iff the immediately surrounding term is a fun-term.
    protected Expr expand(Expr e, boolean from_fun, Const from_const) {
	if (src.getFlag("debug_eta_expand")) {
	    src.w.print("Eta-expanding: ");
	    e.print(src.w,src);
	    src.w.println("");
	    src.w.flush();
	}
	if (e.construct != Expr.CONST)
	    last_pos = e.pos;
	switch (e.construct) {
	case Expr.ABBREV:
	    return expand(((Abbrev)e).subst(),from_fun,from_const);
	case Expr.CONST: {
	    Const c = (Const)e;
	    if (dst.isDefined(c) || dst.isCtor(c) || dst.isResourceType(c)
		|| dst.getClassifier(c) != null /* this last is crude,
						   but we must add
						   type ctors after
						   processing their term
						   ctors args */)
		return c;

	    if (!src.isDefined(c)) {
		/* must be a constructor or a resource type.  Add all
		   the type and related term ctors to dst. */

		if (src.isResourceType(c)) 
		    // already pulled in, in expand(Expr) above
		    return c;

		Const d = c;
		if (src.isTermCtor(c)) 
		    d = (Const)src.getTypeCtor(c);

		Expr dT = expand(src.getClassifier(d),false,null);

		dst.setClassifier(d,dT); // add as a type ctor below

		// 1. process the types of the term ctors
		Iterator it = src.getTermCtors(d).iterator();
		ArrayList a = new ArrayList();
		while(it.hasNext()) {
		    Const c1 = (Const)it.next();
		    Expr c1T = expand(src.getClassifier(c1),false,null);
		    a.add(c1T);
		}

		dst.addTypeCtor(d,dT);
		dst.setTypeCtorRetStat(d,src.getTypeCtorRetStat(d));
		all_consts_add(d);

		// 2. now add the term ctors to dst
		it = src.getTermCtors(d).iterator();
		Iterator it2 = a.iterator();
		while(it.hasNext()) {
		    Const c1 = (Const)it.next();
		    dst.addTermCtor(c1,d,(Expr)it2.next());
		    all_consts_add(c1);
		}

		return c;
	    }

	    if (src.isUntracked(c))
		dst.makeUntracked(c);

	    if (src.isTypeFamilyAbbrev(c))
		dst.markTypeFamilyAbbrev(c);

	    if (src.isSpec(c))
		dst.markSpec(c);

	    Expr cT = expand(src.getClassifier(c),false,null);

	    if (src.isOpaque(c) && src.isDefined(c)) {
		Expr t = src.getDefBody(c);
		if (t.construct == Expr.VAR) {
		    /* we handle one corner case here, where this is a
		       variable introduced by the Parser for the body
		       of a primitive definition without a functional
		       model.  We just need to map over the type from
		       src to dst in that case. */
		    Var v = (Var)t;
		    if (dst.getClassifier(v) == null)
			/* this is in case we have a global Var (for a primitive
			   definition without a functional model).  We will not
			   otherwise set its type in dst. */
			dst.setClassifier(v,src.getClassifier(v));
		}

		if (c.isTypeOrKind(src)) 
		    /* so that we recognize later that c is a type 
		       or kind (by looking at its definition) */
		    t = expand(t.defExpandTop(src),false,c);
		all_consts_add(c);
		dst.define(c, src.getDefOwnership(c), cT, t,
			   src.getDefBodyNoAnnos(c), src.getDefDelim(c), src.getDefCode(c));
		dst.makeOpaque(c);
		return c;
	    }

	    if (src.isTrusted(c))
		dst.markTrusted(c);

	    if (expanding_c == c)
		/* c is a recursive reference to expanding_c in the latter's
		   body; this reference is introduced in the FUN_TERM case
		   below. */
		return c;

	    dst.setClassifier(c, cT);

	    if (c.isProof(src))
		/* we set the classifier above so we know this is a proof
		   later */
		return c;

	    Const prev_c = expanding_c;
	    expanding_c = c;
	    Expr orig = src.getDefBody(c);

	    Expr e2 = expand(orig,from_fun,c);
	    expanding_c = prev_c;

	    if (e2.construct != Expr.CONST || e2 != c)
		// we did not introduce a definition for the body
		// when expanding. The second condition handles
		// a corner case where c is defined to be a term
		// constructor d.  Then, we should not replace
		// c with d, because they behave differently with
		// respect to reference counting (0-ary ctors construct
		// data, 0-ary definitions do not).
		return addDef(e2,orig,c,cT);

	    return e2;
	}
	case Expr.FUN_TERM: {
	    FunTerm f = (FunTerm)((FunTerm)e).coalesce(src,false);
	    Expr tmp = f.dropNoncompInputs(src);
	    if (tmp.construct != Expr.FUN_TERM)
		return expand(tmp,from_fun,from_const);

	    /* we need to set classifiers of non-computational inputs,
	       which might be mentioned in types of later inputs. */

	    int iend = f.vars.length;
	    for (int i = 0; i < iend; i++) 
		dst.setClassifier(f.vars[i],expand(f.types[i],false,null));

	    f = (FunTerm)tmp;
	    
	    iend = f.vars.length;
	    Expr[] ntypes = new Expr[iend];
	    Ownership[] nowned = new Ownership[iend];
	    for (int i = 0; i < iend; i++) {
		nowned[i] = expand(f.owned[i]);
		// we already expanded the type for f.vars[i] above
		ntypes[i] = expand(dst.getClassifier(f.vars[i]),false,null);
	    }

	    Expr b = f.body;

	    Expr nT = expand(f.T,false,null);
	    Ownership nret_stat = expand(f.ret_stat);
	    f = new FunTerm(f.r, nT, f.vars, ntypes, nowned, f.consumps,
			    nret_stat, b);
	    f.setClassifiers(dst); // to set the vars to have the new types

	    f.body = expand(b,true,null); // expand the body

	    f = (FunTerm)f.coalesce(dst,false);
	    Expr ret = f;
	    ret.pos = e.pos;

	    return addDef(ret, e, from_const, null);
	}
	case Expr.STRING_EXPR: {
	    Iterator it = ((StringExpr)e).getConstsUsed(src).iterator();
	    while(it.hasNext()) {
		Const c = (Const)it.next();
		expand(c,from_fun,null);
	    }
	    return e;
	}
	case Expr.VAR: 
	    return e;
	case Expr.ABORT:
	    return e;
	case Expr.LET: {
	    Let l = (Let)e;
	    Expr nt1 = expand(l.t1,false,null);
	    Let nl = new Let(l.x1,l.x1_stat,nt1,l.x2,null);
	    nl.setClassifiers(dst, Expr.APPROX_TRIVIAL,false);

	    Expr nt2 = expand(l.t2,false,null);
	    if (nt1 == l.t1 && nt2 == l.t2)
		return e;
	    nl.t2 = nt2;
	    nl.pos = e.pos;
	    return nl;
	}
	case Expr.DO: {
	    Do d = (Do)e;
	    boolean changed = false;
	    int iend = d.ts.length;
	    Expr[] nts = new Expr[iend];
	    for (int i = 0; i < iend; i++) {
		nts[i] = expand(d.ts[i],false,null);
		changed = changed || (nts[i] != d.ts[i]);
	    }
	    Expr nt = expand(d.t,false,null);
	    if (changed || nt != d.t) {
		Expr ret = new Do(nts,nt);
		ret.pos = d.pos;
		return ret;
	    }
	    return e;
	}
	case Expr.EXISTSE_TERM: {
	    ExistseTerm c = (ExistseTerm)e;
	    return expand(c.t,false,null);
	}

	case Expr.CAST: {
	    Cast c = (Cast)e;
	    Expr nt = expand(c.t,false,null);
	    if (c.t == nt)
		return e;
	    Expr ret = new Cast(nt,c.P,c.T);
	    ret.pos = e.pos;
	    return ret;
	}
	case Expr.COMPRESS: {
	    Compress c = (Compress)e;
	    Expr nt = expand(c.t,false,null);
	    if (c.t == nt)
		return e;
	    Expr ret = new Compress(nt);
	    ret.pos = e.pos;
	    return ret;
	}
	case Expr.TERMINATES: {
	    Terminates c = (Terminates)e;
	    return expand(c.t,false,null);
	}
	case Expr.MATCH: {
	    Match m = (Match)e;
	    Expr nt = expand(m.t,false,null);
	    boolean chg = (nt != m.t);
	    Case[] nC = new Case[m.C.length];
	    Expr scruttp = nt.classify(dst,Expr.APPROX_TRIVIAL,false);
	    for (int i = 0, iend = m.C.length; i < iend; i++) {
		if (src.getFlag("debug_eta_expand")) {
		    src.w.println("Processing Case: "+m.C[i].toString(src));
		    src.w.flush();
		}
		Case c = m.C[i].dropNoncompPatternVars(src);
		if (src.getFlag("debug_eta_expand")) {
		    src.w.println("After dropping noncomp pattern vars: "+c.toString(dst));
		    src.w.flush();
		}
		expand(c.c,false,null); // we might need to add c.c to dst
		c.setPatternVarTypes(dst, false); 
		c.refine(dst,scruttp,Expr.APPROX_TRIVIAL,false);

		Expr nbody = expand(c.body,false,null);
		if (nbody == c.body && c.x == m.C[i].x) 
		    nC[i] = c;
		else {
		    nC[i] = new Case(c.c,c.x,nbody,c.impossible);
		    nC[i].pos = c.pos;
		    chg = true;
		}
		if (src.getFlag("debug_eta_expand")) {
		    src.w.println("Final result1: "+c.toString(dst));
		    src.w.flush();
		}
	    }
	    if (!chg)
		return e;
	    Expr ret = new Match(nt,m.x1,m.x2,m.T,nC,m.consume_first);
	    ret.pos = e.pos;
	    return ret;
	}
	case Expr.TERM_APP: {
	    TermApp s = (TermApp)(((TermApp)e)
				  .spineForm(src,false,false,
					     false /* expand_defs */));

	    if (src.getFlag("debug_eta_expand")) {
		src.w.print("Classifying (expand) ");
		s.print(src.w,src);
		src.w.println("");
		src.w.flush();
	    }

	    Expr T = (s.classify(src,Expr.APPROX_TRIVIAL,false)
		      .defExpandTop(src,false,false));

	    if (src.getFlag("debug_eta_expand")) {
		src.w.println("done.");
		src.w.flush();
	    }

	    Expr tmp = s.dropNoncompArgs(src);

	    if (tmp.construct != Expr.TERM_APP)
		return expand(tmp,from_fun,from_const);

	    s = (TermApp)tmp;

	    Expr nh = expand(s.head,false,null);
	    int num_old_args = s.X.length;
	    Expr[] nX = new Expr[num_old_args];
	    
	    boolean changed = false;
	    for (int i = 0; i < num_old_args; i++) {
		nX[i] = expand(s.X[i],false,null);
		if (nX[i] != s.X[i])
		    changed = true;
	    }
	    
	    if (nh != s.head || changed) {
		s = new TermApp(nh,nX);
		s.pos = e.pos;
	    }

	    if (T.construct != Expr.FUN_TYPE) 
		return s;
	    FunType F = (FunType)T;
	    Expr tmp1 = F.dropNoncompInputs(src);
	    if (tmp1.construct != Expr.FUN_TYPE)
		return s;
	    F = (FunType)tmp1;

	    Var[] vars = F.vars;
	    int iend = vars.length;
	    nX = new Expr[num_old_args + iend];
	    for (int i = 0; i < num_old_args; i++)
		nX[i] = s.X[i];
	    for (int i = 0; i < iend; i++) 
		nX[i+num_old_args] = vars[i];
	    FunTerm f = new FunTerm(null, null, F.vars, F.types, F.owned, F.consumps,
				    F.ret_stat, new TermApp(s.head,nX));
	    f.setClassifiers(dst);// to recompute ownerships
	    f.pos = e.pos;
	    if (from_fun)
		return f;
	    return addDef(f, e, from_const, null);
	} 

	case Expr.FUN_TYPE: {
	    FunType F = (FunType)((FunType)e).coalesce(src,false);

	    // set classifiers, even for spec variables.
	    for (int j = 0, jend = F.vars.length; j < jend; j++) 
		dst.setClassifier(F.vars[j],expand(F.types[j],false,null));

	    Expr tmp = F.dropNoncompInputs(src);
	    if (tmp != F)
		return expand(tmp,from_fun,from_const);
	    F = (FunType)tmp;
	    int iend = F.vars.length;
	    Expr[] ntypes = new Expr[iend];
	    Ownership[] nowned = new Ownership[iend];
	    for (int i = 0; i < iend; i++) {
		ntypes[i] = dst.getClassifier(F.vars[i]);
		nowned[i] = expand(F.owned[i]);
	    }
	    Expr nb = expand(F.body,false,null);
	    Ownership nret_stat = expand(F.ret_stat);
	    Expr ret = new FunType(F.vars,ntypes,nowned,F.consumps,nret_stat,nb);
	    ret.pos = e.pos;
	    return ret;
	}
	case Expr.TYPE_APP: {
	    TypeApp T = (TypeApp)e;
	    /*	    return expand(T.head,false,null); */

	    Expr nhead = expand(T.head,false,null);
	    int iend = T.X.length;
	    Expr[] nX = new Expr[iend];
	    for (int i = 0; i < iend; i++) {
		if (T.X[i].isTypeOrKind(src))
		    nX[i] = expand(T.X[i],false,null);
		else
		    nX[i] = T.X[i]; // basically, we want this to be ignored later
	    }
	    Expr ret = new TypeApp(nhead,nX); 
	    ret.pos = e.pos;
	    return ret;
	}

	default:
	    // I don't think this can happen at this point
	    return e;
	}
    }
}
