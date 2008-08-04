package guru.compiler;

import guru.*;
import java.util.*;
import java.io.*;

public class EtaExpand {
    Context src;
    Context dst;

    Const expanding_c;

    protected Position last_pos;

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
	    
	    dst.define(c, T, e, e2);
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
	
	Const c2 = dst.define(basename, T, e, e2);

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
    // 6. pull in all needed term and type ctors.
    //
    public Expr expand(Expr e) {
	return expand(e, false, null);
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
	    if (dst.isDefined(c) || dst.isCtor(c) 
		|| dst.getClassifier(c) != null /* this last is crude,
						   but we must add
						   type ctors after
						   processing its term
						   ctors args */)
		return c;

	    if (!src.isDefined(c)) {
		/* must be a constructor.  Add all the type and related
		   term ctors to dst. */
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

		// 2. now add the term ctors to dst
		it = src.getTermCtors(d).iterator();
		Iterator it2 = a.iterator();
		while(it.hasNext()) {
		    Const c1 = (Const)it.next();
		    dst.addTermCtor(c1,d,(Expr)it2.next());
		}

		return c;
	    }

	    if (src.isUntracked(c))
		dst.makeUntracked(c);

	    if (src.isTypeFamilyAbbrev(c))
		dst.markTypeFamilyAbbrev(c);

	    Expr cT = expand(src.getClassifier(c),false,null);

	    if (src.isOpaque(c)) { // should be a defined term, not type
		Expr t = src.getDefBody(c);
		dst.define(c, cT, t, src.getDefBodyNoAnnos(c));
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
		// respect to reference counting.
		return addDef(e2,orig,c,cT);

	    return e2;
	}
	case Expr.FUN_TERM: {
	    FunTerm f = (FunTerm)((FunTerm)e).coalesce(src,false);
	    Expr tmp = f.dropNoncompInputs(src);
	    if (tmp.construct != Expr.FUN_TERM)
		return expand(tmp,from_fun,from_const);

	    f = (FunTerm)tmp;

	    int iend = f.vars.length;
	    Expr[] ntypes = new Expr[iend];
	    for (int i = 0; i < iend; i++)
		ntypes[i] = expand(f.types[i],false,null);

	    Expr b = f.body;
	    Expr nT = expand(f.T,false,null);
	    f = new FunTerm(f.r, nT, f.vars, ntypes, f.owned, 
			    f.ret_stat, b);
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
		expand(c,from_fun,from_const);
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
	case Expr.TERMINATES: {
	    Terminates c = (Terminates)e;
	    return expand(c.t,false,null);
	}
	case Expr.INC: {
	    Inc i = (Inc)e;
	    Expr nt = expand(i.t,false,null);
	    if (nt == i.t)
		return e;
	    Expr ret = new Inc(nt);
	    ret.pos = e.pos;
	    return ret;
	}
	case Expr.DEC: {
	    Dec d = (Dec)e;
	    Expr nI = expand(d.I,false,null);
	    Expr nt = expand(d.t,false,null);
	    if (nI == d.I && nt == d.t)
		return e;
	    Expr ret = new Dec(nI,nt);
	    ret.pos = e.pos;
	    return ret;
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
	    Expr ret = new Match(nt,m.x1,m.x2,m.T,nC,m.scrut_stat);
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
	    FunTerm f = new FunTerm(null, null, F.vars, F.types, F.owned,
				    F.ret_stat, new TermApp(s.head,nX));
	    f.setClassifiers(dst);// to recompute ownerships
	    f.pos = e.pos;
	    if (from_fun)
		return f;
	    return addDef(f, e, from_const, null);
	} 

	case Expr.FUN_TYPE: {
	    FunType F = (FunType)((FunType)e).coalesce(src,false);
	    Expr tmp = F.dropNoncompInputs(src);
	    if (tmp != F)
		return expand(tmp,from_fun,from_const);
	    F = (FunType)tmp;
	    int iend = F.vars.length;
	    Expr[] ntypes = new Expr[iend];
	    for (int i = 0; i < iend; i++) 
		ntypes[i] = expand(F.types[i],false,null);
	    Expr nb = expand(F.body,false,null);
	    Expr ret = new FunType(F.vars,ntypes,F.owned,F.ret_stat,nb);
	    ret.pos = e.pos;
	    return ret;
	}
	case Expr.TYPE_APP: {
	    TypeApp T = (TypeApp)e;
	    Expr nhead = expand(T.head,false,null);
	    int iend = T.X.length;
	    Expr[] nX = new Expr[iend];
	    for (int i = 0; i < iend; i++) 
		nX[i] = expand(T.X[i],false,null);
	    return new TypeApp(nhead,nX);
	}

	default:
	    // I don't think this can happen at this point
	    return e;
	}
    }
}
