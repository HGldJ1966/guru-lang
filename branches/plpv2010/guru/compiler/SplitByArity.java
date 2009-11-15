package guru.compiler;

import guru.*;
import java.util.*;
import java.io.*;

public class SplitByArity {
    Context src;
    Context dst;
    
    int nextvar;

    public SplitByArity() { nextvar = 0; }

    // we will modify the bodies of defined terms in the given Context.
    public void process(Context src, Context dst) {
	this.src = src;
	this.dst = dst;

	Iterator it = src.getDefinedConsts().iterator();
	while(it.hasNext()) {
	    Const c = (Const)it.next();

	    Expr T = src.getClassifier(c);
	    Expr t = src.getDefBody(c);

	    if (t.isTypeOrKind(src)) {
		dst.define(c,T,t,src.getDefBodyNoAnnos(c));
		continue;
	    }

	    if (src.isUntracked(c))
		dst.makeUntracked(c);
	    if (src.isTypeFamilyAbbrev(c))
		dst.markTypeFamilyAbbrev(c);
	    if (src.isOpaque(c)) {
		dst.define(c,T,t,src.getDefBodyNoAnnos(c));
		dst.makeOpaque(c);
		continue;
	    }

	    if (src.getFlag("debug_split_by_arity")) {
		src.w.print("Splitting by arity: ");
		c.print(src.w,src);
		src.w.println("");
		src.w.flush();
	    }
		
	    /*dst.setClassifier(c,T); recursive references are to c
				       following eta expansion. */

	    Expr nt = process(t);

	    dst.define(c,T,nt,nt.dropAnnos(dst));
	}
    }

    public Expr[] process(Expr[] X) {
	int iend = X.length;
	Expr[] nX = new Expr[iend];
	for (int i = 0; i < iend; i++)
	    nX[i] = process(X[i]);
	return nX;
    }

    public Expr process(Expr e) {
	switch (e.construct) {
	case Expr.VAR:
	case Expr.ABORT:
	case Expr.CONST: 
	case Expr.STRING_EXPR:
	    return e;
	case Expr.FUN_TERM: {
	    FunTerm f = (FunTerm)e;
	    //	    f.setClassifiers(dst);
	    Expr nb = process(f.body);
	    f = new FunTerm(f.r, f.T, f.vars, f.types, f.owned, 
			    f.ret_stat, nb);
	    f.pos = e.pos;
	    return f;
	}
	case Expr.LET: {
	    Let l = (Let)e;
	    Expr nt1 = process(l.t1);
	    Expr nt2 = process(l.t2);
	    Let nl = new Let(l.x1, l.x1_stat, nt1, l.x2, nt2);
	    nl.pos = e.pos;
	    return nl;

	    /*
	    Let nl = new Let(l.x1,l.x1_stat,nt1,l.x2,null);
	    nl.setClassifiers(dst, Expr.APPROX_TRIVIAL);

	    nl.t2 = process(l.t2);
	    nl.pos = e.pos;
	    return nl; */
	}
	case Expr.CAST: {
	    Cast c = (Cast)e;
	    Expr nt = process(c.t);
	    Expr ret = new Cast(nt,c.P,c.T);
	    ret.pos = e.pos;
	    return ret;
	}
	case Expr.INC: {
	    Inc i = (Inc)e;
	    Expr nt = process(i.t);
	    Expr ret = new Inc(nt,i.T);
	    ret.pos = e.pos;
	    return ret;
	}
	case Expr.DEC: {
	    Dec d = (Dec)e;
	    Expr nI = process(d.I);
	    Expr nt = process(d.t);
	    Expr ret = new Dec(nI,nt,d.T);
	    ret.pos = e.pos;
	    return ret;
	}
	case Expr.MATCH: {
	    Match m = (Match)e;
	    Expr nt = process(m.t);
	    Case[] nC = new Case[m.C.length];
	    Expr scruttp = nt.classify(dst,Expr.APPROX_TRIVIAL,false);
	    for (int i = 0, iend = m.C.length; i < iend; i++) {
		Case c = m.C[i];
		c.setPatternVarTypes(dst, false); 
		c.refine(dst,scruttp,Expr.APPROX_TRIVIAL,false);
		Expr nbody = process(c.body);
		nC[i] = new Case(c.c,c.x,nbody,c.impossible);
		nC[i].pos = c.pos;
	    }

	    Expr ret = new Match(nt,m.x1,m.x2,m.T,nC,m.scrut_stat);
	    ret.pos = e.pos;
	    return ret;
	}
	case Expr.TERM_APP: {
	    TermApp s = splitByArity(dst,(TermApp)e);

	    Expr nh = process(s.head);
	    Expr[] nX = process(s.X);
	    Expr ret;
	    if (nh.construct != Expr.CONST && nh.construct != Expr.VAR) {
		// we have to split this, since the head is a compound term.
		Var v = nextTmp();
		Let l = new Let(v,new Ownership(Ownership.NOT_TRACKED),
				nh,null, new TermApp(v,nX));
		l.setClassifiers(dst, Expr.APPROX_TRIVIAL, false);
		ret = l;
	    }
	    else
		ret = new TermApp(nh,nX);
	    ret.pos = e.pos;
	    return ret;
	}
	default:
	    // this should just be an annotation (as an argument in a TermApp)
	    // at this point.  
	    return e;
	}
    }

    protected Var nextTmp() {
	return new Var("tmp"+(new Integer(nextvar++)).toString());
    }


    protected TermApp splitByArity(Context ctxt, TermApp a) {
	int ar = arity(ctxt,a.head);
	if (ar == a.X.length)
	    return a;
	return splitByArity(ctxt, a.split(ar));
    }

    // call only for terms that are known to be of functional type.
    protected int arity(Context ctxt, Expr e) {
	/*ctxt.w.println("Computing arity of "+e.toString(ctxt) + " {");
	  ctxt.w.flush();*/
	FunType f = (FunType)(e.classify(ctxt,Expr.APPROX_TRIVIAL, false)
			      .defExpandTop(ctxt,false,false));
	/*ctxt.w.println("}");
	  ctxt.w.flush();*/
	return f.getArity();
    }


}