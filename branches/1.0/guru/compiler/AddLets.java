package guru.compiler;

import guru.*;
import java.util.*;
import java.io.*;

/* This class pulls let- and match-terms out from all but return
   positions.  Also, it ensures that scrutinees (of match-terms) are
   Vars.  We assume we are given either a term produced by
   EtaExpand. */
public class AddLets {
    int nextvar;
    Context dst, src;

    static class Def {
	public Var x1;
	public Expr t1;
	public Def(Var x1, Expr t1) {
	    this.x1 = x1;
	    this.t1 = t1; 
	}
    }

    public AddLets() {
	this.nextvar = 0;
    }

    // populate dst with transformed versions of the constants defined in src.
    public void process(Context src, Context dst) {
	this.src = src;
	this.dst = dst;
	Iterator it = src.getDefinedConsts().iterator();
	while (it.hasNext()) {
	    Const c = (Const)it.next();
	    
	    if (src.getFlag("debug_add_lets")) {
		dst.w.print("AddLets processing: ");
		c.print(dst.w,dst);
		dst.w.println(" (");
		dst.w.flush(); 
	    }
	    Expr b = src.getDefBody(c);
	    Expr bNoAnnos;
	    Expr T;
	    if (src.isOpaque(c)) {
		bNoAnnos = src.getDefBodyNoAnnos(c);
		T = src.getClassifier(c);
	    }
	    else {
		b = process(b);
		bNoAnnos = b.dropAnnos(dst);
		T = b.classify(dst,Expr.APPROX_TRIVIAL,false);
	    }

	    if (src.getFlag("debug_add_lets")) {
		dst.w.print(") defining to equal "+b.toString(dst));
		dst.w.println(c.name);
		dst.w.flush(); 
	    }

	    dst.define(c, T, b, bNoAnnos);

	    if (src.isTypeFamilyAbbrev(c))
		dst.markTypeFamilyAbbrev(c);
	}
    }

    protected Var define(Expr t, Vector defs) {
	Var tmp1 = nextTmp();
	/*	dst.w.print("Defining ");
	dst.w.print(tmp1.name);
	dst.w.print(" := ");
	t.print(dst.w, dst);
	dst.w.println("");
	dst.w.flush();*/
	defs.add(new Def(tmp1, t));
	return tmp1;
    }

    protected Expr wrap(Expr t, Vector defs) {
	if (dst.getFlag("debug_add_lets")) {
	    dst.w.println("Wrapping "+t.toString(dst));
	    dst.w.flush();
	}
	Iterator it = defs.iterator();
	while(it.hasNext()) {
	    Def D = (Def)it.next();
	    Expr T = D.t1.classify(dst,Expr.APPROX_TRIVIAL,
				   false);
	    if (dst.getFlag("debug_add_lets")) {
		dst.w.print(D.x1.name);
		dst.w.print(" : ");
		T.print(dst.w, dst);
		dst.w.print(" := ");
		D.t1.print(dst.w, dst);
		dst.w.println("");
		dst.w.flush();
	    }
	    dst.setClassifier(D.x1, T);
	}	    

	Collections.reverse(defs);
	it = defs.iterator();
	while(it.hasNext()) {
	    Def D = (Def)it.next();

	    t = new Let(D.x1, new Ownership(Ownership.DEFAULT), D.t1, null, t);
	}
	return t;
    }

    // any let-terms added will appear either at the top of t, if t is
    // not a fun-term, or at the top of t's body, if t is a fun-term.
    protected Expr process(Expr t) {
	Expr b = t;
	boolean isfun = (b.construct == Expr.FUN_TERM);
	FunTerm f = null;
	if (isfun) {
	    b = (f = (FunTerm)b).body;
	    f.setClassifiers(dst);
	}
	Vector defs = new Vector();
	Expr ret = process(b, defs, true);
	ret = wrap(ret,defs);
	if (!isfun)
	    return ret;

	return new FunTerm(f.r, f.T, f.vars, f.types, f.owned, 
			   f.ret_stat, ret);
    }

    protected Expr[] process(Expr[] X, Vector defs, boolean return_pos) {
	Expr[] nX = new Expr[X.length];
	for (int i = 0, iend = nX.length; i < iend; i++)
	    nX[i] = process(X[i], defs, return_pos);
	return nX;
    }

    protected Var nextTmp() {
	return new Var("tmp"+(new Integer(nextvar++)).toString());
    }

    protected Expr process(Expr t, Vector defs, boolean return_pos) {
	if (src.getFlag("debug_add_lets")) {
	    src.w.println("Processing: "+t.toString(src));
	    src.w.flush();
	}
	switch (t.construct) {
	case Expr.TERM_APP: {
	    TermApp a = (TermApp)t;
	    Expr ret = new TermApp(process(a.head, defs, false),
				   process(a.X, defs, false));
	    ret.pos = t.pos;
	    return ret;
	}
	case Expr.LET: {
	    Let l = (Let)t;
	    Expr t1 = process(l.t1, defs, false);
	    defs.add(new Def(l.x1, t1));
	    return process(l.t2, defs, return_pos);
	}
	case Expr.MATCH: {
	    Match m = (Match)t;
	    Expr nt = process(m.t, defs, false);
	    if (nt.construct != Expr.VAR)
		nt = define(nt,defs);
	    Case[] nC = new Case[m.C.length];
	    Expr scruttp = m.t.classify(src,Expr.APPROX_TRIVIAL,false);
	    for (int i = 0, iend = nC.length; i < iend; i++) {
		Case c = m.C[i];
		boolean impossible = c.impossible;
		c.setPatternVarTypes(dst, false);
		c.refine(dst,scruttp,Expr.APPROX_TRIVIAL,false);
		Vector defs2 = new Vector();
		Expr nbody = wrap(process(c.body,defs2,return_pos), defs2);
		nC[i] = new Case(c.c, c.x, nbody, c.impossible);
		nC[i].pos = t.pos;
	    }

	    Match nm = new Match(nt, m.x1, m.x2, m.T, nC, m.scrut_stat);
	    nm.pos = t.pos;
	    if (!return_pos) 
		return define(nm,defs);
	    return nm;
	}
	case Expr.STRING_EXPR:
	    return process(((StringExpr)t).expand(dst),defs,return_pos);
	case Expr.CONST: 
	case Expr.ABORT:
	case Expr.VAR:
	    return t; 
	case Expr.INC: {

	    /* we need to pull both Incs and Decs out, because Decs
	       need to be pulled out.  That is because we are going to
	       have to turn "dec I t" into "dec(I); t", and we cannot
	       do that if the Dec is buried in a non-returning
	       position.  And once we start moving Decs, we are going
	       to have to move Incs, too, lest we shuffle a Dec past
	       an Inc, invalidating the verification done by
	       CheckRefs. */

	    Inc i = (Inc)t;
	    Expr nt = process(i.t,defs,false);
	    if (nt.construct != Expr.VAR)
		nt = define(nt,defs);
	    Expr ni = new Inc(nt,i.T);
	    ni.pos = t.pos;
	    return define(ni, defs);
	}	    
	case Expr.DEC: {
	    Dec d = (Dec)t;
	    Expr nI = process(d.I,defs,false);
	    Expr nt = process(d.t,defs,return_pos);
	    if (nI.construct != Expr.VAR)
		nI = define(nI,defs);
	    Expr nd = new Dec(nI,nt,d.T);
	    nd.pos = t.pos;
	    if (return_pos)
		return nd;
	    return define(nd,defs);
	}	    
	case Expr.CAST: {
	    Cast c = (Cast)t;
	    Expr nt = process(c.t,defs,return_pos);
	    Expr ret = new Cast(nt,c.P,c.T);
	    ret.pos = t.pos;
	    return ret;
	}
	case Expr.EXISTSE_TERM: {
	    ExistseTerm c = (ExistseTerm)t;
	    Expr nt = process(c.t,defs,return_pos);
	    Expr ret = new Cast(c.P,nt);
	    ret.pos = t.pos;
	    return ret;
	}
	default:
	    return t;
    }
    }
}