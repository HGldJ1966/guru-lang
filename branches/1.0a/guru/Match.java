package guru;

import java.util.*;
import java.io.*;

public class Match extends CasesExpr{
    public Expr T;
    
    // set in the compiler during refcount checking
    public Ownership scrut_stat;

    public Match() {
	super(MATCH);
	scrut_stat = new Ownership(Ownership.UNOWNED);
    }

    public Match(CasesExpr a, Expr T, Ownership scrut_stat) {
	super(MATCH, a);
	this.T = T;
	this.scrut_stat = scrut_stat;
    }

    public Match(Expr t, Var x1, Var x2, Expr T, Case[] C, 
		 Ownership scrut_stat) {
	super(MATCH, t, x1, x2, C);
	this.T = T;
	this.scrut_stat = scrut_stat;
    }

    public void do_print(java.io.PrintStream w, 
			 Context ctxt) {
	w.print("match ");

	if (scrut_stat.status != Ownership.UNOWNED
	    && ctxt.getFlag("print_ownership_annos")) 
	    w.print("%- "+scrut_stat.toString(ctxt)+" -% ");

	do_print1(w,ctxt);
	if (T != null) {
	    w.print(" return ");
	    T.print(w,ctxt);
	}
	do_print2(w,ctxt);
    }

    public int numOccInCases(Expr e) {
	return super.numOcc(e);
    }

    public int numOcc(Expr e) {
	int n = numOccInCases(e);
	if (T != null)
	    n += T.numOcc(e);
	return n;
    }

    public Expr subst(Expr e, Expr x) {
	Expr nT = (T == null ? null : T.subst(e,x));
	CasesExpr nC = (CasesExpr)super.subst(e,x);
	if (nT != T || nC != this)
	    return new Match(nC, nT, scrut_stat);
	return this;
    }
    
    public Expr do_rewrite(Context ctxt, Expr e, Expr x, Stack boundVars) {
	Expr nT = T;
	CasesExpr nC = (CasesExpr)super.do_rewrite(ctxt,e,x,boundVars);
	if (nT != T || nC != this)
	    return new Match(nC, nT, scrut_stat);
	return this;
    }

    // if e matches one of our cases, instantiate that case with e.
    // otherwise, return null.
    protected Expr instantiate(Context ctxt, Expr e) {
	e = e.defExpandTop(ctxt);

	Expr h = e;
	if (h.construct == TERM_APP) {
	    TermApp a = (TermApp)h;
	    h = a.getHead(ctxt,true);
	}

	if (h.construct != CONST){ 
	    return null;
	}
	
	Integer ii = ctxt.getWhichTermCtor((Const)h);
	
	if (ii == null)
	    return null;
	int i = ii.intValue();
	if (i >= C.length)
	    return null;

	return C[i].instantiate(ctxt, e);
    }


    public Expr dropAnnos(Context ctxt) {
	Expr r = super.dropAnnos(ctxt);
	if (r != this)
	    return new Match((CasesExpr)r,T,scrut_stat);
	return this;
    }

    // we assume proofs have been dropped already
    public Expr evalStep(Context ctxt) {
	Expr e = t.evalStep(ctxt);
	if (e != t)
	    return new Match(e,x1,x2,T,C,scrut_stat);
	if (t.construct == ABORT)
	    return ctxt.abort;
	
	Expr ret = instantiate(ctxt, e);
	if (ret == null) 
	    return this;
	return ret;
    }

    public boolean subtermDefEqNoAnno(Context ctxt, Expr e) {
	return (t.subtermDefEqNoAnno(ctxt, e) || super.subtermDefEqNoAnno(ctxt, e));
    }
    
    public Expr classify(Context ctxt, int approx, boolean spec) {
	Expr T1 = super.classify(ctxt,approx,spec);
	if (T != null) {
	    Expr cT = T.classify(ctxt,approx,spec);
	    if (cT.construct != TYPE)
		handleError(ctxt,
			    "The return type of a match-term is not a type.\n"
			    +"1. the return type:"+T.toString(ctxt)+"\n"
			    +"2. its classifier:"+cT.toString(ctxt));
	    if (!T1.defEq(ctxt,T,approx,spec))
		handleError(ctxt,"The stated return type of a match-term"
			    +" is not def. eq. to\nthe type computed"
			    +" for the cases.\n"
			    +"1. stated type: "+T.toString(ctxt)+"\n"
			    +"2. computed: "+T1.toString(ctxt));
	}
	else
	    T = T1;
	return T;
    }

    public java.util.Set getDependences() {
        java.util.Set s = super.getDependences();
        if (T != null)
            s.addAll(T.getDependences());
        return s;
    }


    public void checkSpec(Context ctxt, boolean in_type){
	t.checkSpec(ctxt, in_type);
	for (int i = 0; i < C.length; i++){
	    C[i].checkSpec(ctxt, in_type);
	}
    }
}
