package guru;

import java.util.*;
import java.io.*;

public class Match extends CasesExpr{
    public Expr T;
    public boolean consume_scrut;
    
    public Match() {
	super(MATCH);
    }

    public Match(CasesExpr a, Expr T, boolean consume_scrut) {
	super(MATCH, a);
	this.T = T;
	this.consume_scrut = consume_scrut;
    }

    public Match(Expr t, Var x1, Var x2, Expr T, Case[] C, boolean consume_scrut) {
	super(MATCH, t, x1, x2, C);
	this.T = T;
	this.consume_scrut = consume_scrut;
    }

    public void do_print(java.io.PrintStream w, 
			 Context ctxt) {
	w.print("match ");
	if (!consume_scrut)
	    w.print("! ");
	do_print1(w,ctxt);
	if (T != null) {
	    w.print(" return ");
	    T.print(w,ctxt);
	}
	do_print2(w,ctxt);
    }

    public int hashCode_h(Context ctxt) {
	int h = t.hashCode_h(ctxt);
	for (int i = 0, iend = C.length; i < iend; i++) 
	    h += C[i].hashCode_h(ctxt);
	return h;
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
	    return new Match(nC, nT, consume_scrut);
	return this;
    }
    
    public Expr do_rewrite(Context ctxt, Expr e, Expr x, Stack boundVars) {
	Expr nT = T;
	CasesExpr nC = (CasesExpr)super.do_rewrite(ctxt,e,x,boundVars);
	if (nT != T || nC != this)
	    return new Match(nC, nT, consume_scrut);
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
	    return new Match((CasesExpr)r,T,consume_scrut);
	return this;
    }

    // we assume proofs have been dropped already
    public Expr evalStep(Context ctxt) {
	Expr e = t.evalStep(ctxt);
	if (e != t)
	    return new Match(e,x1,x2,T,C,consume_scrut);
	if (t.construct == ABORT)
	    //return ctxt.abort;
		return t;
	
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


    public void checkSpec(Context ctxt, boolean in_type, Position p){
	t.checkSpec(ctxt, in_type, pos);
	for (int i = 0; i < C.length; i++){
	    C[i].checkSpec(ctxt, in_type, pos);
	}
    }

    public guru.carraway.Expr toCarraway(Context ctxt) {
	guru.carraway.Match m = new guru.carraway.Match();
	m.pos = pos;
	m.consume_scrut = consume_scrut;
	m.t = t.toCarraway(ctxt);
	int iend = C.length;
	ArrayList a = new ArrayList();
	for (int i = 0; i < iend; i++)
	    if (!C[i].impossible)
		a.add((guru.carraway.Case)C[i].toCarraway(ctxt));
	
	m.C = guru.carraway.Parser.toCaseArray(a);
	m.consume_scrut = consume_scrut;
	return m;
    }
}
