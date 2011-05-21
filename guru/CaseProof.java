package guru;

import java.util.*;
import java.io.*;

public class CaseProof extends CasesExpr{
    public CaseProof() {
	super(MATCH);
    }

    public CaseProof(Expr t, Var x1, Var x2, Case[] C) {
	super(MATCH, t, x1, x2, C);
    }

    public void do_print(java.io.PrintStream w, 
			 Context ctxt) {
	w.print("case ");
	do_print1(w,ctxt);
	do_print2(w,ctxt);
    }

    public Expr classify(Context ctxt, int approx, boolean spec) {
	t.classify(ctxt,approx,spec);// do this first so we can drop annotations correctly in the termination check
	t.checkTermination(ctxt);
	return super.classify(ctxt,approx,spec);
    }

    public Expr dropAnnos(Context ctxt) {
	return new Bang();
    }

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars) {
	// TODO: if t is in vars, exchange t for C[i].x in the rec. call
	for (int i = 0, iend = C.length; i < iend; i++) 
	    C[i].body.checkTermination(ctxt, IH, arg, vars);
    }

}
