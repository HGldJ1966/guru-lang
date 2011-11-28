package guru;

import java.util.*;

public class Show extends Expr{
    
    public Expr[] P;
    
    protected int step;

    public Show() { 
	super(SHOW);
    }

    public Show(Expr[] P) {
	super(SHOW);
	this.P = P;
    }	    

    public Expr dropAnnos(Context ctxt) {
	return new Bang();
    }

    public void do_print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("show ");
	for (int i = 0, iend = P.length; i < iend; i++) {
	    P[i].print(w,ctxt);
	    w.print(" ");
	}
	w.print("end");
    }

    public int numOcc(Expr e) {
	int n = 0;
	for (int i = 0, iend = P.length; i < iend; i++) 
	    n += P[i].numOcc(e);
	return n;
    }
    
    public Expr subst(Expr e, Expr x) {
	Expr []nP = new Expr[P.length];
	boolean changed = false;
	for (int i = 0, iend = P.length; i < iend; i++) {
	    nP[i] = P[i].subst(e,x);
	    if (nP[i] != P[i])
		changed = true;
	}
	if (changed)
	    return new Show(nP);
	return this;
    }

    protected String show_proof(Context ctxt, Expr pf, boolean in_trans, boolean multiple_proofs) {
	String str = (!multiple_proofs || !in_trans ? (new Integer(step++)).toString() + ". " : "   ");
	if (pf.construct == TRANS) {
	    Expr c1 = ((Trans)pf).P1.classify(ctxt).dropAnnos(ctxt);
	    Atom a1 = (Atom)c1;
	    str += a1.Y1.toString(ctxt) + " =\n\n";
	    str += show_proof(ctxt,((Trans)pf).P2,true,multiple_proofs);
	}
	else if (pf.construct == TRANSS) {
             step--;
	     return show_proof(ctxt, ((Transs)pf).toTrans(), in_trans, multiple_proofs);
        }
	else {
	    Expr F = pf.classify(ctxt).dropAnnos(ctxt);
	    if (in_trans) {
		Atom a = (Atom)F;
		str += a.Y1.toString(ctxt) + (a.equality ? " =\n\n" : " !=\n\n");
		str += (!multiple_proofs ? (new Integer(step++)).toString() + ". " : "   ");
		str += a.Y2.toString(ctxt) + "\n\n";
	    }
	    else
		str += F.toString(ctxt)+ "\n\n";
	}
	return str;
    }

    public Expr classify(Context ctxt) {
	ctxt.resetNotDefEq();
	String str = "We have the following classifications:\n\n";
	step = 1;
	for (int i = 0, iend = P.length; i < iend; i++) {
	    P[i].classify(ctxt);
	    str += show_proof(ctxt,P[i],false,iend > 1);
	}

	handleError(ctxt, str);
	
	return null;
    }

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars) {
	// we do not bother checking termination since checking the
	// classifier of this proof will generate an error anyway.
    }

    public java.util.Set getDependences() {
        java.util.Set s = new TreeSet();
        for(int i = 0, n = P.length; i < n; ++i)
            s.addAll(P[i].getDependences());
        return s;
    }
}
