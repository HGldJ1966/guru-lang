package guru;

import java.util.*;

public class Show extends Expr{
    
    public Expr[] P;
    
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

    public Expr classify(Context ctxt) {
	ctxt.resetNotDefEq();
	String str = "We have the following classifications:\n\n";
	for (int i = 0, iend = P.length; i < iend; i++) {
	    str += (new Integer(i)).toString() + ". ";
	    str += (P[i].classify(ctxt).dropAnnos(ctxt).toString(ctxt)
		    + "\n\n");
	    /*
	    str += "proved by\n\n      ");
	    if (P[i].construct == VAR && ctxt.isSpec((Var)P[i]))
		str += "spec ";
		str += (P[i].toString(ctxt) + "\n\n"); */
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
