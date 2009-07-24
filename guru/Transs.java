package guru;

import java.util.*;

public class Transs extends Expr{
    
    public Expr[] P; // should be non-empty
 
    protected int step;   
    
    public Transs() { 
	super(TRANSS);
    }

    public Transs(Expr[] P) {
	super(TRANSS);
	this.P = P;
    }

    public Expr dropAnnos(Context ctxt) {
	return new Bang();
    }

    public void do_print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("transs ");
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
	    return new Transs(nP);
	return this;
    }

    public Expr toTrans() {
       Expr q = P[P.length-1];
       for (int i = P.length-2, iend = 0; i >= iend; i--) {
           q = new Trans(P[i], q);
           q.pos = P[i].pos;
       }
       return q;
    }


    public Expr classify(Context ctxt) {
       return toTrans().classify(ctxt);  
   }

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars) {  //what is this doing?
	for(int i = 0, n = P.length; i < n; ++i)
            P[i].checkTermination(ctxt,IH,arg,vars);
    }

    public java.util.Set getDependences() {
        java.util.Set s = new TreeSet();
        for(int i = 0, n = P.length; i < n; ++i)
            s.addAll(P[i].getDependences());
        return s;
    }

}
