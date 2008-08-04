package guru;

public class Subst extends Expr{
    
    public Expr I;
    public Expr P;
    
    public Subst() { 
	super(SUBST);
    }

    public Subst(Expr I, Expr P) {
	super(SUBST);
	this.I = I;
	this.P = P;
    }

    public Expr dropAnnos(Context ctxt) {
	return new Bang();
    }

    public void do_print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("subst ");
	I.print(w,ctxt);
	w.print(" ");
	P.print(w,ctxt);
    }
    
    public int numOcc(Expr e) {
	return I.numOcc(e) + P.numOcc(e);
    }

    public Expr subst(Expr e, Expr x) {
	Expr n1 = I.subst(e,x), n2 = P.subst(e,x);
	if (n1 != I || n2 != P)
	    return new Subst(n1,n2);
	return this;
    }

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars) {
	P.checkTermination(ctxt,IH,arg,vars);
    }

    public java.util.Set getDependences() {
        java.util.Set s = I.getDependences();
        s.addAll(P.getDependences());
        return s;
    }
}
