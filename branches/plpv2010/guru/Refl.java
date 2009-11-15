package guru;

public class Refl extends Expr{
    
    public Expr Y;
    
    public Refl() { 
	super(REFL);
    }

    public Refl(Expr Y) {
	super(REFL);
	this.Y = Y;
    }

    public Expr dropAnnos(Context ctxt) {
	return new Bang();
    }

    public void do_print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("refl ");
	Y.print(w,ctxt);
    }

    public int numOcc(Expr e) {
	return Y.numOcc(e);
    }

    public Expr subst(Expr e, Expr x) {
	Expr n = Y.subst(e,x);
	if (n != Y)
	    return new Refl(n);
	return this;
    }
    
    public Expr classify(Context ctxt) {
	return new Atom(true, Y, Y);
    }

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars)
    { }

    public java.util.Set getDependences() {
        return Y.getDependences();
    }
}
