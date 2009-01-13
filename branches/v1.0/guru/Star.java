package guru;

public class Star extends Expr{
    
    public Star() { 
	super(STAR);
    }

    public void do_print(java.io.PrintStream w, Context ctxt) {
	w.print("*");
    }
    
    public Expr dropAnnos(Context ctxt) {
	return this;
    }

    public int numOcc(Expr e) {
	return (this == e) ? 1 : 0;
    }

    public Expr subst(Expr e, Expr x) {
	return (this == x) ? e : this;
    }
    
    public isInstC isInstance(Context ctxt, Expr ee) {
	return new isInstC(ee);
    }

    public boolean defEqNoAnno(Context ctxt, Expr ee) {
	return this == ee.defExpandTop(ctxt);
    }
}
