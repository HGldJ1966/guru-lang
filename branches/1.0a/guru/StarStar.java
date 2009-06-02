package guru;

public class StarStar extends Expr{
    
    public StarStar() { 
	super(STARSTAR);
    }

    public Expr dropAnnos(Context ctxt) {
	return this;
    }

    public void do_print(java.io.PrintStream w, Context ctxt) {
	w.print("**");
    }
    
    public int numOcc(Expr e) {
	return (this == e) ? 1 : 0;
    }

    public Expr subst(Expr e, Expr x) {
	return (this == x) ? e : this;
    }

    public isInstC isInstance(Context ctxt, Expr ee) {
	return new isInstC(true);
    }

    public boolean defEqNoAnno(Context ctxt, Expr ee, boolean spec) {
	return this == ee.defExpandTop(ctxt,true,spec);
    }
}
