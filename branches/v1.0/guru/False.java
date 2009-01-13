package guru;

public class False extends Expr{
    public False() { 
	super(FALSE);
    }
    public void do_print(java.io.PrintStream w, Context ctxt) {
	w.print("False");
    }

    public Expr dropAnnos(Context ctxt) {
	return this;
    }

    public int numOcc(Expr e) {
	return (this == e) ? 1 : 0;
    }

    public Expr subst(Expr e, Expr x) {
	return this;
    }
    
    public Expr classify(Context ctxt, int approx, boolean spec) {
	return ctxt.formula;
    }

    public boolean defEqNoAnno(Context ctxt, Expr e, boolean spec) {
	return e.defExpandTop(ctxt).construct == FALSE;
    }
}
