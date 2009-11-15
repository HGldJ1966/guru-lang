package guru;

public class Formula extends Expr{
    public Formula() { 
	super(FORMULA);
    }
    public void do_print(java.io.PrintStream w, Context ctxt) {
	w.print("formula");
    }

    public int numOcc(Expr e) {
	return (this == e) ? 1 : 0;
    }
    public Expr subst(Expr e, Expr x) {
	return this;
    }

    public Expr classify(Context ctxt, int approx, boolean spec) {
	return ctxt.fkind;
    }

    public Expr dropAnnos(Context ctxt) {
	return this;
    }

    public boolean defEqNoAnno(Context ctxt, Expr e) {
	return (this == e.defExpandTop(ctxt));
    }
}
