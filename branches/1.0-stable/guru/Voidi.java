package guru;

public class Voidi extends Expr{
    public Voidi() { 
	super(VOIDI);
    }
    public void do_print(java.io.PrintStream w, Context ctxt) {
	w.print("voidi");
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
    
    public int hashCode_h(Context ctxt) {
	return 29;
    }

    public Expr classify(Context ctxt, int approx, boolean spec) {
	return ctxt.voidt;
    }

    public boolean defEqNoAnno(Context ctxt, Expr e, boolean spec) {
	return (e.defExpandTop(ctxt).construct == VOIDI);
    }

    protected boolean defEqNoAnnoApprox(Context ctxt, Expr e, boolean spec) {
	return defEqNoAnno(ctxt,e,spec);
    }

    public void getFreeVarsComputational(Context ctxt,
					 java.util.Collection vars) { }

    public void checkSpec(Context ctxt, boolean in_type, Position p) { }
}
