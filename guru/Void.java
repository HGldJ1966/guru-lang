package guru;

public class Void extends Expr{
    public Void() { 
	super(VOID);
    }
    public void do_print(java.io.PrintStream w, Context ctxt) {
	w.print("void");
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
	return ctxt.type;
    }

    public boolean defEqNoAnno(Context ctxt, Expr e, boolean spec) {
	return (e.defExpandTop(ctxt).construct == VOID);
    }

    protected boolean defEqNoAnnoApprox(Context ctxt, Expr e, boolean spec) {
	return defEqNoAnno(ctxt,e,spec);
    }

    public void getFreeVarsComputational(Context ctxt,
					 java.util.Collection vars) { }

    public void checkSpec(Context ctxt, boolean in_type) { }

    public guru.carraway.Expr toCarrawayType(Context ctxt, boolean rttype) {
	return new guru.carraway.Void();
    }
}
