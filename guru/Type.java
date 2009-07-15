package guru;

public class Type extends Expr{
    public Type() { 
	super(TYPE);
    }
    public void do_print(java.io.PrintStream w, Context ctxt) {
	w.print("type");
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
	return ctxt.tkind;
    }



    public boolean defEqNoAnno(Context ctxt, Expr e, boolean spec) {
	return (e.defExpandTop(ctxt).construct == TYPE);
    }

    protected boolean defEqNoAnnoApprox(Context ctxt, Expr e, boolean spec) {
	return defEqNoAnno(ctxt,e,spec);
    }

    public void getFreeVarsComputational(Context ctxt,
					 java.util.Collection vars) { }

    public void checkSpec(Context ctxt, boolean in_type, Position p) { }

    public guru.carraway.Expr toCarrawayType(Context ctxt, boolean dtype) {
	if (dtype)
	    return new guru.carraway.Untracked();
	else
	    return new guru.carraway.Type();
    }
}
