package guru;

public class Inc extends IncDec {
    
    public Expr t;

    public Inc() {
	super(INC);
    }
    
    public Inc(Expr t) {
	super(INC);
	this.t = t;
    }

    public void do_print(java.io.PrintStream w, 
			 Context ctxt) {
	w.print("inc ");
	t.print(w,ctxt);
    }

    public int numOcc(Expr e) {
	return t.numOcc(e);
    }

    public Expr subst(Expr e, Expr y) {
	Expr nt = t.subst(e,y);
	if (nt != t)
	    return new Inc(nt);
	return this;
    }

    public Expr classify(Context ctxt, int approx, boolean spec) {
	Expr T = t.classify(ctxt, approx, spec);
	checkType(ctxt,T.defExpandTop(ctxt));
	return T;
    }
    
    public Expr dropAnnos(Context ctxt) {
	return t.dropAnnos(ctxt);
    }

    public void checkSpec(Context ctxt, boolean in_type){
	t.checkSpec(ctxt, in_type);
    }

    public boolean termTerminates(Context ctxt) {
        return t.termTerminates(ctxt);
    }
    public void getFreeVarsComputational(Context ctxt, 
					 java.util.Collection vars) {
	t.getFreeVarsComputational(ctxt,vars);
	Expr T = t.classify(ctxt, APPROX_TRIVIAL, false);

	// when we increment in the C code, we use this type.
	T.getFreeVarsComputational(ctxt,vars);
    }

}
