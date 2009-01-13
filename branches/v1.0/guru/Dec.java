package guru;

public class Dec extends IncDec {
    
    // I needs to be terminating, since we drop it when dropping annos.

    public Expr I, t;
    
    public Dec() {
	super(DEC);
    }
    
    public Dec(Expr I, Expr t) {
	super(DEC);
	this.I = I;
	this.t = t;
    }

    public void do_print(java.io.PrintStream w, 
			 Context ctxt) {
	w.print("dec ");
	I.print(w,ctxt);
	w.print(" ");
	t.print(w,ctxt);
    }

    public int numOcc(Expr e) {
	return I.numOcc(e) + t.numOcc(e);
    }

    public Expr subst(Expr e, Expr x) {
	Expr nI = I.subst(e,x), nt = t.subst(e,x);
	if (nI != I || nt != t)
	    return new Dec(nI,nt);
	return this;
    }

    public Expr classify(Context ctxt, int approx, boolean spec) {
	Expr T = I.classify(ctxt, approx, spec);
	checkType(ctxt,T.defExpandTop(ctxt,false,spec));
	return t.classify(ctxt,approx,spec);
    }
    
    public Expr dropAnnos(Context ctxt) {
	return t.dropAnnos(ctxt);
    }
    public void checkSpec(Context ctxt, boolean in_type){
	I.checkSpec(ctxt, in_type);
	t.checkSpec(ctxt, in_type);
    }
    public void getFreeVarsComputational(Context ctxt, 
					 java.util.Collection vars) {
	I.getFreeVarsComputational(ctxt,vars);
	t.getFreeVarsComputational(ctxt,vars);

	Expr T = I.classify(ctxt, APPROX_TRIVIAL, false);

	// when we decrement in the C code, we use this type.
	T.getFreeVarsComputational(ctxt,vars);

    }
}
