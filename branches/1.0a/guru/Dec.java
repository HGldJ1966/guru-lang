package guru;

public class Dec extends IncDec {
    
    // I needs to be terminating, since we drop it when dropping annos.

    public Expr I, T, t;
    
    public Dec() {
	super(DEC);
    }
    
    public Dec(Expr I, Expr t, Expr T) {
	super(DEC);
	this.I = I;
	this.t = t;
	this.T = T;
    }

    public void do_print(java.io.PrintStream w, 
			 Context ctxt) {
	w.print("dec ");
	I.print(w,ctxt);
	w.print(" ");
	if (ctxt.getFlag("print_inc_dec_types")) {
	    w.print("%- ");
	    if (T == null)
		w.print(" <null>");
	    else
		T.print(w,ctxt);
	    w.print(" -% ");
	}
	t.print(w,ctxt);
    }

    public int numOcc(Expr e) {
	return I.numOcc(e) + t.numOcc(e);
    }

    public Expr subst(Expr e, Expr x) {
	Expr nI = I.subst(e,x), nt = t.subst(e,x);
	Expr nT = null;
	if (T != null)
	    nT = T.subst(e,x);
	if (nI != I || nt != t || nT != T)
	    return new Dec(nI,nt,nT);
	return this;
    }

    public Expr classify(Context ctxt, int approx, boolean spec) {
	if (T == null)
	    T = I.classify(ctxt, approx, spec);
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

	if (T == null)
	    T = I.classify(ctxt, APPROX_TRIVIAL, false).defExpandTop(ctxt);

	// when we decrement in the C code, we use this type.
	T.getFreeVarsComputational(ctxt,vars);

    }
}
