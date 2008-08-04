package guru;

public class Exists extends Abstraction {

    public Exists() {
	super(EXISTS);
    }

    public Exists(Abstraction a) {
	super(EXISTS, a.vars, a.types, a.body);
    }

    public Exists(Var[] vars, Expr[] types, Expr body) {
	super(EXISTS, vars, types, body);
    }

    public Exists(Var v, Expr B, Expr body) {
	super(EXISTS,v,B,body);
    }

    public void do_print(java.io.PrintStream w,
		      Context ctxt) {
	w.print("Exists");
	super.do_print(w, ctxt);
    }

    public Expr subst(Expr e, Expr x) {
	Abstraction s = (Abstraction)super.subst(e,x);
	if (s != this)
	    return new Exists(s);
	return this;
    }

    public Expr dropAnnos(Context ctxt) {
	Expr ret = super.dropAnnos(ctxt);
	if (ret.construct == ABSTRACTION)
	    return new Exists((Abstraction)ret);
	return ret;
    }

    public Expr classify(Context ctxt, int approx, boolean spec) {
	if (ctxt.getFlag("debug_classify_exists")) {
	    ctxt.w.println("Classifying Exists-formula: "+toString(ctxt));
	    ctxt.w.flush();
	}
	checkClassifiers(ctxt, approx, spec);
	body.classify(ctxt,approx,spec);
	return ctxt.formula;
    }
    public void getFreeVarsComputational(Context ctxt,
					 java.util.Collection vars) { }
}
