package guru;

public class Forall extends Abstraction {

    public Forall() {
	super(FORALL);
    }

    public Forall(Abstraction a) {
	super(FORALL, a.vars, a.types, a.body);
    }

    public Forall(Var[] vars, Expr[] types, Expr body) {
	super(FORALL, vars, types, body);
    }

    public void do_print(java.io.PrintStream w,
		      Context ctxt) {
	w.print("Forall");
	super.do_print(w, ctxt);
    }

    public Expr subst(Expr e, Expr x) {
	Abstraction s = (Abstraction)super.subst(e,x);
	if (s != this)
	    return new Forall(s);
	return this;
    }

    public Abstraction rename(Context ctxt, Position p) {
	return new Forall(super.rename(ctxt,p));
    }

    public Expr classify(Context ctxt, int approx, boolean spec) {
	if (ctxt.getFlag("debug_classify_forall")) {
	    ctxt.w.println("Classifying Forall-formula: "+toString(ctxt));
	    ctxt.w.flush();
	}

	checkClassifiers(ctxt, approx, true);
	body.classify(ctxt,approx,spec);
	return ctxt.formula;
    }

    public Expr next() {
	Expr ret = super.next();
	if (ret.construct == ABSTRACTION)
	    return new Forall((Abstraction)ret);
	return ret;
    }

    public Expr dropAnnos(Context ctxt) {
	Expr ret = super.dropAnnos(ctxt);
	if (ret.construct == ABSTRACTION)
	    return new Forall((Abstraction)ret);
	return ret;
    }
    public Expr instantiate(Expr e) {
	Expr ret = super.instantiate(e);
	if (ret.construct == ABSTRACTION)
	    return new Forall((Abstraction)ret);
	return ret;
    }

    public void getFreeVarsComputational(Context ctxt,
					 java.util.Collection vars) { }
}
