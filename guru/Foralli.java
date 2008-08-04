package guru;

public class Foralli extends Abstraction {

    public Foralli() {
	super(FORALLI);
    }

    public Foralli(Abstraction a) {
	super(FORALLI, a.vars, a.types, a.body);
    }

    public void do_print(java.io.PrintStream w,
		      Context ctxt) {
	w.print("foralli");
	super.do_print(w, ctxt);
    }

    public Expr subst(Expr e, Expr x) {
	Abstraction s = (Abstraction)super.subst(e,x);
	if (s != this)
	    return new Foralli(s);
	return this;
    }

    public Expr instantiate(Expr e) {
	Expr ret = super.instantiate(e);
	if (ret.construct == ABSTRACTION)
	    return new Foralli((Abstraction)ret);
	return ret;
    }

    public Expr classify(Context ctxt) {
	checkClassifiers(ctxt,0,true);
	return new Forall(vars, types, body.classify(ctxt));
    }

    public boolean defEqNoAnno(Context ctxt, Expr ee) {
	return true;
    }

    public Expr dropAnnos(Context ctxt) {
	return new Bang();
    }

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] v) {
	if (isBound(IH))
	    return;
	for (int i = 0, iend = v.length; i < iend; i++)
	    if (isBound(v[i]))
		handleError(ctxt,
			    "A pattern variable in an induction-proof is being"
			    +" rebound, and we\ncurrently do not support"
			    +" that.\n"
			    +"1. the variable: "+v[i].toString(ctxt));

	body.checkTermination(ctxt,IH,arg,v);
    }
}
