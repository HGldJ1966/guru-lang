package guru;

public class Aclash extends Expr{

    public Expr t;

    public Aclash() {
	super(ACLASH);
    }

    public Aclash(Expr t) {
	super(ACLASH);
	this.t = t;
    }

    public void do_print(java.io.PrintStream w,
		      Context ctxt) {
	w.print("aclash ");
	t.print(w,ctxt);
    }

    public int numOcc(Expr e) {
	return t.numOcc(e);
    }

    public Expr subst(Expr e, Expr x) {
	Expr nt = t.subst(e,x);
	if (nt != t)
	    return new Aclash(nt);
	return this;
    }

    public Expr classify(Context ctxt) {
        if(!t.termTerminates(ctxt))
            handleError(ctxt,
                        "The term given to aclash must terminate; it "
                        +"may need a terminates cast:\n"
                        +"The term: "+t.toString(ctxt));
	return new Atom(false, new Abort(new Bang()), t);
    }

    public Expr dropAnnos(Context ctxt) {
	return new Bang();
    }

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars)
    { }

    public java.util.Set getDependences() {
        return t.getDependences();
    }
}
