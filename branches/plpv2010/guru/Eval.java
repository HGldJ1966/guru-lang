package guru;

public class Eval extends Expr{
    
    public Expr t1;
    
    public Eval() {
        super(EVAL);
    }

    public Eval(Expr t1) {
	super(EVAL);
	this.t1 = t1;
    }

    public Expr dropAnnos(Context ctxt) {
	return new Bang();
    }

    public void do_print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("eval ");
	t1.print(w,ctxt);
    }

    public int numOcc(Expr e) {
	return t1.numOcc(e);
    }
    
    public Expr subst(Expr e, Expr x) {
	Expr n1 = t1.subst(e,x);
	if (n1 != t1)
	    return new Eval(n1);
	return this;
    }

    public Expr classify(Context ctxt) {
	t1 = t1.dropAnnos(ctxt);
	
	Expr t1a = t1.eval(ctxt);

	return new Atom(true,t1,t1a);
    }
	    
    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars)
    { }

    public java.util.Set getDependences() {
        return t1.getDependences();
    }
}
