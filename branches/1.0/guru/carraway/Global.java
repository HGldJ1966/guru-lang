package guru.carraway;

public class Global extends Command {
    Sym c;
    Expr t;

    public Global() {
	super(GLOBAL);
    }

    public void process(Context ctxt) {
	t.comment_expr(0,ctxt);
	Expr T = t.simpleType(ctxt);
	if (T.construct == Expr.VOID) 
	    handleError(ctxt,"The type of a global is void.\n\n"
			+"1. the global: "+c.toString(ctxt)
			+"\n\n2. its type: "+T.toString(ctxt));
	ctxt.addGlobal(c,T,t);

	Sym r = t.simulate(ctxt, pos);
	if (r == null)
	    handleError(ctxt,"A global definitely aborts.\n\n"
			+"1. the global: "+c.toString(ctxt));
	ctxt.setSubst(c,r);

	t.comment_expr(1,ctxt);
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("Global ");
	c.print(w,ctxt);
	w.print(" = ");
	t.print(w,ctxt);
	w.println(".");
    }
}
