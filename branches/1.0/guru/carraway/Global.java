package guru.carraway;

public class Global extends Command {
    Sym c;
    Expr t;

    public Global() {
	super(GLOBAL);
    }

    public void process(Context ctxt) {

	// stage 0

	ctxt.stage = 0;
	ctxt.commentBox(c.toString(ctxt));
	t.comment_expr(c,ctxt);

	// stage 1 

	ctxt.stage = 1;
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

	t.comment_expr(c,ctxt);

	// stage 2
 
	ctxt.stage = 2;
	T.print(ctxt.cw,ctxt);
	c.print(ctxt.cw,ctxt);
	ctxt.cw.println(";\n");

	String initn = "init_"+c.toString(ctxt);
	FunTerm f = new FunTerm(initn, t.linearize(ctxt, pos, c), pos);
	
	ctxt.addGlobalInit(initn);

	f.comment_expr(null,ctxt);
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
