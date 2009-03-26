package guru.carraway;
import java.util.Collection;
import java.util.Iterator;

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

	ctxt.checkpointRefs();

	// stage 2

	ctxt.stage = 2;
	Sym r = t.simulate(ctxt, pos);
	if (r == null)
	    handleError(ctxt,"A global definitely aborts.\n\n"
			+"1. the global: "+c.toString(ctxt));

	// could be null if r untracked
	Context.RefStat ru = ctxt.refStatus(r); 

	Collection cr = ctxt.restoreRefs();

	if (ctxt.getFlag("debug_refs")) {
	    ctxt.w.println("Dropping pre-existing references dropped in the definition of a global:");
	    ctxt.w.flush();
	}
	Iterator it = cr.iterator();
	Context.RefStat u;
	while(it.hasNext()) {
	    u = (Context.RefStat)it.next();
		
	    if (u.created) {
		if (u.ref == r) 
		    continue;
		c.simulateError(ctxt,"The definition of a global is leaking a reference.\n\n"
				+"1. the global: "+c.toString(ctxt)
				+"\n\n2. the reference "+r.refString(ctxt));
	    }
	    else {
		// drop the reference from the context as it will exist after processing this global.
		if (ctxt.refStatus(u.ref) != null) 
		    ctxt.dropRef(u.ref, pos);
	    }
	}

	if (ru != null)
	    ctxt.setSubst(c,ctxt.newRef(pos,ru));

	t.comment_expr(c,ctxt);

	// stage 3
 
	ctxt.stage = 3;
	T.print(ctxt.cw,ctxt);
	ctxt.cw.print(" ");
	c.print(ctxt.cw,ctxt);
	ctxt.cw.println(";\n");

	String initn = "init_"+c.toString(ctxt);
	FunTerm f = new FunTerm(initn, t.linearize(ctxt, pos, c), pos);
	
	ctxt.addGlobalInit(initn);

	f.print(ctxt.cw,ctxt);
	ctxt.cw.flush();
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
