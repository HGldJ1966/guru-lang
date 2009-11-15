package guru;

public class Stub extends Command {
    public Const c;
    public Stub() {
	super(STUB);
    }

    public void process(Context ctxt) {
	if (!ctxt.isDefined(c))
	    handleError(ctxt,"A command to stub out a defined constant is "
			+"being\nissued, but the given constant is not"
			+" defined.\n"
			+"1. The constant: "+c.toString(ctxt));
	if (!c.isTerm(ctxt))
	    handleError(ctxt,"A command to stub out a defined constant is "
			+"being\nissued, but the given constant is not"
			+" defined to be a term.\n"
			+"1. The constant: "+c.toString(ctxt)+"\n"
			+"2. What it is defined to equal: "
			+c.defExpandTop(ctxt).toString(ctxt));
	ctxt.makeOpaque(c);
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("Stub ");
	c.print(w,ctxt);
	w.println(".");
	w.flush();
    }
}
