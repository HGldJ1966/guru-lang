package guru;

import java.util.*;

public class Opaque extends Command {
    public Const d;
    public Opaque() {
	super(OPAQUE);
    }

    public void process(Context ctxt) {
	if (!d.isTypeOrKind(ctxt))
	    handleError(ctxt,"A command to make a type opaque is "
			+"being\nissued, but the given constant is not"
			+" a declared or defined type.\n"
			+"1. The constant: "+d.toString(ctxt));
	ctxt.makeOpaque(d);
	if (ctxt.isTypeCtor(d)) {
	    Iterator it = ctxt.getTermCtors(d).iterator();
	    while (it.hasNext()) {
		Const c = (Const)it.next();
		ctxt.makeOpaque(c);
	    }
	}
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("Opaque ");
	d.print(w,ctxt);
	w.println(".");
	w.flush();
    }
}