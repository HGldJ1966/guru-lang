package guru;

import java.util.*;

public class Untracked extends Command {
    public Const d;
    public Untracked() {
	super(UNTRACKED);
    }

    public void process(Context ctxt) {
	if (!d.isTypeOrKind(ctxt))
	    handleError(ctxt,"A command to make a type untracked is "
			+"being\nissued, but the given constant is not"
			+" a declared or defined type.\n"
			+"1. The constant: "+d.toString(ctxt));
	ctxt.makeUntracked(d);
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("Untracked ");
	d.print(w,ctxt);
	w.println(".");
	w.flush();
    }
}