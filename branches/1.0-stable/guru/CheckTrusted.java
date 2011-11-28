package guru;

import java.util.*;

public class CheckTrusted extends Command {
    public CheckTrusted() {
	super(CHECK_TRUSTED);
    }

    public void process(Context ctxt) {
	Iterator it = ctxt.getTrustedDefs().iterator();
	while (it.hasNext()) {
	    Const c = (Const)it.next();
	    Expr def = ctxt.getDefBody(c);
	    Expr T = ctxt.getClassifier(c);
	    Expr cT = def.classify(ctxt);
	    if (!T.defEq(ctxt,cT)) 
		handleError(ctxt,"The classifier computed for the body of a "
			    +"previously trusted\ndefinition does not "
			     +"match the declared classifier.\n"
			    +"1. the defined constant: "+c.toString(ctxt)+"\n"
			    +"2. declared classifier: "+T.toString(ctxt)+"\n"
			    +"3. computed classifier: "+cT.toString(ctxt));
	    ctxt.clearTrusted();
	}
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	w.println("CheckTrusted.");
	w.flush();
    }
}