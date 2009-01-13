package guru;

public class Inductive extends Command {
    public Const d;
    public Expr K;
    public Const[] c;
    public Expr[] D;

    public Inductive() {
	super(INDUCTIVE);
    }

    public void process(Context ctxt) {
	Expr superkind = K.classify(ctxt);
	if (superkind.construct != Expr.TKIND)
	    handleError(ctxt,
			"Type constructor's declared classifier is not a "
			+"kind:\n"+superkind.toString(ctxt));

	int iend = c.length;

	/*
	 * We must (1) add all the term ctors, before (2) classifying
	 * their declared types.  Step (1) is needed so that we do not
	 * erroneously conclude that the datatype is flat in the
	 * middle of step (2).  We will generally call ctxt.isFlat()
	 * during step (2), because we have to set ownership status
	 * on the constructor's arguments.
	 */

	// step (1)
	for (int i = 0; i < iend; i++){
	    ctxt.addTermCtor(c[i],d,D[i]);
	
	}
	// step (2)
	for (int i = 0; i < iend; i++) {
	    Expr cl = D[i].classify(ctxt);
	    
	    if (cl.construct != Expr.TYPE)
		handleError(ctxt,"Classifier declared for term constructor \""+
			    c[i].toString(ctxt)+"\" is not a type.\n"+
			    "1. its classifier: "+cl.toString(ctxt));
	    
	    if (D[i].construct == Expr.FUN_TYPE){
		FunType ft = (FunType) D[i];
		for (int j = 0; j < ft.vars.length; j++)
		    if (ft.owned[j].status == Ownership.SPEC)
			ctxt.markSpec(ft.vars[j]);
	    }
	}
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("Inductive ");
	d.print(w, ctxt);
	w.print(" : ");
	K.print(w, ctxt);
	w.print(" := ");
	boolean first = true;
	for (int i = 0, iend = c.length; i < iend; i++) {
	    if (first)
		first = false;
	    else
		w.print(" | ");
	    c[i].print(w, ctxt);
	    w.print(" : ");
	    D[i].print(w, ctxt);
	}
	w.println(".");
    }

    public java.util.Set getDependences() {
        java.util.Set s = K.getDependences();
        for(int i = 0, n = D.length; i < n; ++i)
            s.addAll(D[i].getDependences());
        return s;
    }
}
