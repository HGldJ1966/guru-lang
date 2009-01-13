package guru;

import java.util.Stack;

public class ProofApp extends App{

    public ProofApp() { 
	super(PROOF_APP);
    }
    
    public ProofApp(App a) {
	super(PROOF_APP, a.head, a.X);
    }

    public void do_print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("[");
	super.do_print(w,ctxt);
	w.print("]");
    }

    public Expr subst(Expr e, Expr x) {
	App s = (App)super.subst(e,x);
	if (s != this)
	    return new ProofApp(s);
	return this;
    }
    
    public Expr do_rewrite(Context ctxt, Expr e, Expr x, Stack boundVars)
    {
    	throw new RuntimeException("do_rewrite called on an inappropriate expression with construct " + construct);
    }

    public Expr classify(Context ctxt) {
	Expr cl = head.classify(ctxt);

	/* check argument types first, before calling termTerminates,
	   since we want to insert any spec annotations on TermApps
	   first (this is done by classification). */
	Expr ret = apply_classifier(FORALL, 0, true, ctxt, cl, 0);

	App e = spineForm(ctxt, false, true, false);
        for (int i = 0, iend = e.X.length; i < iend; i++) 
            e.X[i].checkTermination(ctxt);
	return ret;
    }

    public Expr dropAnnos(Context ctxt) {
  	return new Bang();
    }
	
    public boolean isAnnotation(Context ctxt){
	return true;
    }

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars) {
	App e = spineForm(ctxt, false, true,
			  false /* no need to expand defs */);
	int iend = e.X.length;
	if (e.head == IH) {
	    if (arg >= iend)
		handleError(ctxt,
			    "Induction hypothesis is being used without enough"
			    +" arguments\nto observe structural decrease in"
			    +" the parameter of induction.\n"
			    +"1. The use of the IH:"+e.toString(ctxt));
	    boolean found = false;
            for (int i = 0; i < iend; i++) {
              Expr tmp = e.X[i].dropAnnos(ctxt);
              for (int j = 0, jend = vars.length; j < jend; j++)
                if (tmp == vars[j]) {
                  found = true;
                  break;
                }
            }
	    if (!found) {
		String s = "";
		for (int j = 0, jend = vars.length; j < jend; j++)
		    s += vars[j].toString(ctxt) + " ";
		handleError(ctxt,
			    "Induction hypothesis is being used without a"
			    +" structurally\nsmaller argument for"
			    +" the parameter of induction.\n"
			    +"1. The use of the IH: "+e.toString(ctxt)+"\n"
			    +"2. The argument that should decrease: "
			    +(new Integer(arg))+"\n"
			    +"3. The variables that could be used: "+s+"\n");
	    }
	}
	for (int i = 0; i < iend; i++)
	    e.X[i].checkTermination(ctxt,IH,arg,vars);
    }

}
