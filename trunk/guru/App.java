package guru;

import java.util.*;

public class App extends Expr{
    
    public Expr head;
    public Expr [] X;
    
    public App(int construct) {
	super(construct);
    }

    public App(int construct, Expr head, Expr[] X) {
	super(construct);
	if (head == null)
	    throw new IllegalArgumentException();
	this.head = head;
	this.X = X;
    }

    protected void print_arg(java.io.PrintStream w, Context ctxt, int i) {
	X[i].print(w,ctxt);
    }

    public void do_print(java.io.PrintStream w, Context ctxt) {
	head.print(w,ctxt);
	for (int i = 0, iend = X.length; i < iend; i++) {
	    w.print(" ");
	    print_arg(w,ctxt,i);
	}
    }

    public int numOccInArgs(Expr e) {
	int n = 0;
	for (int i = 0, iend = X.length; i < iend; i++)
	    n += X[i].numOcc(e);
	return n;
    }

    public int numOcc(Expr e) {
	return head.numOcc(e) + numOccInArgs(e);
    }

    public boolean isApp() {
	return true;
    }

    // convert this App to spine form, in which the head of the App is not
    // an App (and is top-level def-expanded).
    public Expr getHead(Context ctxt, boolean spec) {
	return (spineForm(ctxt, false, spec, true)).head;
    }

    public Expr subst(Expr e, Expr x) {
	int iend = X.length;
	Expr[] sX = new Expr[iend];
	boolean changed = false;
	for (int i = 0; i < iend; i++) {
	    sX[i] = X[i].subst(e,x);
	    if (sX[i] != X[i])
		changed = true;
	}
	Expr h = head.subst(e,x);
	if (h != head || changed)
	    return new App(construct, h, sX);
	return this;
    }

    public Expr do_rewrite(Context ctxt, Expr e, Expr x, Stack boundVars) {
    	int iend = X.length;
    	Expr[] sX = new Expr[iend];
    	boolean changed = false;
    	for (int i = 0; i < iend; i++) 
    	{
    	    sX[i] = X[i].rewrite(ctxt,e,x,boundVars);
    	    if (sX[i] != X[i])
    		changed = true;
    	}
    	Expr h = head.rewrite(ctxt,e,x,boundVars);
    	if (h != head || changed)
    	    return new App(construct, h, sX);
    	return this;
    }

    // if cl is a Fun-type or Fun-kind, check that the
    // arg's classifier matches the domain classifier,
    // and return the instantiated range classifier.
    protected Expr apply_classifier(int expected_construct, int approx,
				    boolean spec,
				    Context ctxt, Expr cl, int arg) {
	if (arg == X.length)
	    // we have consumed all the arguments in this App
	    return cl;

	cl = cl.defExpandTop(ctxt, false, spec);
	Expr err_tgt = ((X[arg].construct == VAR || X[arg].construct == CONST)
			? this : X[arg]);
	if (cl.construct != expected_construct)
	    err_tgt.handleError
		(ctxt,
		 "A term does not accept enough arguments to apply to"
		 +" argument "+(new Integer(arg))+".\n"+
		 "1. The classifier of the head at that point:\n"
		 +cl.toString(ctxt)
		 +"\n2. The application: "+toString(ctxt));
	Abstraction e = (Abstraction)cl;
	
	// if we are doing approximate checking and the argument is a proof
	// (including !, which could also be for a dropped type), then
	// we do not type check that argument.

	if (approx == NO_APPROX || (!isTypeOrKind(ctxt)
				    && !X[arg].isProof(ctxt)
				    && X[arg].construct != BANG)) {
	    /* if this is a TypeApp, and we are doing approximate
	       checking, we do not bother classifying the argument.
	       We assume any bangs here were put there by us after
	       real type checking, so we do not worry about them,
	       either. */
	    if (ctxt.getFlag("debug_classify_apps")) {
		ctxt.w.println("(About to classify argument "+
			       (new Integer(arg)).toString());
		ctxt.w.flush();
	    }

	    Expr xc = X[arg].classify(ctxt, approx, spec);
	    
	    if (ctxt.getFlag("debug_classify_apps")) {
		ctxt.w.println(") Done. About to test def. eq.:"
			       +"\n1. "+e.types[0].toString(ctxt)
			       +"\n2. "+xc.toString(ctxt));
		ctxt.w.flush();
	    }

	    if (!e.types[0].defEq(ctxt, xc, approx, spec))
		err_tgt.handleError
		    (ctxt,
		     "In an application, the classifier of argument "
		     +(new Integer(arg))+
		     " is not definitionally equal\nto the expected one:\n"
		     +"1. the argument: "+X[arg].toString(ctxt)+"\n"
		     +"2. argument's classifier: "+xc.toString(ctxt)+"\n"
		     +"3. expected classifier: "+e.types[0].toString(ctxt));
	}
	Expr Xarg = X[arg];
	Expr next = e.instantiate(Xarg);
	arg++;
	return apply_classifier(expected_construct, approx, spec,
				ctxt, next, arg);
    }

    // return an equivalent expr where the head is not an App,
    // and is top-level def-expanded.  This must be overridden in child
    // classes.  Also, doBeta() may be overridden to do beta-reduction.
    public App spineForm(Context ctxt, boolean drop_annos, 
			 boolean spec,
			 boolean expand_defs) {
	Expr h = head;
	if (expand_defs)
	    h = h.defExpandTop(ctxt, drop_annos, spec);
	if (h.construct == construct) {
	    App e = ((App)h).spineForm(ctxt, drop_annos, spec, expand_defs);
	    int eXlen = e.X.length;
	    Expr[] X2 = new Expr[X.length + eXlen];
	    for (int i = 0; i < eXlen; i++)
		X2[i] = e.X[i];
	    for (int i = 0, iend = X.length; i < iend; i++)
		X2[i+eXlen] = X[i];
	    return (App)((new App(construct, e.head, X2))
			 .doBeta(ctxt,drop_annos, spec, expand_defs));
	}
	if (h == head)
	    return (App)doBeta(ctxt,drop_annos,spec,expand_defs);
	return (App)((new App(construct, h, X)).doBeta(ctxt,drop_annos,
						       spec, expand_defs));
    }

    /* do beta-reduction as appropriate, leaving the result in spine form */
    protected Expr doBeta(Context ctxt, boolean drop_annos, boolean spec,
			 boolean expand_defs) {
	return this;
    }

    protected boolean defEqNoAnno(Context ctxt, Expr ee, boolean spec) {
	
	//if (ee.construct == SPEC)
	//    ee = ((Spec) ee).t;

	ee = ee.defExpandTop(ctxt,true,spec);
	
	if (ee.construct != construct) {
	    ctxt.notDefEq(this,ee);
	    return false;
	}
	
	if (ctxt.getFlag("debug_def_eq")) {
	    ctxt.w.println("App testing def. eq. of: ");
	    ctxt.w.print("1. ");
	    print(ctxt.w,ctxt);
	    ctxt.w.println("");
	    ctxt.w.print("2. ");
	    ee.print(ctxt.w,ctxt);
	    ctxt.w.println("");
	}

	App e1 = spineForm(ctxt, true, spec, true);
	App e2 = ((App)ee).spineForm(ctxt, true, spec, true);

	if (ctxt.getFlag("debug_def_eq")) {
	    ctxt.w.println("Spine forms: ");
	    ctxt.w.print("1. ");
	    e1.print(ctxt.w,ctxt);
	    ctxt.w.println("");
	    ctxt.w.print("2. ");
	    e2.print(ctxt.w,ctxt);
	    ctxt.w.println("");
	    ctxt.w.println("------------------------------------------------- {");
	}

	int iend = e1.X.length;
	if (iend != e2.X.length) {
	    ctxt.notDefEq(this,ee);
	    return false;
	}

	for (int i = 0; i < iend; i++){
	    if (!e1.X[i].defEqNoAnno(ctxt, e2.X[i], spec)){
		return false;
	    }
	}
	boolean ret = e1.head.defEqNoAnno(ctxt, e2.head, spec);

	if (ctxt.getFlag("debug_def_eq")) {
	    ctxt.w.println("} " + (new Boolean(ret)).toString());
	    ctxt.w.flush();
	}

	return ret;
    }

    public Expr dropAnnos(Context ctxt) {
	return this; // the proper work is done in TermApp and TypeApp
    }

    public isInstC isInstance(Context ctxt, Expr ee) {
	ee = ee.defExpandTop(ctxt);
	if (ee.construct != construct)
	    return new isInstC();
	App e1 = spineForm(ctxt,false,true,true);
	App e2 = ((App)ee).spineForm(ctxt,false,true,true);
	int iend = e1.X.length;
	if (iend != e2.X.length)
	    return new isInstC();
	isInstC q, found = null;
	for (int i = 0; i < iend; i++) {
	    q = e1.X[i].isInstance(ctxt, e2.X[i]);
	    if (!q.is)
		return q;
	    if (q.val != null)
		found = q;
	}
	
	q = e1.head.isInstance(ctxt, e2.head);
	if (!q.is)
	    return q;
	if (q.val != null)
	    found = q;

	if (found == null)
	    return new isInstC(true);

	return found;
    }

    public void getFreeVarsComputational(Context ctxt,
					 java.util.Collection vars) {
       for (int i = 0; i < X.length; i++)
	   X[i].getFreeVarsComputational(ctxt,vars);
    }

    public java.util.Set getDependences() {
        java.util.Set s = head.getDependences();
        for(int i = 0, n = X.length; i < n; ++i)
            s.addAll(X[i].getDependences());
        return s;
    }
}
