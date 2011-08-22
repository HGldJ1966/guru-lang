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

    public int hashCode_h(Context ctxt) {
	int h = head.hashCode_h(ctxt);
	for (int i = 0, iend = X.length; i < iend; i++)
	    h += X[i].hashCode_h(ctxt);
	return h;
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
	return getHead(ctxt,false,spec,true);
    }

    public Expr getHead(Context ctxt, boolean drop_annos, 
			boolean spec, boolean expand_defs) {
	Expr r = spineForm(ctxt, drop_annos, spec, expand_defs);
	if (r.construct == CONST)
	    return r;
	return ((App)r).head;
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

    /* called by apply_classifier() to check whether or not the expected type
       is def. eq. to the actual type for an argument.  The int arg tells
       which argument this is. */
    protected boolean apply_classifier_types_defeq(Context ctxt, int arg,
						   Expr expected, Expr actual, 
						   int approx, boolean spec) {
	return expected.defEq(ctxt,actual,approx,spec);
    }

    /* called by apply_classifier() to compute the classifier for the
       arg'th argument, arg_e. */
    protected Expr apply_classifier_classify_arg(Context ctxt, int arg, Expr arg_e, 
						 int approx, boolean spec) {
	return arg_e.classify(ctxt,approx,spec);

    }

    // if cl is a Fun-type or Fun-kind, check that the
    // arg's classifier matches the domain classifier,
    // and return the instantiated range classifier.
    protected Expr apply_classifier(int expected_construct, int approx,
				    boolean spec,
				    Context ctxt, Expr cl, int arg) {
	if (arg == X.length) {
	    // we have consumed all the arguments in this App
	    //System.out.println("Done instantiating: "+cl.toString(ctxt));
	    //System.out.flush();

	    return cl;
	}

	cl = cl.defExpandTop(ctxt, false, spec);
	Expr err_tgt = ((X[arg].construct == VAR || X[arg].construct == CONST || X[arg].construct == LEMMA_MARK)
			? this : X[arg]);
	if (cl.construct != expected_construct)
	    err_tgt.handleError
		(ctxt,
		 "A term does not accept enough arguments to apply to"
		 +" argument "+(new Integer(arg+1))+".\n"+
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
			       (new Integer(arg+1)).toString() + ": " +
			       X[arg].toString(ctxt) +
			       " [approx = "+(new Integer(approx)).toString()
			       +", spec = "+(new Boolean(spec)).toString()
			       +" -- but these might be changed for this argument]");
		ctxt.w.flush();
	    }

	    if (X[arg].construct == LEMMA_MARK)
	    {
	    	LemmaMark lm = (LemmaMark)X[arg];
	    	lm.formula = e.types[0];
	    }
	    Expr xc = apply_classifier_classify_arg(ctxt,arg,X[arg], approx, spec);
	    
	    if (ctxt.getFlag("debug_classify_apps")) {
		ctxt.w.println(") Done. About to test def. eq.:"
			       +"\n1. "+e.types[0].toString(ctxt)
			       +"\n2. "+xc.toString(ctxt));
		ctxt.w.flush();
	    }
	    
	    if (!apply_classifier_types_defeq(ctxt, arg, e.types[0], xc, approx, spec))
		err_tgt.handleError
		    (ctxt,
		     "In an application, the classifier of argument "
		     +(new Integer(arg+1))+
		     " is not definitionally equal\nto the expected one:\n"
		     +"1. the argument: "+X[arg].toString(ctxt)+"\n"
		     +"2. argument's classifier: "+xc.toString(ctxt)+"\n"
		     +"3. expected classifier: "+e.types[0].toString(ctxt));
	}
	Expr Xarg = X[arg];
	//System.out.println("Instantiating: "+e.toString(ctxt));
	//System.out.flush();
	Expr next = e.instantiate(Xarg);
	arg++;
	return apply_classifier(expected_construct, approx, spec,
				ctxt, next, arg);
    }

    // return an equivalent expr where the head is not an App,
    // and is top-level def-expanded.  This must be overridden in child
    // classes.  Also, doBeta() may be overridden to do beta-reduction.
    //
    // This will return either an App or a CONST -- assuming type family
    // abbreviations' bodies can only be those.
    public Expr spineForm(Context ctxt, boolean drop_annos, 
			 boolean spec,
			 boolean expand_defs) {
	if (ctxt.getFlag("debug_spine_form")) {
	    ctxt.w.println("spineForm "+toString(ctxt)
			   +"(drop_annos = "+(new Boolean(drop_annos)).toString()
			   +", spec = "+(new Boolean(spec)).toString()
			   +", expand_defs = "+(new Boolean(expand_defs)).toString()
			   +") ( ");
	    ctxt.w.flush();
	}

	Expr h = head;
	if (expand_defs) {
	    h = h.defExpandTop(ctxt, drop_annos, spec);
	    if (ctxt.getFlag("debug_spine_form")) {
		ctxt.w.println("spineForm expanding head to: "+h.toString(ctxt));
		ctxt.w.flush();
	    }
	}
	Expr ret = null;
	if (h.construct == construct) {
	    Expr e = ((App)h).spineForm(ctxt, drop_annos, spec, expand_defs);
	    App a;
	    if (e.construct == CONST) 
		a = new App(construct, (Const)e, X);
	    else {
		a = (App)e;
		int eXlen = a.X.length;
		Expr[] X2 = new Expr[X.length + eXlen];
		for (int i = 0; i < eXlen; i++)
		    X2[i] = a.X[i];
		for (int i = 0, iend = X.length; i < iend; i++)
		    X2[i+eXlen] = X[i];
		a = new App(construct, a.head, X2);
	    }
	    ret = a.doBeta(ctxt,drop_annos, spec, expand_defs);
	}
	else
	    ret = doBeta(ctxt,drop_annos,spec,expand_defs);
	
	if (ctxt.getFlag("debug_spine_form")) {
	    ctxt.w.println(") spineForm = "+ret.toString(ctxt));
	    ctxt.w.flush();
	}
	return ret;
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
	    ctxt.w.println("App testing def. eq. (spec = "+(new Boolean(spec)).toString()+") of: ");
	    ctxt.w.print("1. ");
	    print(ctxt.w,ctxt);
	    ctxt.w.println("");
	    ctxt.w.print("2. ");
	    ee.print(ctxt.w,ctxt);
	    ctxt.w.println("");
	}

	Expr e1 = spineForm(ctxt, true, spec, true);
	Expr e2 = ((App)ee).spineForm(ctxt, true, spec, true);

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

	if (e1.construct == CONST) {
	    if (e2.construct == CONST)
		return e1.defEqNoAnno(ctxt,e2,spec);
	    ctxt.notDefEq(e1,e2);
	    return false;
	}
	
	if (e2.construct == CONST) {
	    ctxt.notDefEq(e1,e2);
	    return false;
	}
    
	App a1 = (App)e1;
	App a2 = (App)e2;

	int iend = a1.X.length;
	if (iend != a2.X.length) {
	    ctxt.notDefEq(this,ee);
	    return false;
	}

	for (int i = 0; i < iend; i++){
	    if (!a1.X[i].defEqNoAnno(ctxt, a2.X[i], spec)){
		return false;
	    }
	}
	boolean ret = a1.head.defEqNoAnno(ctxt, a2.head, spec);

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
	if (ctxt.getFlag("debug_isInstance")) {
	    ctxt.w.println("(isInstance "+toString(ctxt)+" of "+ee.toString(ctxt));
	    ctxt.w.flush();
	}
	ee = ee.defExpandTop(ctxt);
	if (ee.construct != construct) {
	    if (ctxt.getFlag("debug_isInstance")) {
		ctxt.w.println("no)");
		ctxt.w.flush();
	    }
	    return new isInstC();
	}
	Expr e1 = spineForm(ctxt,false,true,true);
	Expr e2 = ((App)ee).spineForm(ctxt,false,true,true);

	if (e1.construct == CONST) {
	    isInstC ret = e1.isInstance(ctxt,e2);
	    if (ctxt.getFlag("debug_isInstance")) {
		ctxt.w.println(")");
		ctxt.w.flush();
	    }
	    return ret;
	}

	if (e2.construct == CONST) {
	    if (ctxt.getFlag("debug_isInstance")) {
		ctxt.w.println("no)");
		ctxt.w.flush();
	    }
	    return new isInstC();
	}

	App a1 = (App)e1;
	App a2 = (App)e2;

	int iend = a1.X.length;
	if (iend != a2.X.length) {
	    if (ctxt.getFlag("debug_isInstance")) {
		ctxt.w.println("no)");
		ctxt.w.flush();
	    }
	    return new isInstC();
	}
	isInstC q, found = null;
	for (int i = 0; i < iend; i++) {
	    q = a1.X[i].isInstance(ctxt, a2.X[i]);
	    if (!q.is) {
		if (ctxt.getFlag("debug_isInstance")) {
		    ctxt.w.println(")");
		    ctxt.w.flush();
		}
		return q;
	    }
	    if (q.val != null)
		found = q;
	}
	
	q = a1.head.isInstance(ctxt, a2.head);
	if (!q.is) {
	    if (ctxt.getFlag("debug_isInstance")) {
		ctxt.w.println("no)");
		ctxt.w.flush();
	    }
	    return q;
	}
	if (q.val != null)
	    found = q;

	if (found == null) {
	    if (ctxt.getFlag("debug_isInstance")) {
		ctxt.w.println("no)");
		ctxt.w.flush();
	    }
	    return new isInstC(true);
	}

	if (ctxt.getFlag("debug_isInstance")) {
	    ctxt.w.println(")");
	    ctxt.w.flush();
	}

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
