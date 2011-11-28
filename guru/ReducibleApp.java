package guru;

import java.util.Stack;

public class ReducibleApp extends App{
    
    public ReducibleApp(int construct) {
	super(construct);
    }
    
    public ReducibleApp(int construct, App a) {
	super(construct, a.head, a.X);
    }

    public ReducibleApp(int construct, Expr head, Expr[] X) {
	super(construct, head, X);
    }

    public Expr getHeadKind(Context ctxt) {
	return null;
    }

    public Expr classify(Context ctxt, int approx, boolean spec) {
	Expr cl = head.classify(ctxt,approx,spec);
	cl.pos = pos;
	Expr clc = cl.classify(ctxt,approx,spec);
	Expr hc = getHeadKind(ctxt);
	if (clc.construct != hc.construct)
	    handleError(ctxt,"An application's head does not have the"
			+" expected kind of classifier.\n"
			+"1. the head: "+head.toString(ctxt)
			+"\n2. its classifier: "+cl.toString(ctxt)
			+"\n3. its classifier's kind: "+clc.toString(ctxt)
			+"\n4. the expected kind: "+hc.toString(ctxt));
	return apply_classifier(FUN_TYPE, approx, spec, ctxt, cl, 0);
    }

    public Expr subst(Expr e, Expr x) {
	App s = (App)super.subst(e,x);
	if (s != this)
	    return new ReducibleApp(construct,s);
	return this;
    }
    
    public Expr spineForm(Context ctxt, boolean drop_annos, boolean spec,
			 boolean expand_defs) {
	Expr s = super.spineForm(ctxt, drop_annos, spec, expand_defs);
	if (s == this)
	    return this;
	if (s.construct == CONST)
	    return s;
	return new ReducibleApp(construct,(App)s);
    }

    protected boolean headBetaOk(Context ctxt, boolean spec) {
	return false;
    }

    protected Expr doBeta(Context ctxt, boolean drop_annos, boolean spec,
			  boolean expand_defs) {
	if (ctxt.getFlag("debug_spine_form")) {
	    ctxt.w.println("doBeta "+toString(ctxt)
			   +"(drop_annos = "+(new Boolean(drop_annos)).toString()
			   +", spec = "+(new Boolean(spec)).toString()
			   +", expand_defs = "+(new Boolean(expand_defs)).toString()
			   +") ( ");
	    ctxt.w.flush();
	}

	if (head.construct != CONST) {
	    if (ctxt.getFlag("debug_spine_form")) {
		ctxt.w.println(") doBeta1 = "+toString(ctxt));
		ctxt.w.flush();
	    }
	    return this;
	}
	Const c = (Const)head;

	if (!headBetaOk(ctxt,spec)) {
	    if (ctxt.getFlag("debug_spine_form")) {
		ctxt.w.println(") doBeta2 = "+toString(ctxt));
		ctxt.w.flush();
	    }
	    return this;
	}

	Expr nhead = drop_annos ? ctxt.getDefBodyNoAnnos(c) : ctxt.getDefBody(c);
	if (nhead.construct != FUN_TERM)
	    return nhead;

	FunTerm f = (FunTerm)nhead;

	if (f.vars.length > X.length) {
	    // we do not beta-reduce until we have all arguments
	    if (ctxt.getFlag("debug_spine_form")) {
		ctxt.w.println(") doBeta3 = "+toString(ctxt));
		ctxt.w.flush();
	    }
	    return this;
	}

	int i = 0;
	while (nhead.construct == FUN_TERM) {
	    f = (FunTerm)nhead;
	    nhead = f.instantiate(X[i++]);
	}

	int iend = X.length, start = i;

	if (start == iend) {
	    if (nhead.construct == construct) {
		// should put in spine form in case there are further
		// beta reductions to do.
		if (ctxt.getFlag("debug_spine_form")) {
		    ctxt.w.println(") doBeta4 = "+nhead.toString(ctxt));
		    ctxt.w.flush();
		}
		return ((App)nhead).spineForm(ctxt,drop_annos,spec,expand_defs);
	    }
	    if (ctxt.getFlag("debug_spine_form")) {
		ctxt.w.println(") doBeta5 = "+nhead.toString(ctxt));
		ctxt.w.flush();
	    }
	    return nhead;
	}
	Expr[] nX = new Expr[iend - start];
	for (; i < iend; i++)
	    nX[i-start] = X[i];

	Expr ret = ((new ReducibleApp(construct, nhead,nX))
		    .spineForm(ctxt, drop_annos, spec, expand_defs));
	if (ctxt.getFlag("debug_spine_form")) {
	    ctxt.w.println(") doBeta6 = "+ret.toString(ctxt));
	    ctxt.w.flush();
	}
	return ret;
    }

    protected boolean defEqNoAnnoApprox(Context ctxt, Expr ee, boolean spec) {
	return defEqInternal(ctxt,ee,spec,true);
    }

    protected boolean defEqNoAnno(Context ctxt, Expr ee, boolean spec) {
	return defEqInternal(ctxt,ee,spec,false);
    }

    protected boolean defEqInternal(Context ctxt, Expr ee, boolean spec,
				    boolean approx) {
	if (ctxt.getFlag("debug_type_app_def_eq")) {
	    ctxt.w.println("Checking these exprs for definitional equality:"
			   +"\n1. "+toString(ctxt)
			   +"\n2. "+ee.toString(ctxt));
	    ctxt.w.flush();
	}

	Expr e1 = spineForm(ctxt, true, spec, true);

	if (e1 != this) {
	    if (approx)
		return e1.defEqNoAnnoApprox(ctxt,ee,spec);
	    return e1.defEqNoAnno(ctxt,ee,spec);
	}

	ee = ee.defExpandTop(ctxt,true,spec);
	
	if (ee.construct != construct) {
	    ctxt.notDefEq(this,ee);
	    return false;
	}
	
	Expr e2 = ((App)ee).spineForm(ctxt, true, spec, true);

	if (ctxt.getFlag("debug_type_app_def_eq")) {
	    ctxt.w.println("Spine forms:"
			   +"\n1. "+e1.toString(ctxt)
			   +"\n2. "+e2.toString(ctxt));
	    ctxt.w.flush();
	}

	if (e2.construct == CONST) {
	    ctxt.notDefEq(e1,e2);
	    return false;
	}
    
	App a1 = (App)e1;
	App a2 = (App)e2;

	int iend = a1.X.length;

	if (approx)
	    return a1.head.defEqNoAnnoApprox(ctxt, a2.head, spec);

	if (iend != a2.X.length) {
	    ctxt.notDefEq(this,ee);
	    return false;
	}

	for (int i = 0; i < iend; i++) {
	    if (!a1.X[i].defEqNoAnno(ctxt, a2.X[i], spec)){
		return false;
	    }
	}
	return a1.head.defEqNoAnno(ctxt, a2.head, spec);
    }

    public Expr do_rewrite(Context ctxt, Expr e, Expr x, Stack boundVars)
    {
    	return this;
    }

    public Expr dropAnnos(Context ctxt) {
	int iend = X.length;
	Expr[] X2 = new Expr[iend];
	boolean changed = false;
	for (int i = 0; i < iend; i++) {
  
	    X2[i] = X[i].dropAnnos(ctxt);
	    if (X2[i] != X[i])
		changed = true;
	}
	Expr nhead = head.dropAnnos(ctxt);

	if (nhead != head || changed)
	    return new ReducibleApp(construct, nhead, X2);
	return this;
    }

    public void checkSpec(Context ctxt, boolean in_type, Position p){
	head.checkSpec(ctxt, in_type, pos);
	for (int i = 0; i < X.length; i++)
	    X[i].checkSpec(ctxt, true /* here we cross to types or formulas */,
			   pos);
    }

    /* a type application is compiled to the head of its spine form,
       which cannot be a variable in our type system.  So it has no
       free vars. */
    public void getFreeVarsComputational(Context ctxt,
					 java.util.Collection vars) { }

}
