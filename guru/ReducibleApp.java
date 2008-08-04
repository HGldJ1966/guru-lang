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
    
    public App spineForm(Context ctxt, boolean drop_annos, boolean spec,
			 boolean expand_defs) {
	App s = (App)super.spineForm(ctxt, drop_annos, spec, expand_defs);
	if (s != this)
	    return new ReducibleApp(construct,s);
	return this;
    }

    protected boolean headBetaOk(Context ctxt, boolean spec) {
	return false;
    }

    protected Expr doBeta(Context ctxt, boolean drop_annos, boolean spec,
			  boolean expand_defs) {
	if (head.construct != CONST)
	    return this;
	
	Const c = (Const)head;

	if (!headBetaOk(ctxt,spec))
	    return this;

	Expr nhead = ctxt.getDefBody(c);
	FunTerm f = (FunTerm)nhead;

	if (f.vars.length > X.length)
	    // we do not beta-reduce until we have all arguments
	    return this;

	int i = 0;
	while (nhead.construct == FUN_TERM) {
	    f = (FunTerm)nhead;
	    nhead = f.instantiate(X[i++]);
	}

	int iend = X.length, start = i;

	if (start == iend)
	    return nhead;
	Expr[] nX = new Expr[iend - start];
	for (; i < iend; i++)
	    nX[i-start] = X[i];

	return ((new ReducibleApp(construct, nhead,nX))
		.spineForm(ctxt, drop_annos, spec, expand_defs));
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

	ee = ee.defExpandTop(ctxt,true,spec);
	
	if (ee.construct != construct) {
	    ctxt.notDefEq(this,ee);
	    return false;
	}
	
	App e1 = spineForm(ctxt, true, spec, true);
	App e2 = ((App)ee).spineForm(ctxt, true, spec, true);

	if (ctxt.getFlag("debug_type_app_def_eq")) {
	    ctxt.w.println("Spine forms:"
			   +"\n1. "+e1.toString(ctxt)
			   +"\n2. "+e2.toString(ctxt));
	    ctxt.w.flush();
	}

	int iend = e1.X.length;

	if (approx)
	    return e1.head.defEqNoAnnoApprox(ctxt, e2.head, spec);

	if (iend != e2.X.length) {
	    ctxt.notDefEq(this,ee);
	    return false;
	}

	for (int i = 0; i < iend; i++) {
	    if (!e1.X[i].defEqNoAnno(ctxt, e2.X[i], spec)){
		return false;
	    }
	}
	return e1.head.defEqNoAnno(ctxt, e2.head, spec);
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

    public void checkSpec(Context ctxt, boolean in_type){
	head.checkSpec(ctxt, in_type);
	for (int i = 0; i < X.length; i++)
	    X[i].checkSpec(ctxt, true /* here we finally cross from
					 types or formulas possibly to
					 terms */);
    }

    /* a type application is compiled to the head of its spine form,
       which cannot be a variable in our type system.  So it has no
       free vars. */
    public void getFreeVarsComputational(Context ctxt,
					 java.util.Collection vars) { }

}
