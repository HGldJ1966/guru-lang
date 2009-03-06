package guru;

import java.util.*;
import java.io.*;

public class TermApp extends App{
    
    boolean specarg[];

    public TermApp() {
	super(TERM_APP);
    }
    
    public TermApp(Expr head, Expr[] X) {
	super(TERM_APP, head, X);
	specarg = new boolean[X.length];
    }

    public TermApp(Expr head, Expr[] X, boolean specarg[]) {
	super(TERM_APP, head, X);
	this.specarg = specarg;
    }

    public TermApp(Expr head, Expr arg) {
	super(TERM_APP);
	X = new Expr[1];
	X[0] = arg;
	specarg = new boolean[1];
	this.head = head;
    }

    public TermApp(Expr head, Expr arg1, Expr arg2) {
	super(TERM_APP);
	X = new Expr[2];
	X[0] = arg1;
	X[1] = arg2;
	specarg = new boolean[2];
	this.head = head;
    }

    public TermApp(App a, boolean specarg[]) {
	super(TERM_APP, a.head, a.X);
	this.specarg = specarg;
    }

    public void do_print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("(");
	super.do_print(w,ctxt);
	w.print(")");
    }

    protected void print_arg(java.io.PrintStream w, Context ctxt, int i) {
	if (ctxt.getFlag("show_spec_args"))
	    if (specarg[i])
		w.print("spec ");
	super.print_arg(w,ctxt,i);
    }

    public Expr subst(Expr e, Expr x) {
	App s = (App)super.subst(e,x);
	if (s != this)
	    return new TermApp(s, specarg);
	return this;
    }
    
    // n is assumed to be less than X.length-1.
    public TermApp split(int n) {
	Expr[] nX1 = new Expr[n];
	Expr[] nX2 = new Expr[X.length - n];
	boolean []specarg1 = new boolean[n];
	boolean []specarg2 = new boolean[X.length-n];
	int i;
	for (i = 0; i < n; i++) {
	    nX1[i] = X[i];
	    specarg1[i] = specarg[i];
	}
	for (; i < X.length; i++) {
	    nX2[i-n] = X[i];
	    specarg2[i-n] = specarg[i];
	}
	return new TermApp(new TermApp(head, nX1, specarg1), nX2, specarg2);
    }

    public Expr do_rewrite(Context ctxt, Expr e, Expr x, Stack boundVars) {
	App s = (App)super.do_rewrite(ctxt,e,x,boundVars);
	if (s != this)
	    return new TermApp(s, specarg);
	return this;
    }

    // we drop all arguments that are types.  We also drop stars as
    // arguments, for the benefit of Inj. 
    public Expr dropAnnos(Context ctxt) {
	int iend = X.length;
	Expr[] X2 = new Expr[iend];
	boolean changed = false;
	int cnt = 0;

	for (int i = 0; i < iend; i++) {
	    Expr tmp = X[i];

	    	    
	    if (tmp.isTypeOrKind(ctxt)
		|| tmp.isProof(ctxt)
		|| tmp.construct == STAR
		|| specarg[i]) {
		changed = true;
	    }
	    else{
		tmp = tmp.dropAnnos(ctxt);
		X2[cnt] = tmp;
		if (X2[cnt] != X[i]){ 
		    changed = true;
		}
		cnt++;
	    }
	}
	Expr [] X3 = new Expr[cnt];
	System.arraycopy(X2, 0, X3, 0, cnt);

	Expr h = head.dropAnnos(ctxt);

	if (X3.length == 0){
	    return h;
	}

	if (changed || h != head){
	    return new TermApp(h, X3);
	}
	return this;
    }

    public App spineForm(Context ctxt, boolean drop_annos, boolean spec,
			 boolean expand_defs) {
	Expr h = head;
	Expr prev = null;
	if (expand_defs) {
	    Expr prev2 = null;
	    while (h != prev) {
		prev2 = prev;
		prev = h;
		h = h.defExpandOne(ctxt, drop_annos, spec);
	    }
	    if (prev2 != null)
		prev = prev2;

	    if (h.construct != construct && h.construct != CONST &&
		h.construct != VAR)
		/* we are trying to keep these constructs in the head. */
		h = prev;
	}

	if (ctxt.getFlag("debug_spine_form")) {
	    ctxt.w.println("Computing spine form of "+toString(ctxt));
	    ctxt.w.println("{");
	    ctxt.w.println("Head expands to "+h.toString(ctxt));
	    ctxt.w.flush();
	}
	App ret = this;
	if (h.construct == construct) {
	    TermApp e = (TermApp)((TermApp)h).spineForm(ctxt, drop_annos,
							spec, expand_defs);
	    int eXlen = e.X.length;
	    int newlen = X.length + eXlen;
	    Expr[] X2 = new Expr[newlen];
	    boolean[] specarg2 = new boolean[newlen];
	    for (int i = 0; i < eXlen; i++) {
		X2[i] = e.X[i];
		specarg2[i] = e.specarg[i];
	    }
	    for (int i = 0, iend = X.length; i < iend; i++) {
		X2[i+eXlen] = X[i];
		specarg2[i+eXlen] = specarg[i];
	    }
	    ret = new TermApp(e.head, X2, specarg2);
	}
	else if (h != head)
	    ret = new TermApp(h, X, specarg);

	if (ctxt.getFlag("debug_spine_form")) {
	    ret.print(ctxt.w,ctxt);
	    ctxt.w.println("\n}");
	    ctxt.w.flush();
	}
	return ret;
    }

    public Expr classify(Context ctxt, int approx, boolean spec) {
	if (ctxt.getFlag("debug_classify_term_apps")) {
	    ctxt.w.print("(Classifying ");
	    print(ctxt.w,ctxt);
	    ctxt.w.println("");
	    ctxt.w.flush();
	}
	Expr cl = head.classify(ctxt,approx,spec).defExpandTop(ctxt,false,
							       spec);
	Expr ret = apply_classifier(FUN_TYPE, approx, spec, ctxt, cl, 0);
	FunType ch = (FunType)((FunType)cl).coalesce(ctxt,spec);
	boolean check_spec_terminates = ctxt.getFlag("check_spec_terminates");
	for (int i = 0;i < X.length; i++) {
	    if (ch.owned[i].status == Ownership.SPEC) {
		if (check_spec_terminates)
		    X[i].checkTermination(ctxt);
		specarg[i] = true;
	    }
	}
	if (ctxt.getFlag("debug_classify_term_apps")) {
	    ctxt.w.println(") Classifier is:");
	    ret.print(ctxt.w,ctxt);
	    ctxt.w.println("");
	    ctxt.w.flush();
	}

	return ret;
    }

    public Expr evalStep(Context ctxt) {
	Expr h = head.evalStep(ctxt);
	if (h != head)
	    return new TermApp(h, X);
	if (h.construct == ABORT)
	    return ctxt.abort;
	
	int iend = X.length;
	Expr[] X2 = new Expr[iend];
	for (int i = 0; i < iend; i++) {
	    X2[i] = X[i].evalStep(ctxt);
	    if (X2[i] != X[i]) {
		for (int j = i+1; j < iend; j++)
		    X2[j] = X[j];
		return new TermApp(h, X2);
	    }
	    else {
		if (X[i].construct == ABORT)
		    return ctxt.abort;
	    }
	}
	
	// none of the args evaluated to something different
	if (h.construct == FUN_TERM) {
	    FunTerm f = (FunTerm)h;
	    iend = X2.length;

	    /*
	    System.out.println("\n=======\ninstantiating ");
	    f.do_print(System.out, ctxt);
	    System.out.println("\n with ");
	    X2[0].do_print(System.out,ctxt);
	    System.out.println("=======\n");
	    */

	    Expr hh = f.instantiate(X2[0]);
	    if (iend == 1)
		return hh;
	    iend--;
	    Expr[] X3 = new Expr[iend];
	    for (int i = 0; i < iend; i++)
		X3[i] = X2[i+1];
	    return new TermApp(hh, X3);
	}
	return this;
    }

    public boolean subtermDefEqNoAnno(Context ctxt, Expr e) {
	// This check is captured below, all arguments always evaluated for a terminating term
	//
	// If it's a TermApp of a constructor, we need to look at all the sub expressions
	//if (head.construct == CONST && ctxt.isTermCtor((Const)head)) {
	//    for (int i = 0; i < X.length; i++)
	//	//if (X[i].defEqNoAnno(ctxt, e))
	//	if (X[i].subtermDefEqNoAnno(ctxt, e))
	//	    return true;
	//    return false;
	//} else {

	// Same as the head?
	// Same as the whole application? ("this")
	if (head.subtermDefEqNoAnno(ctxt, e)
	    || super.subtermDefEqNoAnno(ctxt, e))
	    return true;
	// In our CBV instantiated function evaluation scheme, all arguments are evaluated, so check equality
	for (int i = 0; i < X.length; i++)
	    if (X[i].subtermDefEqNoAnno(ctxt, e))
		return true;
	// Same as any of the spline form TermApp "heads"?
	for (int i = 0; i < X.length; i++) {
	    Expr[] newX = new Expr[i+1];
	    for (int j = 0; j <= i; j++) {
		newX[j] = X[j];
	    }
	    if (e.defEqNoAnno(ctxt, new TermApp(head, newX), true))
		return true;
	}
	return false;

	//}
    }

    public Expr dropNoncompArgs(Context ctxt) {
	if (ctxt.getFlag("debug_drop_noncomp")) {
	    ctxt.w.println("Dropping non-comp arguments from term-app "+
			   toString(ctxt));
	    ctxt.w.flush();
	}
	ArrayList nX = new ArrayList();
	ArrayList no = new ArrayList();
	boolean changed = false;
	Boolean b = new Boolean(false);
	for (int i = 0, iend = X.length; i < iend; i++) {
	    if (X[i].isProof(ctxt) || specarg[i]) 
		changed = true;
	    else {
		nX.add(X[i]);
		no.add(b);
	    }
	}

	Expr ret = this;
	if (changed) {
	    if (nX.size() == 0)
		ret = head;
	    else
		ret = new TermApp(head, Parser.toExprArray(nX),
				  Parser.toBooleanArray(no));
	}
	
	if (ctxt.getFlag("debug_drop_noncomp")) {
	    ctxt.w.println("Returning "+
			   ret.toString(ctxt));
	    ctxt.w.flush();
	}

	return ret;
    }

    public void checkTermination(Context ctxt) {
	Expr no_annos = dropAnnos(ctxt).defExpandTop(ctxt);
	if (no_annos.construct == FUN_TERM || no_annos.construct == CONST)
	    return;
	if (no_annos.construct != TERM_APP)
	    handleError(ctxt,"We are checking termination of a term application where"
			+" dropping\nannotations gives an unexpected form of expression."
			+"1. the term application: "+toString(ctxt)
			+"\n2. with annotations dropped: "+no_annos.toString(ctxt));
	TermApp t = (TermApp)((TermApp)no_annos).spineForm(ctxt,true,true,true);

	TermApp anno_t = (TermApp)spineForm(ctxt,false,true,true);
	if(ctxt.getFlag("debug_terminates")) {
	    ctxt.w.println("termTerminates checking TermApp.\n"
			   +"\n1. original term, no annos: "+no_annos.toString(ctxt)
			   +"\n2. spine form, no annos: "+t.toString(ctxt)
			   +"\n3. spine form, with annos: "+anno_t.toString(ctxt)
			   +"\n4. head:"
			   +anno_t.head.toString(ctxt)+
			   "\n5. inj:"
			   +anno_t.isI(ctxt)
			   +"\n5. head is ctor:"
			   +(anno_t.head.construct == CONST ? 
			     (new Boolean(ctxt.isTermCtor((Const)anno_t.head))).toString() : "false"));
	    ctxt.w.flush();
	}


	if(t.head.construct != CONST)
	    handleError(ctxt,"Checking termination, the head of an application is "
			+"not a constant.\n"
			+"1. the application in spine form: "+t.toString(ctxt)
			+"\n2. the head: "+t.head.toString(ctxt));
	
	Const c = (Const)t.head;
	boolean is_total = ctxt.isTotal(c);
	if (!is_total && !ctxt.isTermCtor(c))
	    handleError(ctxt,"Checking termination, the head of an application is "
			+"neither\ndeclared total nor a term constructor.\n"
			+"1. the application in spine form: "+t.toString(ctxt)
			+"\n2. the head: "+c.toString(ctxt));

	if (is_total) {
	    /* a little more work is needed here to check that if
	       totality were proved when some arguments are certain
	       fixed other terms, we have those arguments here. */
	    Collection thms = ctxt.getTotalityTheorems(c);
	    Iterator it = thms.iterator();

	    boolean problem = true;
	    while(it.hasNext()) {
		Forall F = (Forall)it.next();
		TermApp lhs = (TermApp)((Atom)((Exists)F.body).body).Y1;
		
		problem = false;
		for (int j = 0, jend = lhs.X.length; j < jend; j++)
		    if (lhs.X[j].construct != VAR)
			if (!lhs.X[j].defEq(ctxt,t.X[j])) {
			    problem = true;
			    break; // out of for loop
			}
		if (!problem)
		    // we have found a matching totality theorem.
		    break; // out of while loop
	    }

	    if (problem) {
		String s = ("Termination checking cannot find a registered totality theorem"
			    +" for the\ngiven application.  The number of theorems registered"
			    +" for the head is "+(new Integer(thms.size())).toString()+".\n"
			    +"1. the term to termination check: "+t.toString());
		if (thms.size() > 0) {
		    s = s+"2. the totality theorems registered for the head:\n";
		    it = thms.iterator();
		    while(it.hasNext()) {
			Forall F = (Forall)it.next();
			s = s + "-- "+F.toString(ctxt);
		    }
		}
		handleError(ctxt, s);
	    }
	}

	/* we cannot look at just t next, because terminates casts
	   will have been dropped computing it. */
	for (int i = 0, iend = t.X.length; i < iend; i++)
	    anno_t.X[i].checkTermination(ctxt);
    }

    public void checkSpec(Context ctxt, boolean in_type){
	head.checkSpec(ctxt, in_type);
	
	// we set specarg[i] in classify() above

	for (int i = 0;i < X.length; i++) {
	    if (X[i].isProof(ctxt))
		continue;
	    if (!specarg[i])
		X[i].checkSpec(ctxt, in_type);
	}
    }

    public void getFreeVarsComputational(Context ctxt,
					 java.util.Collection vars) {
	for (int i = 0; i < X.length; i++) 
	    if (specarg[i] || X[i].isProof(ctxt) || X[i].isTypeOrKind(ctxt))
		continue;
	    else
		X[i].getFreeVarsComputational(ctxt,vars);
    }

}
