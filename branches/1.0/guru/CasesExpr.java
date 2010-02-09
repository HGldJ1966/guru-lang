package guru;

import java.util.*;

public class CasesExpr extends Expr {
    public Case[] C;
    public Expr t;
    public Var x1;
    public Var x2;
    
    public CasesExpr(int construct) {
	super(construct);
    }

    public CasesExpr(int construct, CasesExpr a) {
	super(construct);
	this.C = a.C;
	this.t = a.t;
	this.x1 = a.x1;
	this.x2 = a.x2;
    }

    public CasesExpr(int construct, Expr t, Var x1, Var x2, 
		     Case[] C) {
	super(construct);
	this.C = C;
	this.t = t;
	this.x1 = x1;
	this.x2 = x2;
    }

    public void do_print(java.io.PrintStream w, 
			 Context ctxt) {
	do_print1(w,ctxt);
	do_print2(w,ctxt);
    }

    protected void do_print1(java.io.PrintStream w, 
			     Context ctxt) {
	t.print(w,ctxt);
	if (x1 != null) {
	    w.print(" by ");
	    x1.print(w,ctxt);
	    w.print(" ");
	    x2.print(w,ctxt);
	}
    }

    protected void do_print2(java.io.PrintStream w, 
			     Context ctxt) {
	w.print(" with ");
	boolean first = true;
	for (int i = 0, iend = C.length; i < iend; i++) {
	    if (first)
		first = false;
	    else
		w.print(" | ");
	    C[i].print(w,ctxt);
	}
	w.print(" end");
    }

    public int numOcc(Expr e) {
	int n = t.numOcc(e);
	if (x1 != null) {
	    n += x1.numOcc(e);
	    n += x2.numOcc(e);
	}
	for (int i = 0, iend = C.length; i < iend; i++)
	    n += C[i].numOcc(e);
	return n;
    }

    public boolean defEqNoAnno(Context ctxt, Expr ee, boolean spec) {
	ee = ee.defExpandTop(ctxt);

	if (ee.construct != construct) {
	    ctxt.notDefEq(this,ee);
	    return false;
	}
	CasesExpr e = (CasesExpr)ee;
	if (!t.defEqNoAnno(ctxt,e.t,spec))
	    return false;
	int iend = C.length;
	if (iend != e.C.length) {
	    ctxt.notDefEq(this,ee);
	    return false;
	}
	for (int i = 0; i < iend; i++)
	    if (!C[i].defEqNoAnno(ctxt,e.C[i],spec))
		return false;
	return true;
    }

    public Expr subst(Expr e, Expr x) {
	int iend = C.length;
	Expr nt = t.subst(e,x);
	Case[] sC = new Case[iend];
	boolean changed = false;
	for (int i = 0; i < iend; i++) {
	    sC[i] = (Case)C[i].subst(e,x);
	    if (sC[i] != C[i])
		changed = true;
	}
	if (changed || nt != t)
	    return new CasesExpr(construct,nt,x1,x2,sC);
	return this;
    }
    
    public Expr do_rewrite(Context ctxt, Expr e, Expr x, Stack boundVars) {
		
    int iend = C.length;
	Case[] sC = new Case[iend];
	boolean changed = false;
	for (int i = 0; i < iend; i++) {
	    sC[i] = (Case)C[i].rewrite(ctxt,e,x,boundVars);
	    if (sC[i] != C[i])
		changed = true;
	}
	Expr nt = t.rewrite(ctxt,e,x, boundVars);
	if (changed || nt != t)
	    return new CasesExpr(construct,nt,x1,x2,sC);
	return this;
    }

    public Expr dropAnnos(Context ctxt) {
	int iend = C.length;
	Expr nt = t.dropAnnos(ctxt);
	Case[] sC = new Case[iend];
	boolean changed = false;
	for (int i = 0; i < iend; i++) {
	    sC[i] = (Case)C[i].dropAnnos(ctxt);
	    if (sC[i] != C[i])
		changed = true;
	}
	if (changed || nt != t)
	    return new CasesExpr(construct,nt,x1,x2,sC);
	return this;
    }

    public Expr classify(Context ctxt, int approx, boolean spec) {
	Expr clt = t.classify(ctxt,approx,spec).defExpandTop(ctxt,false,spec);
	Const head = clt.typeGetHead(ctxt,spec);
	if (approx != APPROX_TRIVIAL && head == null)
	    handleError(ctxt,
			"The scrutinee's type in a match-term is not"
			+" an inductive type (or is opaque).\n"
			+"1. the type: "+clt.toString(ctxt));
	Expr t1 = t.dropAnnos(ctxt);
	Expr clt1 = clt.dropAnnos(ctxt);
	Expr retT = null;
	int i, iend;
	if (ctxt.getFlag("debug_refine_cases")) {
	    ctxt.w.println("\nChecking match with scrutinee "
			   +t.toString(ctxt));
	    ctxt.w.flush();
	}

	Const head2 = null;

	for (i = 0, iend = C.length; i < iend; i++) {

	    if (head2 == null) {
		head2 = ctxt.getTypeCtor(C[i].c);
		if (!head2.defEq(ctxt,head,approx,spec)) 
		    handleError(ctxt,
				"The head of the type of the scrutinee does not match the head of the type of the cases.\n\n"
				+"1. the head of the type of the scrutinee: "+head.toString(ctxt)
				+"\n\n2. the head of the type of the first case: "+head2.toString(ctxt));
	    }

	    Expr pat = C[i].getPattern();
	    if (!C[i].allVarsPresent(ctxt))
		C[i].handleError(ctxt,
				 "There are too few or too many variables in a"
				 +" pattern.\n1. the pattern: "
				 +pat.toString(ctxt)
				 +"\n2. the constructor's type: "
				 +ctxt.getClassifier(C[i].c).toString(ctxt));

	    // get this first, so that the types of the pattern variables
	    // get set in the context.  dropAnnos() needs the types of
	    // variables to be set.
	    C[i].setPatternVarTypes(ctxt, false);
	    C[i].setSpecOwnership(ctxt);
	    Expr pattp = pat.classify(ctxt,approx,spec);

	    /* set these types before refining, so that they are
	       nominally still using the pattern variables (for
	       benefit of things like checking for no free
	       computational variables after eta-expansion, which will
	       use the names of variables). */
	    if (x1 != null) {
		Expr assump1 = new Atom(true, t1, pat.dropAnnos(ctxt));
		ctxt.setClassifier(x1, assump1);

		// note that the call to getPatternType sets the classifiers
		// of the pattern variables.
		Expr assump2 = new Atom(true, clt1, pattp.dropAnnos(ctxt));
		ctxt.setClassifier(x2, assump2);
	    }

	    if (!C[i].refine(ctxt, clt1, approx, spec)) {
		if (ctxt.getFlag("debug_refine_cases")) {
		    ctxt.w.println("Impossible case in match (so not checking body): "+pat.toString(ctxt));
		    ctxt.w.flush();
		}
		C[i].clearDefs(ctxt);
		continue;
	    }

	    Expr tp = C[i].body.classify(ctxt,approx,spec);

	    C[i].impossible = C[i].impossible || (C[i].body.construct == IMPOSSIBLE);

	    if (retT == null) {
		int freevars = 0;
		for (int j = 0, jend = C[i].x.length; j < jend; j++) {
		    freevars += tp.numOcc(C[i].x[j]);
		}
		if (freevars > 0) 
		    C[i].handleError(ctxt,"The classifier computed for the "
				     +"body of a case contains pattern "
				     +"variables from that case."
				     +"\n1. the case: "+pat.toString(ctxt)
				     +"\n2. its body's classifier: "
				     +tp.toString(ctxt));
		retT = tp;
	    }
	    else if (!retT.defEq(ctxt, tp, approx, spec))
		C[i].handleError(ctxt,
			    "The classifier computed for the body of a case"
			    +" is different\n"
			    +"from the expected one.\n"
                            +"1. The case: "+pat.toString(ctxt)
			    +"\n"
			    +"2. computed: "+tp.toString(ctxt)+"\n"
			    +"3. expected: "+retT.toString(ctxt));

	    C[i].clearDefs(ctxt);
	}
		
	if (retT == null) {
	    if (iend > 0)
		handleError(ctxt, "Could not compute the "
			    +"return type for a match, since no cases\n"
			    +"were checked.  Check that the pattern's term constructors are from\nthe same type as the scrutinee.");
	    handleError(ctxt, "No return type is stated for a match term,"
			+ " but the match has no cases, so no return type\n"
			+ "could be computed.\n");
	}
	return retT;
    }

    public void checkTermination(Context ctxt) {
        for (int i = 0, iend = C.length; i < iend; i++)
            C[i].checkTermination(ctxt);
	t.checkTermination(ctxt);
    }

    public void getFreeVarsComputational(Context ctxt, Collection vars){
	for (int i =0; i< C.length; i++) 
	    C[i].getFreeVarsComputational(ctxt, vars);
	t.getFreeVarsComputational(ctxt,vars);
    }

    public java.util.Set getDependences() {
        java.util.Set s = new TreeSet();
        for(int i = 0, n = C.length; i < n; ++i)
            s.addAll(C[i].getDependences());
	s.addAll(t.getDependences());
        return s;
    }
}
