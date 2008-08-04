package guru;

public class Induction extends Expr{
    public Case[] C;
    public VarListExpr vl;
    public Var x1;
    public Var x2;
    public Var x3;
    public Expr F;
    
    public Induction() {
	super(INDUCTION);
    }

    public Induction(VarListExpr vl, Var x1, Var x2, Var x3, Expr F, 
		     Case[] C) {
	super(INDUCTION);
	this.C = C;
	this.vl = vl;
	this.x1 = x1;
	this.x2 = x2;
	this.x3 = x3;
	this.F = F;
    }

    public void do_print(java.io.PrintStream w, 
			 Context ctxt) {
	w.print("induction ");
	vl.print(w,ctxt);
	w.print(" by ");
	x1.print(w,ctxt);
	w.print(" ");
	x2.print(w,ctxt);
	w.print(" ");
	x3.print(w,ctxt);
	w.print(" return ");
	F.print(w,ctxt);
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
	int n = vl.numOcc(e);
	n += x1.numOcc(e);
	n += x2.numOcc(e);
	n += x3.numOcc(e);
	n += F.numOcc(e);
	for (int i = 0, iend = C.length; i < iend; i++)
	    n += C[i].numOcc(e);
	return n;
    }

    public Expr subst(Expr e, Expr x) {
	VarListExpr nvl = (VarListExpr)vl.subst(e,x);
	Expr nF = F.subst(e,x);
	int iend = C.length;
	Case[] sC = new Case[iend];
	boolean changed = false;
	for (int i = 0; i < iend; i++) {
	    sC[i] = (Case)C[i].subst(e,x);
	    if (sC[i] != C[i])
		changed = true;
	}
	if (nvl != vl || nF != F || changed)
	    return new Induction(nvl, x1, x2, x3, nF, sC);
	return this;
    }

    public Expr dropAnnos(Context ctxt) {
	return new Bang();
    }

    public Expr classify(Context ctxt) {
	vl.checkClassifiers(ctxt,0,true);
	int last = vl.types.length - 1;
	Expr last_var = vl.vars[last];
	Expr last_type = vl.types[last];
	if (!last_type.isdtype(ctxt,true /* spec */))
	    handleError(ctxt,
			"The last type in the quantified part of an "
			+"induction-proof is not\n"
			+"an inductive type.\n"
			+"The type: "+last_type.toString(ctxt));
	Expr cF = F.classify(ctxt);
	if (cF.construct != FORMULA)
	    handleError(ctxt,
			"The return type of an induction-proof is not a "
			+"formula.\n"
			+"1. the return type:"+F.toString(ctxt)+"\n"
			+"2. its classifier:"+cF.toString(ctxt));

	Expr IH = new Forall(vl.vars, vl.types, F);
	ctxt.setClassifier(x3, IH);

	for (int i = 0, iend = C.length; i < iend; i++) {
	    // get this first, to set the types of pattern variables.
	    // dropAnnos() needs these to be set.

	    C[i].setPatternVarTypes(ctxt, false);
	    
	    C[i].markSpec(ctxt); // AS: I'm not sure why this is needed

	    Expr pat = C[i].getPattern();
	    Expr pattp = pat.classify(ctxt);

	    Expr assump1 = new Atom(true, last_var, pat.dropAnnos(ctxt));

	    ctxt.setClassifier(x1, assump1);

	    // note that the call to getPatternType sets the classifiers
	    // of the pattern variables.
	    Expr assump2 = new Atom(true, last_type.dropAnnos(ctxt),
				    pattp.dropAnnos(ctxt));
	    ctxt.setClassifier(x2, assump2);

	    /*System.out.println("\n---- assumptions ");
	    assump1.do_print(System.out,ctxt);
	    System.out.println("\n");
	    assump2.do_print(System.out,ctxt);
	    */

	    Expr form = C[i].body.classify(ctxt);
	    if (!F.defEq(ctxt, form))
		C[i].handleError
		    (ctxt,
		     "The classifier computed for the body of a case in"
		     +" an induction-proof\nis different from"
		     +" the expected one.\n"
		     +"1. computed classifier: "
		     +form.toString(ctxt)+"\n"
		     +"2. expected classifier: "+F.toString(ctxt)+"\n"
		     +"3. the case: "+C[i].getPattern().toString(ctxt));

	    /* check termination after computing the type, because
	       computing the type will add declarations for any variables
	       bound in the body to the context.  Those declarations
	       are used during termination checking, because we drop
	       annotations when termination checking, which requires
	       type information for variables. */
	    C[i].body.checkTermination(ctxt, x3, last, C[i].x);
	}
			       
	return IH;
    }

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars) {
	for (int i = 0, iend = C.length; i < iend; i++) 
	    C[i].body.checkTermination(ctxt, IH, arg, vars);
    }

    public java.util.Set getDependences() {
        java.util.Set s = getDependences();
        s.addAll(vl.getDependences());
        s.addAll(F.getDependences());
        for(int i = 0, n = C.length; i < n; ++i)
            s.addAll(C[i].getDependences());
        return s;
    }

}
