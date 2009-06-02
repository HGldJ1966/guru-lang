package guru;

public class Cast extends Expr{
    
    public Expr t, P, T;
    
    public Cast() {
	super(CAST);
    }
    
    public Cast(Expr t, Expr P) {
	super(CAST);
	this.t = t;
	this.P = P;
	this.T = null;
    }

    public Cast(Expr t, Expr P, Expr T) {
	super(CAST);
	this.t = t;
	this.P = P;
	this.T = T;
    }

    public void do_print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("cast ");
	if (ctxt.getFlag("show_some_computed_types")) {
	    w.print("%- ");
	    if (T == null)
		w.print(" <no computed type>");
	    else
		T.print(w,ctxt);
	    w.print(" -% ");
	}
	t.print(w,ctxt);
	w.print(" by ");
	P.print(w,ctxt);
    }

    public int numOcc(Expr e) {
	return t.numOcc(e) + P.numOcc(e) + (T != null ? T.numOcc(e) : 0);
    }

    public Expr subst(Expr e, Expr x) {
	Expr nt = t.subst(e,x), nP = P.subst(e,x);
	Expr nT = (T != null ? T.subst(e,x) : null);
	if (nt != t || nP != P || nT != T)
	    return new Cast(nt, nP, nT);
	return this;
    }

    /* during regular type checking, we will store the type of the cast
       term.  Then during any subsequent approximate type checking, we
       will just return that type, and ignore the proof. */
    public Expr classify(Context ctxt, int approx, boolean spec) {
	if (ctxt.getFlag("debug_classify_casts")) {
	    ctxt.w.print("Classifying ");
	    print(ctxt.w,ctxt);
	    ctxt.w.println("");
	    ctxt.w.flush();
	}

	Expr ct = t.classify(ctxt, approx, spec);
	if (approx > 0) {
	    if (T == null)
		handleError(ctxt,
			    "Approximate type checking called on a cast-term"
			    +" which has not\nbeen type checked yet.");
	    if (ctxt.getFlag("debug_classify_casts")) {
		ctxt.w.println("Returning stored type "+T.toString(ctxt));
		ctxt.w.flush();
	    }
	    return T;
	}

	Expr fla = P.classify(ctxt);
	if (fla.construct == ATOM) {
	    Atom q = (Atom)fla;
	    if (q.equality) {
		if (!ct.defEq(ctxt, q.Y1, approx, spec))
		    handleError(ctxt,
				"The type T of a term which is being cast"
				+" does not match the LHS of the\n"
				+"casting equation.\n"
				+"1. The type T: "+ct.toString(ctxt)
				+"\n"
				+"2. The casting equation: "
				+q.toString(ctxt));
		return (T = q.Y2);
	    }
	}

	handleError(ctxt,
		    "The proof used in a cast does not prove an equation.\n"
		    +"1. The proof's classifier: "+fla.toString(ctxt)+"\n"
		    +"2. The proof: "+P.toString(ctxt));
	return null;
    }
    
    public Expr dropAnnos(Context ctxt) {
	return t.dropAnnos(ctxt);
    }
    public void checkTermination(Context ctxt) {
        t.checkTermination(ctxt);
    }

    public java.util.Set getDependences() {
        java.util.Set s = t.getDependences();
        s.addAll(P.getDependences());
        if (T != null)
            s.addAll(T.getDependences());
        return s;
    }

    public void checkSpec(Context ctxt, boolean in_type){
	t.checkSpec(ctxt, in_type);
    }

    public void getFreeVarsComputational(Context ctxt, 
					 java.util.Collection vars) {
	t.getFreeVarsComputational(ctxt,vars);
    }

    public guru.carraway.Expr toCarraway(Context ctxt) {
	Expr T1 = classify(ctxt,APPROX_TRIVIAL,false);
	if (T1.construct != T.construct ||
	    T1.construct == VAR || T.construct == VAR) {
	    // these should be the cases we need to include a Carraway cast for
	    guru.carraway.Cast C = new guru.carraway.Cast();
	    C.pos = pos;
	    C.T = T.toCarrawayType(ctxt,false);
	    C.t = t.toCarraway(ctxt);
	    return C;
	}

	return t.toCarraway(ctxt);
    }
}
