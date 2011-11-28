package guru;

public class CompileAs extends Expr{
    
    public Expr t1, t2, P;
    
    public CompileAs() {
	super(COMPILE_AS);
    }
    
    public CompileAs(Expr t1, Expr t2, Expr P) {
	super(COMPILE_AS);
	this.t1 = t1;
	this.t2 = t2;
	this.P = P;
    }

    public void do_print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("compiles ");
	t1.print(w,ctxt);
	w.print(" as ");
	t2.print(w,ctxt);
	w.print(" by ");
	P.print(w,ctxt);
    }

    public int numOcc(Expr e) {
	return t1.numOcc(e) + t2.numOcc(e) + P.numOcc(e);
    }

    public Expr subst(Expr e, Expr x) {
	Expr nt1 = t1.subst(e,x), nt2 = t2.subst(e,x), nP = P.subst(e,x);
	if (nt1 != t1 || nP != P || nt2 != t2)
	    return new CompileAs(nt1, nt2, nP);
	return this;
    }

    public Expr classify(Context ctxt, int approx, boolean spec) {
	Expr ct1 = t1.classify(ctxt, approx, true /* we allow t1 to be specificational, since we
						     won't compile it. */);
	Expr ct2 = t2.classify(ctxt, approx, spec);

	if (approx != NO_APPROX) 
	    return ct1;

	Expr fla = P.classify(ctxt);
	if (fla.construct == ATOM) {
	    Atom q = (Atom)fla;
	    if (q.equality) {
		if (!t1.defEq(ctxt, q.Y1, approx, spec))
		    handleError(ctxt,
				"In a compiles-as term, the equation proved does not have the first child"
				+" of the compiles-as term\nas it left-hand side.\n\n"
				+"1. The equation proved: "+fla.toString(ctxt)
				+"\n2. The first child of the compiles-as term: "
				+t1.toString(ctxt));
		if (!t2.defEq(ctxt, q.Y2, approx, spec))
		    handleError(ctxt,
				"In a compiles-as term, the equation proved does not have the second child"
				+" of the compiles-as term\nas it right-hand side.\n\n"
				+"1. The equation proved: "+fla.toString(ctxt)
				+"\n2. The second child of the compiles-as term: "
				+t2.toString(ctxt));
		return ct1;
	    }
	}

	handleError(ctxt,
		    "The proof used in a compiles-as term does not prove an equation.\n"
		    +"1. The proof's classifier: "+fla.toString(ctxt)+"\n"
		    +"2. The proof: "+P.toString(ctxt));
	return null;
    }
    
    public Expr dropAnnos(Context ctxt) {
	return t2.dropAnnos(ctxt);
    }
    public void checkTermination(Context ctxt) { 
        t2.checkTermination(ctxt);
    }

    public java.util.Set getDependences() {
        java.util.Set s = t1.getDependences();
        s.addAll(t2.getDependences());
        s.addAll(P.getDependences());
        return s;
    }

    public void checkSpec(Context ctxt, boolean in_type, Position p){
	// we do not check specificationality in t1, since we allow t1 to be specificational
	t2.checkSpec(ctxt, in_type, pos);
    }

    public void getFreeVarsComputational(Context ctxt, 
					 java.util.Collection vars) {
	t1.getFreeVarsComputational(ctxt,vars);
	t2.getFreeVarsComputational(ctxt,vars);
    }

    public guru.carraway.Expr toCarraway(Context ctxt) {
	return t2.toCarraway(ctxt);
    }
}
