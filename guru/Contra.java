package guru;

public class Contra extends Expr {

    public Expr P;
    public Expr F;

    public Contra() {
	super(CONTRA);
    }

    public Contra(Expr P, Expr F) {
	super(CONTRA);
	this.P = P;
	this.F = F;
    }

    public Expr dropAnnos(Context ctxt) {
	return new Bang();
    }

    public void do_print(java.io.PrintStream w,
		      Context ctxt) {
	w.print("contra ");
	P.print(w,ctxt);
	w.print(" ");
	F.print(w,ctxt);
    }

    public int numOcc(Expr e) {
	return F.numOcc(e) + P.numOcc(e);
    }

    public Expr subst(Expr e, Expr x) {
	Expr nP = P.subst(e,x), nF = F.subst(e,x);
	if (nP != P || nF != F)
	    return new Contra(nP, nF);
	return this;
    }

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars) {
	P.checkTermination(ctxt,IH,arg,vars);
    }

    public Expr classify(Context ctxt) {
	Expr cP = P.classify(ctxt);
	Expr cF = F.classify(ctxt);
	if (cF.construct != FORMULA)
	    // I do not think it is possible to have something which is
	    // syntactically a formula and passes classification, but
	    // fails to have classifier formula.  But just in case...
	    handleError(ctxt,
			"The second expression given to a contra-proof is not"
			+"\na formula.\n"
			+"1. The expression: "+F.toString(ctxt)+"\n"
			+"2. Its classifier: "+cF.toString(ctxt));

	if (cP.construct == ATOM) {
	    Atom a = (Atom)cP;
	    if (!a.equality) {
		if (a.Y1.defEq(ctxt, a.Y2))
		    return F;
		handleError(ctxt,
			    "The proof given to a contra-proof does not derive"
			    +" a contradictory disequation.\n"
			    +"1. The proof's classifier: "+ cP.toString(ctxt));
	    }
	}
	handleError(ctxt,
		    "A contra-proof has not been given a proof of a"
		    +" contradictory disequation.\n"
		    +"1. The proof it is given proves: "
		    +cP.toString(ctxt));
	return null;
    }

    public java.util.Set getDependences() {
        java.util.Set s = P.getDependences();
        s.addAll(F.getDependences());
        return s;
    }
}
