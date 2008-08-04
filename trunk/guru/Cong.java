package guru;

public class Cong extends Expr{

    public Expr Estar;
    public Expr P;

    public Cong() {
	super(CONG);
    }

    public Cong(Expr Estar, Expr P) {
	super(CONG);
	this.Estar = Estar;
	this.P = P;
    }

    public Expr dropAnnos(Context ctxt) {
	return new Bang();
    }

    public void do_print(java.io.PrintStream w,
		      Context ctxt) {
	w.print("cong ");
	Estar.print(w,ctxt);
	w.print(" ");
	P.print(w,ctxt);
    }

    public int numOcc(Expr e) {
	return Estar.numOcc(e) + P.numOcc(e);
    }

    public Expr subst(Expr e, Expr x) {
	Expr nEstar = Estar.subst(e,x), nP = P.subst(e,x);
	if (nEstar != Estar || nP != P)
	    return new Cong(nEstar, nP);
	return this;
    }

    public Expr classify(Context ctxt) {
	Expr cP = P.classify(ctxt);

	if (cP.construct == ATOM) {
	    Atom a = (Atom)cP;
	    if (a.equality) {

		Expr nY1 = Estar.subst(a.Y1, ctxt.star);
		Expr nY2 = Estar.subst(a.Y2, ctxt.star);

		return new Atom(a.equality, nY1, nY2);
	    }
	}

	handleError(ctxt,
		    "Subproof of a cong-proof does not prove an"
		    +" equation.\n"
		    +"1. The subproof's classifier: "+cP.toString(ctxt)+"\n"
		    +"2. The subproof: "+P.toString(ctxt));

	return null;
    }

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars) {
	P.checkTermination(ctxt, IH,arg,vars);
    }

    public java.util.Set getDependences() {
        java.util.Set s = Estar.getDependences();
        s.addAll(P.getDependences());
        return s;
    }
}
