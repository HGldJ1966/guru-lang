package guru;

public class Existsi extends Expr{

    public Expr I;
    public Expr Fhat;
    public Expr P;

    public Existsi() {
	super(EXISTSI);
    }

    public Existsi(Expr I, Expr Fhat, Expr P) {
	super(EXISTSI);
	this.I = I;
	this.Fhat = Fhat;
	this.P = P;
    }

    public Expr dropAnnos(Context ctxt) {
	return new Bang();
    }

    public void do_print(java.io.PrintStream w,
		      Context ctxt) {
	w.print("existsi ");
	I.print(w,ctxt);
	w.print(" ");
	Fhat.print(w,ctxt);
	w.print(" ");
	P.print(w,ctxt);
    }

    public int numOcc(Expr e) {
	return I.numOcc(e) + Fhat.numOcc(e) + P.numOcc(e);
    }

    public Expr subst(Expr e, Expr x) {
	Expr nI = I.subst(e,x), nFhat = Fhat.subst(e,x), nP = P.subst(e,x);
	if (nI != I || nFhat != Fhat || nP != P)
	    return new Existsi(nI, nFhat, nP);
	return this;
    }

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars) {
	P.checkTermination(ctxt,IH,arg,vars);
    }

    public Expr classify(Context ctxt) {
        if (!I.termTerminates(ctxt))
            handleError(ctxt,
                        "Expression given to existsi must be terminating; "
                        +"perhaps you need a terminates...by cast?");
	Expr cI = I.classify(ctxt);
	if (!cI.isB(ctxt) && !Expr.isFormula(cI.construct))
	    handleError(ctxt,
			"Expression given to existsi is not "
			+"classifiable by a\n"
			+"B expression or formula.\n"
			+"1. the term: "+I.toString(ctxt)+"\n"
			+"2. its classifier: "+cI.toString(ctxt));
	Expr cP = P.classify(ctxt);
	Expr expected = Fhat.subst(I,ctxt.star);
	if (!cP.defEq(ctxt,expected))
	    handleError(ctxt,
			"Proof given to existsi does not prove the right"
			+" instance of the given context.\n"
			+"1. the proof proves : "+cP.toString(ctxt)+"\n"
			+"2. expected instance: "+expected.toString(ctxt));
	Var v = new Var("x");
	Expr F = Fhat.subst(v,ctxt.star);
	ctxt.setClassifier(v,cI);
	return new Exists(v,cI,F);
    }

    public java.util.Set getDependences() {
        java.util.Set s = I.getDependences();
        s.addAll(Fhat.getDependences());
        s.addAll(P.getDependences());
        return s;
    }
}
