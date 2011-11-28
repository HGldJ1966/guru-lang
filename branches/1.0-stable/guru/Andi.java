package guru;

public class Andi extends Expr{

    public Expr P1;
    public Expr P2;

    public Andi() {
	super(ANDI);
    }

    public Andi(Expr P1, Expr P2) {
	super(ANDI);
	this.P1 = P1;
	this.P2 = P2;
    }

    public Expr dropAnnos(Context ctxt) {
	return new Bang();
    }

    public void do_print(java.io.PrintStream w,
			 Context ctxt) {
	w.print("andi ");
	P1.print(w,ctxt);
	w.print(" ");
	P2.print(w,ctxt);
    }

    public int numOcc(Expr e) {
	return P1.numOcc(e) + P2.numOcc(e);
    }

    public Expr subst(Expr e, Expr x) {
	Expr nP1 = P1.subst(e,x), nP2 = P2.subst(e,x);
	if (nP1 != P1 || nP2 != P2)
	    return new Andi(nP1, nP2);
	return this;
    }

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars) {
	P1.checkTermination(ctxt,IH,arg,vars);
	P2.checkTermination(ctxt,IH,arg,vars);
    }

    public Expr classify(Context ctxt) {
	Expr cP1 = P1.classify(ctxt);
	Expr cP2 = P2.classify(ctxt);
	Var v = new Var("x");
	ctxt.setClassifier(v,cP1);
	return new Exists(v,cP1,cP2);
    }

    public java.util.Set getDependences() {
        java.util.Set s = P1.getDependences();
        s.addAll(P2.getDependences());
        return s;
    }
}
