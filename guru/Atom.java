package guru;

public class Atom extends Expr
{
    public Expr Y1, Y2;
    public boolean equality; // true if an equality, false if a disequality

    public Atom() {
	super(ATOM);
    }

    public Atom(boolean equality, Expr Y1, Expr Y2) {
	super(ATOM);
	this.equality = equality;
	this.Y1 = Y1;
	this.Y2 = Y2;
    }

    public void do_print(java.io.PrintStream w,
		      Context ctxt) {
	w.print("{ ");
	Y1.print(w,ctxt);
	w.print(equality ? " = " : " != ");
	Y2.print(w,ctxt);
	w.print(" }");
    }
    public int numOcc(Expr e) {
	return Y1.numOcc(e) + Y2.numOcc(e);
    }

    public Expr subst(Expr e, Expr x) {
	Expr nY1 = Y1.subst(e,x), nY2 = Y2.subst(e,x);
	if (nY1 != Y1 || nY2 != Y2)
	    return new Atom(equality, nY1, nY2);
	return this;
    }

    public Expr classify(Context ctxt, int approx, boolean spec) {
	return ctxt.formula;
    }

    public boolean defEqNoAnno(Context ctxt, Expr ee, boolean spec) {
	ee = ee.defExpandTop(ctxt,true,spec);

	if (ee.construct != construct)
	    return false;
	Atom e = (Atom)ee;
	return (equality == e.equality &&
		Y1.defEqNoAnno(ctxt,e.Y1,true) &&
		Y2.defEqNoAnno(ctxt,e.Y2,true));
    }

    public Expr dropAnnos(Context ctxt) {
	Expr nY1 = Y1.dropAnnos(ctxt);
	Expr nY2 = Y2.dropAnnos(ctxt);
	if (nY1 != Y1 || nY2 != Y2)
	    return new Atom(equality,nY1,nY2);
	return this;
    }

    public java.util.Set getDependences() {
        java.util.Set s = Y1.getDependences();
        s.addAll(Y2.getDependences());
        return s;
    }

    public void checkSpec(Context ctxt, boolean in_type, Position p) { }

    public void getFreeVarsComputational(Context ctxt,
					 java.util.Collection vars) { }
}
