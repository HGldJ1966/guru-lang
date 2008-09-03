package guru;

public class Inv extends Expr{
    
    //public Expr E;
    public Expr t;
    public Expr P;

    public Inv() { 
	super(INV);
    }

    public Expr dropAnnos(Context ctxt) {
	return new Bang();
    }

    public void do_print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("cinv ");
	//E.print(w,ctxt);
	//w.print(" ");
	t.print(w,ctxt);
	w.print(" ");
	P.print(w,ctxt);
    }

    public int numOcc(Expr e) {
	//return E.numOcc(e) + t.numOcc(e) + P.numOcc(e);
	return t.numOcc(e) + P.numOcc(e);
    }
    
    public Expr subst(Expr e, Expr x) {
	//Expr nE = E.subst(e,x);
	Expr nt = t.subst(e,x);
	Expr nP = P.subst(e,x);
	if (nP == P && nt == t) //&& nE == E)
	    return this;
	Inv ret = new Inv();
	//ret.E = nE;
	ret.t = nt;
	ret.P = nP;
	return ret;
    }

    public Expr classify(Context ctxt) {
	Expr cP = P.classify(ctxt);
	if (cP.construct != ATOM || !((Atom)cP).equality)
	    handleError(ctxt, "Subproof of an inv-proof does not prove "
			+ "an equation.\n"
			+"1. The subproof's classifier: "+cP.toString(ctxt)
			+"\n2. The subproof: "+P.toString(ctxt)
			+ "\n Construct: " + cP.construct);
	
	Atom a = (Atom)cP;

	a.Y2.checkTermination(ctxt);

	Expr T = t.classify(ctxt);

	// AS: cinv is not that useful unless t is evaluated.
	Expr et = t.eval(ctxt);

	Expr Y1 = a.Y1.defExpandTop(ctxt).dropAnnos(ctxt);
	if (Y1.construct == TERM_APP)
	    Y1 = ((TermApp)Y1).spineForm(ctxt, true, true, true);

	if (!Y1.subtermDefEqNoAnno(ctxt, et))
	    handleError(ctxt, "We cannot find the evaluated given term in the "
			+"LHS of the equation\nproved by the subproof given to"
			+" a cinv-proof.\n"
			+"1. The equation: "+cP.toString(ctxt)
			+"\n2. The given term: "+t.toString(ctxt)
			+"\n3. The evaluated given term: "+et.toString(ctxt));
	ctxt.resetNotDefEq();

	Var v = new Var("x_inv");
	return new Exists(v, T, new Atom(true, t, v));
    }

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars) {
	P.checkTermination(ctxt,IH,arg,vars);
    }

    public java.util.Set getDependences() {
        //java.util.Set s = E.getDependences();
        //s.addAll(t.getDependences());
        java.util.Set s = t.getDependences();
        s.addAll(P.getDependences());
        return s;
    }
}
