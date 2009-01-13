package guru;

public class Symm extends Expr{
    
    public Expr P;
    
    public Symm() { 
	super(SYMM);
    }

    public Symm(Expr P) {
	super(SYMM);
	this.P = P;
    }	    

    public Expr dropAnnos(Context ctxt) {
	return new Bang();
    }

    public void do_print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("symm ");
	P.print(w,ctxt);
    }

    public int numOcc(Expr e) {
	return P.numOcc(e);
    }
    
    public Expr subst(Expr e, Expr x) {
	Expr n = P.subst(e,x);
	if (n != P)
	    return new Symm(n);
	return this;
    }

    public Expr classify(Context ctxt) {
	Expr cP = P.classify(ctxt).defExpandTop(ctxt);

	if (cP.construct == ATOM) {
	    Atom a = (Atom)cP;
	    return new Atom(a.equality, a.Y2, a.Y1);
	}

	handleError(ctxt,
		    "Subproof of a symm-proof does not prove an"
		    +" equation or disequation.\n"
		    +"1. The subproof's classifier: "+cP.toString(ctxt)
		    +"2. The subproof: "+P.toString(ctxt));
	
	return null;
    }

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars) {
	P.checkTermination(ctxt,IH,arg,vars);
    }

    public java.util.Set getDependences() {
        return P.getDependences();
    }

}
