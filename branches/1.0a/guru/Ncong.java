package guru;

public class Ncong extends Expr{
    
    public Expr Ihat, I1, I2;
    public Expr P;
    
    public Ncong() { 
	super(NCONG);
    }

    public Ncong(Expr Ihat, Expr I1, Expr I2, Expr P) {
	super(NCONG);
	this.Ihat = Ihat;
	this.I1 = I1;
	this.I2 = I2;
	this.P = P;
    }

    public Expr dropAnnos(Context ctxt) {
	return new Bang();
    }

    public void do_print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("ncong ");
	Ihat.print(w,ctxt);
	w.print(" ");
	I1.print(w,ctxt);
	w.print(" ");
	I2.print(w,ctxt);
	w.print(" ");
	P.print(w,ctxt);
    }
    
    public int numOcc(Expr e) {
	return Ihat.numOcc(e) + I1.numOcc(e) + I2.numOcc(e) + P.numOcc(e);
    }

    public Expr subst(Expr e, Expr x) {
	Expr n1 = Ihat.subst(e,x), n2 = I1.subst(e,x), n3 = I2.subst(e,x),
	    n4 = P.subst(e,x);
	if (n1 != Ihat || n2 != I1 || n3 != I2 || n4 != P)
	    return new Ncong(n1,n2,n3,n4);
	return this;
    }
   
    protected void checkInst(Context ctxt, Expr I, Expr expected, 
			     String which) {
	isInstC a = Ihat.isInstance(ctxt, I);
	if (!a.is)
	    handleError(ctxt,
			"The "+which+" term given to an ncong-proof is not\n"
			+"an instance of the given context.\n"
			+"1. The "+which+" term : "+I.toString(ctxt)+"\n"
			+"2. The context: "+Ihat.toString(ctxt));
	if (!a.val.defEq(ctxt, expected))
	    handleError(ctxt,
			"The "+which+" term given to an ncong-proof does not\n"
			+"have the expected subterm in the * position of the\n"
			+"given context.\n"
			+"1. The "+which+" term : "+I.toString(ctxt)+"\n"
			+"2. The expected subterm : "+expected.toString(ctxt)
			+"\n"
			+"3. The context: "+Ihat.toString(ctxt));
    }


    public Expr classify(Context ctxt) {
	Expr cP = P.classify(ctxt);

	if (cP.construct == ATOM) {
	    Atom a = (Atom)cP;
	    if (!a.equality) {
		checkInst(ctxt, I1, a.Y1, "first");
		checkInst(ctxt, I2, a.Y2, "second");
		
		return new Atom(false, I1, I2);
	    }
	}

	handleError(ctxt,
		    "Subproof of a ncong-proof does not prove a"
		    +" disequation.\n"
		    +"1. The subproof's classifier: "+cP.toString(ctxt)
		    +"2. The subproof: "+P.toString(ctxt));
	
	return null;
    }


    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars) {
	P.checkTermination(ctxt,IH,arg,vars);
    }

    public java.util.Set getDependences() {
        java.util.Set s = Ihat.getDependences();
        s.addAll(I1.getDependences());
        s.addAll(I2.getDependences());
        s.addAll(P.getDependences());
        return s;
    }
}
