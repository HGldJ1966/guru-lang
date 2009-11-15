package guru;

public class Trans extends Expr{
    
    public Expr P1;
    public Expr P2;
    
    public Trans() { 
	super(TRANS);
    }

    public Trans(Expr P1, Expr P2) {
	super(TRANS);
	this.P1 = P1;
	this.P2 = P2;
    }

    public Expr dropAnnos(Context ctxt) {
	return new Bang();
    }

    public void do_print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("trans ");
	P1.print(w,ctxt);
	w.print(" ");
	P2.print(w,ctxt);
    }
    
    public int numOcc(Expr e) {
	return P1.numOcc(e) + P2.numOcc(e);
    }

    public Expr subst(Expr e, Expr x) {
	Expr n1 = P1.subst(e,x), n2 = P2.subst(e,x);
	if (n1 != P1 || n2 != P2)
	    return new Trans(n1,n2);
	return this;
    }

    public Expr classify(Context ctxt) {
	Expr cP1 = P1.classify(ctxt).defExpandTop(ctxt);
	Expr cP2 = P2.classify(ctxt).defExpandTop(ctxt);

	if (cP1.construct == ATOM) {
	    Atom a1 = (Atom)cP1;
	    if (a1.equality) {
		if (cP2.construct == ATOM) {
		    Atom a2 = (Atom)cP2;
		    
		    if (!a1.Y2.defEq(ctxt,a2.Y1)) {
                        String withoutAnnos = (a1 != a1.dropAnnos(ctxt) || a2 != a2.dropAnnos(ctxt)) ?
                            ( "\n"
                              +"\n"
                              +"The above trans-proof mismatch without annotations:\n"
                              +"1. First equation:  "+a1.dropAnnos(ctxt).toString(ctxt)+"\n"
                              +"2. Second equation: "+a2.dropAnnos(ctxt).toString(ctxt) ) :
                            "";
			handleError(ctxt,
				    "A trans-proof is attempting to go from"
				    +" a to b and then b' to c,\n"
				    +"where b is not definitionally equal to"
				    +" b'.\n"
                                    +"\n"
				    +"1. First equation:  "+a1.toString(ctxt)
				    +"\n"
				    +"2. Second equation: "+a2.toString(ctxt)
                                    +withoutAnnos);
                    }
		    return new Atom(a2.equality, a1.Y1, a2.Y2);
		}
		handleError(ctxt,
			    "Second subproof of a trans-proof does not prove"
			    +" an equation or disequation.\n"
			    +"1. The subproof's classifier: "
			    +cP2.toString(ctxt)+"\n"
			    +"2. The subproof: "+P2.toString(ctxt));
	    }
	}

	handleError(ctxt,
		    "First subproof of a trans-proof does not prove an"
		    +" equation.\n"
		    +"1. The subproof's classifier: "+cP1.toString(ctxt)+"\n"
		    +"2. The subproof: "+P1.toString(ctxt));
	
	return null;
    }

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars) {
	P1.checkTermination(ctxt,IH,arg,vars);
	P2.checkTermination(ctxt,IH,arg,vars);
    }

    public java.util.Set getDependences() {
        java.util.Set s = P1.getDependences();
        s.addAll(P2.getDependences());
        return s;
    }

}
