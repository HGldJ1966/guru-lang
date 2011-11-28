package guru;

public class Join extends Expr{
    
    public Expr t1;
    public Expr t2;
    
    public Join() {
        super(JOIN);
    }

    public Join(Expr t1, Expr t2) {
	super(JOIN);
	this.t1 = t1;
	this.t2 = t2;
    }

    public Expr dropAnnos(Context ctxt) {
	return new Bang();
    }

    public void do_print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("join ");
	t1.print(w,ctxt);
	w.print(" ");
	t2.print(w,ctxt);
    }

    public int numOcc(Expr e) {
	return t1.numOcc(e) + t2.numOcc(e);
    }
    
    public Expr subst(Expr e, Expr x) {
	Expr n1 = t1.subst(e,x), n2 = t2.subst(e,x);
	if (n1 != t1 || n2 != t2)
	    return new Join(n1,n2);
	return this;
    }

    public Expr classify(Context ctxt) {
	t1 = t1.dropAnnos(ctxt);
	t2 = t2.dropAnnos(ctxt);

	if (ctxt.getFlag("debug_join")) {
	    ctxt.w.println("About to join: "+t1.toString(ctxt) + "  and  " + t2.toString(ctxt) + " {");
	    ctxt.w.flush();
	}
	
	Expr t1a = t1.eval(ctxt);
	

	Expr t2a = t2.eval(ctxt);
	ctxt.resetNotDefEq();

	if (ctxt.getFlag("debug_join")) {
	    ctxt.w.println("} Done evaluating: "+t1.toString(ctxt) + "  and  " + t2.toString(ctxt));
	    ctxt.w.flush();
	}

	if (t1a.defEq(ctxt,t2a)) 
	    return new Atom(true,t1,t2);

	/*	System.out.print("t1:");
	t1.do_print(System.out,ctxt);
	System.out.println();
	System.out.print("t1a:");
	t1a.do_print(System.out,ctxt);
	System.out.println(); */

	handleError(ctxt,
		    "Evaluation cannot join two terms in a join-proof.\n"
		    +"1. normal form of first term: "
		    +t1a.toString(ctxt)+"\n"
		    +"2. normal form of second term: "
		    +t2a.toString(ctxt)+"\n");
	return null;
    }
	    
    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars)
    { }

    public java.util.Set getDependences() {
        java.util.Set s = t1.getDependences();
        s.addAll(t2.getDependences());
        return s;
    }
}
