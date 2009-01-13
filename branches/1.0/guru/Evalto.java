package guru;

public class Evalto extends Expr{
    
    public Expr t1, t2;
    
    public Evalto() {
        super(EVALTO);
    }

    public Evalto(Expr t1, Expr t2) {
	super(EVALTO);
	this.t1 = t1;
	this.t2 = t2;
    }

    public Expr dropAnnos(Context ctxt) {
	return new Bang();
    }

    public void do_print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("evalto ");
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
	    return new Evalto(n1,n2);
	return this;
    }

    public Expr classify(Context ctxt) {
	Expr orig1 = t1;
	Expr orig2 = t2;
	t1 = t1.dropAnnos(ctxt);
	t2 = t2.dropAnnos(ctxt);
	
	Expr cur = t1, prev;
	boolean eq = false;
	boolean first = true, dbg = ctxt.getFlag("debug_eval");
	ctxt.resetNotDefEq();
	do {
	    if (dbg) 
		ctxt.printDefEqErrorIf();
	    if (cur.result)
		break;
	    prev = cur;
	    cur = cur.evalStep(ctxt);
	    if (dbg) {
		if (first) {
		    first = false;
		    System.out.print("[ " + prev.toString(ctxt));
		}
		System.out.print(" -->\n  " + cur.toString(ctxt));
	    }
	}
	while(prev != cur && !(eq = cur.defEq(ctxt,t2)));

	ctxt.resetNotDefEq();

	if (dbg && !first)
	    // we took at least one step (and we are debugging)
	    System.out.println("]");

	if (!eq)
	    handleError(ctxt,"Evaluation does not lead from the first term"
			+" to the second\nin an evalto-proof."
			+"\n1. first term without annos: "+t1.toString(ctxt)
			+"\n2. second term without annos: "+t2.toString(ctxt)
			+"\n3. normal form of first term: "
			+cur.toString(ctxt));

	return new Atom(true,t1,t2);
    }
	    
    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars)
    { }

    public java.util.Set getDependences() {
        java.util.Set s = t1.getDependences();
        s.addAll(t2.getDependences());
        return s;
    }
}
