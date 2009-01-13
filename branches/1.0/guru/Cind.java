package guru;

public class Cind extends Expr {
    
    public Expr P;
    public Expr t;
    public Var v;

    public Cind() {
	super(CIND);
	t = null;
	v = null;
    }
    
    public Cind(Expr P) {
	super(CIND);
	this.P = P;
	t = null;
	v = null;
    }

    private Expr create_t(Context ctxt) {
	if (t == null) {
	    Expr fla = P.classify(ctxt);
	    if (fla.construct != ATOM)
		handleError(ctxt,
			    "The proof used in a cind does not prove an equation.\n"
			    +"1. The proof's classifier: "+fla.toString(ctxt)+"\n"
			    +"2. The proof: "+P.toString(ctxt));
	    Atom q = (Atom) fla;
	    if (q.Y1.construct != TERM_APP)
		handleError(ctxt,
			    "The LHS of a proof used in cind is not a term application.\n"
			    +"1. The proof's classifier: "+fla.toString(ctxt)+"\n"
			    +"2. The proof: "+P.toString(ctxt));
	    TermApp ta = (TermApp) q.Y1;
	    Expr head = ta.head;
	    Expr [] X = ta.X;
	    Expr I = q.Y2;
	    v = new Var("budget");
	    Expr cnat = ctxt.lookup("nat");
	    if (cnat == null)
		handleError(ctxt, "Type \"nat\", needed for cind, not found in current context");
	    ctxt.setClassifier(v, cnat);
	    t = new Atom(true, new TermApp( new TermApp( new Cutoff(ta.head), v), X), I);
	}
	return t;
    }

    public void do_print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("cind  ");
	P.print(w,ctxt);
    }

    public int numOcc(Expr e) {
	return P.numOcc(e);
    }

    public Expr subst(Expr e, Expr x) {
	Expr nP = P.subst(e,x);
	if (nP != P)
	    return new Cind(nP);
	return this;
    }

    public Expr classify(Context ctxt) {
	Expr ct = create_t(ctxt);
	Expr cnat = ctxt.lookup("nat");
	if (cnat == null)
	    handleError(ctxt, "Type \"nat\", needed for cind, not found in current context");
	ctxt.setClassifier(v, cnat);
	return new Exists(v, cnat, ct);
    }
    
    public Expr dropAnnos(Context ctxt) {
	return new Bang();
    }
}
