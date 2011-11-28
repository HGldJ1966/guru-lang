package guru;

public class Inj extends Expr{
    
    public Expr Ihat;
    public Expr P;
    
    public Inj() { 
	super(INJ);
    }

    public Inj(Expr Ihat, Expr P) {
	super(INJ);
	this.Ihat = Ihat;
	this.P = P;
    }

    public Expr dropAnnos(Context ctxt) {
	return new Bang();
    }

    public void do_print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("inj ");
	Ihat.print(w,ctxt);
	w.print(" ");
	P.print(w,ctxt);
    }
    
    public int numOcc(Expr e) {
	return Ihat.numOcc(e) + P.numOcc(e);
    }

    public Expr subst(Expr e, Expr x) {
	Expr n1 = Ihat.subst(e,x), n2 = P.subst(e,x);
	if (n1 != Ihat || n2 != P)
	    return new Inj(n1,n2);
	return this;
    }

    protected Expr checkInst(Context ctxt, Atom f, Expr Y, String which) {
	isInstC a = Ihat.isInstance(ctxt, Y);
	if (!a.is)
	    handleError(ctxt,
			"The "+which+" of the equation proved by the"
			+" subproof of an inj-proof is not\n"
			+"an instance of the given context.\n"
			+"1. The equation: "+f.toString(ctxt)+"\n"
			+"2. The "+which+": "+Y.toString(ctxt)+"\n"
			+"3. The context: "+Ihat.toString(ctxt));
	if (!a.val.isY(ctxt)) 
	    handleError(ctxt,
			"The expression extracted by an inj-proof from the"
			+which+" of the equation proved by its\n"
			+"subproof is not a term or a type\n"
			+"1. The equation: "+f.toString(ctxt)+"\n"
			+"2. The "+which+": "+Y.toString(ctxt)+"\n"
			+"3. The extracted expression : "+a.val.toString(ctxt));

	return a.val;
    }

    public Expr classify(Context ctxt) {
	Expr cP = P.classify(ctxt);
	if (cP.construct == ATOM) {
	    Atom a = (Atom)cP;
	    if (a.equality) {
		Expr Y = checkInst(ctxt, a, a.Y1, "LHS");
		Expr Yp = checkInst(ctxt, a, a.Y2, "RHS");
		Expr ret = new Atom(true, Y, Yp);
		if (Y.isTypeOrKind(ctxt)) {
		    // we need to check that we are not pulling an
		    // equation between types out of an equation
		    // between terms.  If dropping annotations causes
		    // the star to disappear, we know it was used inside
		    // a term somewhere.  Note that even though stars
		    // are not considered types, TermApp.dropAnnos()
		    // drops stars as arguments in applications for
		    // our benefit.
		    boolean ttoT = a.Y1.isTerm(ctxt);
		    if (!ttoT) {
			Expr tmp = Ihat.dropAnnos(ctxt);
			ttoT = (tmp.numOcc(ctxt.star) == 0);
		    }
		    if (ttoT)
			handleError
			    (ctxt,
			     "An inj-proof is trying to go from an equality"
			     +" on terms\nto an equality on types. This is"
			     +" disallowed.\n"
			     +"1. the term equation: "+cP.toString(ctxt)
			     +"\n"
			     +"2. the desired type equation: "
			     +ret.toString(ctxt));
		}
		return ret;
	    }
	}
	handleError(ctxt,
		    "The subproof of an inj-proof does not prove an"
		    +" equation.\n"
		    +"1. The subproof's classifier: "+cP.toString(ctxt)+"\n"
		    +"2. The subproof: "+P.toString(ctxt));
	return null;
    }

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars) {
	P.checkTermination(ctxt,IH,arg,vars);
    }

    public java.util.Set getDependences() {
        java.util.Set s = Ihat.getDependences();
        s.addAll(P.getDependences());
        return s;
    }
}
