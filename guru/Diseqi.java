package guru;

public class Diseqi extends Expr {
    Expr P;

    public Diseqi() {
	super(DISEQI);
    }
    
    public Diseqi(Expr P) {
	super(DISEQI);
	this.P = P;
    }
    
    public void do_print(java.io.PrintStream w, 
			 Context ctxt) {
	w.print("diseqi ");
	P.print(w,ctxt);
    }

    public Expr classify(Context ctxt) {
	Expr cP = P.classify(ctxt).defExpandTop(ctxt);
	if (cP.construct != FORALL)
	    handleError(ctxt,"The proof given to a diseq-proof does not prove an"
			+"implication.\n1. the formula proved: "+cP.toString(ctxt));
	Forall F = (Forall)cP;
	if (F.vars.length != 1)
	    handleError(ctxt,"The proof given to a diseq-proof proves "
			+"universal, but\nwith the wrong number of variables (should be 1)."
			+"\n1. the formula proved: "+cP.toString(ctxt));
	Expr premise = F.types[0].defExpandTop(ctxt);
	if (premise.construct != ATOM || !((Atom)premise).equality)
	    handleError(ctxt,"The proof given to a diseq-proof proves "
			+"an implication, but\nwith the premise is not an equation."
			+"\n1. the premise: "+premise.toString(ctxt)
			+"\n2. the formula proved: "+cP.toString(ctxt));
	Atom e = (Atom)premise;
	Expr tmp = F.body.defExpandTop(ctxt);
	if (tmp.construct != FALSE)
	    handleError(ctxt,"The proof given to a diseq-proof proves "
			+"an implication, but\nthe consequent is not False."
			+"\n1. the consequent: "+tmp.toString(ctxt)
			+"\n2. the formula proved: "+cP.toString(ctxt));
	return new Atom(false, e.Y1, e.Y2);
    }
    
    public Expr subst(Expr e, Expr x) {
	Expr nP = P.subst(e,x);
	if (nP != P)
	    return new Diseqi(nP);
	return this;
    }

    public int numOcc(Expr e) {
	return P.numOcc(e);
    }
    
    public Expr dropAnnos(Context ctxt) {
	return new Bang();
    }

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] v) {
	P.checkTermination(ctxt,IH,arg,v);
    }
}
