package guru;


import java.util.*;
import java.io.*;

public class Impossible extends Expr{
    
    public Expr P, T;
    
    public Impossible() {
        super(IMPOSSIBLE);
    }

    public Impossible(Expr P, Expr T) {
	super(IMPOSSIBLE);
	this.P = P;
	this.T = T;
    }

    public Expr do_rewrite(Context ctxt, Expr e, Expr x, Stack boundVars)
    {
	return this;
    }

    public void do_print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("impossible ");
	P.print(w,ctxt);
	w.print(" ");
	T.print(w,ctxt);
    }
    
    public int numOcc(Expr e) {
	return P.numOcc(e) + T.numOcc(e);
    }

    public Expr subst(Expr e, Expr x) {
	Expr nP = P.subst(e,x);
	Expr nT = T.subst(e,x);
	if (nP != P || nT != T)
	    return new Impossible(nP,nT);
	return this;
    }

    public Expr dropAnnos(Context ctxt) {
	return new Abort(new Bang());
    }

    public isInstC isInstance(Context ctxt, Expr ee) {
	ee = ee.defExpandTop(ctxt);
	if (ee.construct != IMPOSSIBLE)
	    return new isInstC(); // not an instance

	Impossible e = (Impossible)ee;
	return T.isInstance(ctxt, e.T);
    }
    
    public Expr classify(Context ctxt, int approx, boolean spec) {
	Expr cP = null;
	if (approx == NO_APPROX)
	    cP = P.classify(ctxt,approx,spec);
	Expr cT = T.classify(ctxt,approx,spec);
	if (cT.construct != TYPE)
	    handleError(ctxt,
			"An impossible-term is used with an expression "
			+"which is not a type.\n"
			+"1. The expression: "+T.toString(ctxt)+"\n"
			+"2. Its classifier: "+cT.toString(ctxt));
	if (approx > 0)
	    return T;

	if (cP.construct == ATOM) {
	    Atom a = (Atom)cP;
	    if (!a.equality) {
		if (a.Y1.defEq(ctxt, a.Y2))
		    return T;
		handleError(ctxt,
			    "The proof in an impossible-term does not derive"
			    +" a contradictory disequation.\n"
			    +"1. The proof's classifier: "+ cP.toString(ctxt));
	    }
	}
	handleError(ctxt,
		    "The proof in an impossible-term does not prove"
		    +" a contradictory disequation:\n"
		    +"1. the proof's classifier: "+cP.toString(ctxt));
	return null;
    }
    
    public void checkTermination(Context ctxt) {
	handleError(ctxt,"An impossible-term does not terminate.");
    }

    public java.util.Set getDependences() {
        java.util.Set s = P.getDependences();
        s.addAll(T.getDependences());
        return s;
    }

    public void checkSpec(Context ctxt, boolean in_type, Position p){
    }

    public void getFreeVarsComputational(Context ctxt, 
					 java.util.Collection vars) {
    }
}

