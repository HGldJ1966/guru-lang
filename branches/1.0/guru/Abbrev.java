package guru;

import java.util.Stack;

public class Abbrev extends Expr{

    public Var x;
    public Expr U;
    public Expr G;
    protected Expr subst;

    public Abbrev(boolean eabbrev, Var x, Expr U, Expr G) {
	super(eabbrev ? EABBREV : ABBREV);
	this.x = x;
	this.U = U;
	this.G = G;
    }

    public void do_print(java.io.PrintStream w, Context ctxt)
    {
		if (ctxt.getFlag("no_expand_vars") )
		{
			if (construct == EABBREV)
			    w.print("eabbrev ");
			else
			    w.print("abbrev ");
			x.abbrev_print(w,ctxt);
			w.print(" = ");
			U.print(w,ctxt);
			w.print(" in ");
		}
		G.print(w,ctxt);
    }

    public Expr subst() {
	if (subst == null)
	    subst = G.subst(U,x);
	return subst;
    }

    public int numOcc(Expr e)
    {
    	return subst().numOcc(e);
    }

    public Expr subst(Expr e, Expr y) {
	Expr nU = U.subst(e,y);
	if (x == y) {
	    if (nU != U)
		return new Abbrev(construct == EABBREV, x, nU, G);
	    return this;
	}
	Expr nG = G.subst(e,y);
	if (nU != U || nG != G)
	    return new Abbrev(construct == EABBREV, x, nU, nG);
	return this;
    }
    
    public Expr dropAnnos(Context ctxt) {
	Expr tmp = subst();
	return tmp.dropAnnos(ctxt);
    }

    protected void add_def(Context ctxt, Expr def) {
	if (construct == EABBREV)
	    if (def.isTerm(ctxt))
		def = def.eval(ctxt);
	ctxt.macroDefine(x,def);
    }

    public Expr classify(Context ctxt, int approx, boolean spec) {
	// we do not classify U here.  If x is not used, garbage
	// can appear for U.  That is needed, because U might not
	// be classifiable; for example, if it is a term containing
	// bangs, intended to be used in a formula.
	//
	// The reason we do not actually substitute U for x in G and
	// then classify the result is that classification assumes the
	// expression being classified is an expression built by the
	// parser (for purposes of reporting line number information).
	add_def(ctxt, U);
	Expr cG = G.classify(ctxt, approx, spec);
	if (cG.numOcc(x) == 0)
	    return cG;
	return new Abbrev(construct == EABBREV, x, U, cG);
    }

    public Expr evalStep(Context ctxt) {
	return subst();
    }

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars) {
	subst().checkTermination(ctxt,IH,arg,vars);
    }

    public boolean defEqNoAnno(Context ctxt, Expr e, boolean spec) {
	add_def(ctxt,U);
	return G.defEqNoAnno(ctxt,e,spec);
    }

    public void checkTermination(Context ctxt) {
        subst().checkTermination(ctxt);
    }

    public void getFreeVarsComputational(Context ctxt,
					 java.util.Collection vars) {
	U.getFreeVarsComputational(ctxt, vars);
	G.getFreeVarsComputational(ctxt, vars);
	vars.remove(x);
    }

    public java.util.Set getDependences() {
        java.util.Set s = U.getDependences();
        s.addAll(G.getDependences());
        return s;
    }
    
    
    public Expr do_rewrite(Context ctxt, Expr e, Expr x, Stack boundVars) {
    	return subst().do_rewrite(ctxt, e, x, boundVars);
    }
    

    public void checkSpec(Context ctxt, boolean in_type, Position p){
	subst().checkSpec(ctxt, in_type, p);
    }
}
