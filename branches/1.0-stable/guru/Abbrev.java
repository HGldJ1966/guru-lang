package guru;

import java.util.Stack;

public class Abbrev extends Expr{
	// flags
	static final int	fAbbrevNone = 0x0;
	static final int	fAbbrevEvaluate = 0x1;
	static final int	fAbbrevClassify = 0x2;
	
	int	flags;
    public Var x;
    public Expr U;
    public Expr G;
    protected Expr subst;	// cache for substituted version of G

    public Abbrev(int f, Var x, Expr U, Expr G) {
	super(ABBREV);
	flags = f;
	this.x = x;
	this.U = U;
	this.G = G;
    }

    public void do_print(java.io.PrintStream w, Context ctxt)
    {
		if (ctxt.getFlag("no_expand_vars") )
		{
			if ((flags & fAbbrevEvaluate) != 0)
			    w.print("eabbrev ");
			else if ((flags & fAbbrevClassify) != 0)
			    w.print("cabbrev ");
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
		return new Abbrev(flags, x, nU, G);
	    return this;
	}
	Expr nG = G.subst(e,y);
	if (nU != U || nG != G)
	    return new Abbrev(flags, x, nU, nG);
	return this;
    }
    
    public Expr dropAnnos(Context ctxt) {
	Expr tmp = subst();
	return tmp.dropAnnos(ctxt);
    }

    protected void add_def(Context ctxt) {
    	Expr def = U;
		if ((flags&fAbbrevEvaluate)!=0 && def.isTerm(ctxt))
			def = def.eval(ctxt);
		ctxt.macroDefine(x,def);
    }

    public Expr classify(Context ctxt, int approx, boolean spec) {
    // [Duckki] if wanted, U can be classified here, otherwise:
	// we do not classify U here.  If x is not used, garbage
	// can appear for U.  That is needed, because U might not
	// be classifiable; for example, if it is a term containing
	// bangs, intended to be used in a formula.
	//
	// The reason we do not actually substitute U for x in G and
	// then classify the result is that classification assumes the
	// expression being classified is an expression built by the
	// parser (for purposes of reporting line number information).
		if ((flags&fAbbrevClassify)!=0 && ctxt.getClassifier(x)==null) {
			// copied from Let.java
			Expr T = U.classify(ctxt, approx, spec);
			ctxt.setClassifier(x,T);
		}
	add_def(ctxt);
	Expr cG = G.classify(ctxt, approx, spec);
	if (cG.numOcc(x) == 0)
	    return cG;
	return new Abbrev(flags, x, U, cG);
    }

    public Expr evalStep(Context ctxt) {
	return subst();
    }

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars) {
	subst().checkTermination(ctxt,IH,arg,vars);
    }

    public boolean defEqNoAnno(Context ctxt, Expr e, boolean spec) {
	add_def(ctxt);
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
