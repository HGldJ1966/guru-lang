package guru;

public class Size extends Expr {
    
    public Expr t;

    public Size() {
	super(SIZE);
    }
    
    public Size(Expr t) {
	super(SIZE);
	this.t = t;
    }

    public void do_print(java.io.PrintStream w, 
			 Context ctxt) {
	w.print("size ");
	t.print(w,ctxt);
    }

    public Expr do_rewrite(Context ctxt, Expr e, Expr x, 
			   java.util.Stack boundVars) {
	Expr nt = t.rewrite(ctxt,e,x,boundVars);
	if (nt != t)
	    return new Size(nt);
	return this;
    }

    public int numOcc(Expr e) {
	return t.numOcc(e);
    }

    public Expr subst(Expr e, Expr y) {
	Expr nt = t.subst(e,y);
	if (nt != t)
	    return new Size(nt);
	return this;
    }

    public Expr classify(Context ctxt, int approx, boolean spec) {
	t.classify(ctxt, approx, spec);
	return _const(ctxt,"nat");
    }
    
    public Expr dropAnnos(Context ctxt) {
	Expr nt = t.dropAnnos(ctxt);
	if (nt != t)
	    return new Size(nt);
	return this;
    }

    public int hashCode_h(Context ctxt) {
	return t.hashCode_h(ctxt) + 11;
    }

    public boolean defEqNoAnno(Context ctxt, Expr ee, boolean spec) {
	ee = ee.defExpandTop(ctxt,true,spec);
	if (ee.construct != construct) {
	    ctxt.notDefEq(this,ee);
	    return false;
	}
	Size e = (Size)ee;

	return t.defEqNoAnno(ctxt,e.t,spec);
    }

    // this is how we axiomatize the fact that every value has a size.
    public void checkTermination(Context ctxt) {
        t.checkTermination(ctxt);
    }

    public Expr evalStep(Context ctxt) {
	Expr nt = t.evalStep(ctxt);
	if (nt != t)
	    return new Size(nt);
	if (t.construct == ABORT)
	    return ctxt.abort;
	
	if (t.construct == FUN_TERM)
	    return _const(ctxt,"Z");
	if (t.construct == CONST) {
	    Expr ret = new TermApp(_const(ctxt,"S"), _const(ctxt,"Z"));
	    ret.pos = pos;
	    return ret;
	}
	if (t.construct == TERM_APP) {
	    TermApp a = (TermApp)((TermApp)t).spineForm(ctxt,true,true,true);
	    Expr ret = _const(ctxt,"Z");
	    Expr plus = _const(ctxt,"plus");
	    for (int i = 0, iend = a.X.length; i < iend; i++)
		ret = new TermApp(plus,ret,new Size(a.X[i]));
	    ret = new TermApp(_const(ctxt,"S"), ret);
	    ret.pos = pos;
	    return ret;
	}

	// this could happen if t is a stuck term
	return this;
    }

    public void checkSpec(Context ctxt, boolean in_type, Position p){
	handleError(ctxt, "A size-term is being" 
		    + " used in a non-specificational location.\n"
		    + "1. the size-term: " + toString(ctxt));
    }

    public void getFreeVarsComputational(Context ctxt, 
					 java.util.Collection vars) {
	t.getFreeVarsComputational(ctxt,vars);
    }

}
