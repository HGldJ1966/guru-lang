package guru;

public class Do extends Expr {
    
    public Expr[] ts;
    public Expr t;
    
    public Do() {
	super(DO);
    }
    
    public Do(Expr[] ts, Expr t) {
	super(DO);
	this.ts = ts;
	this.t = t;
    }

    public void do_print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("do ");
	for (int i = 0, iend = ts.length; i < iend; i++) {
	    ts[i].print(w,ctxt);
	    w.print(" ");
	}
	t.print(w,ctxt);
	w.print(" end");
    }

    public int numOcc(Expr e) {
	int n = 0;
	for (int i = 0, iend = ts.length; i < iend; i++) 
	    n += ts[i].numOcc(e);
	
	return t.numOcc(e) + n;
    }

    public Expr subst(Expr e, Expr x) {
	Expr[] nts = new Expr[ts.length];
	boolean changed = false;
	for (int i = 0, iend = ts.length; i < iend; i++) {
	    nts[i] = ts[i].subst(e,x);
	    changed = changed || (nts[i] != ts[i]);
	}
	    
	Expr nt = t.subst(e,x);
	if (nt != t || changed)
	    return new Do(nts, nt);
	return this;
    }

    public Expr classify(Context ctxt, int approx, boolean spec) {
	for (int i = 0, iend = ts.length; i < iend; i++) {
	    Expr tau = ts[i].classify(ctxt,approx,spec);
	    if (tau.defExpandTop(ctxt,false,spec).construct != VOID)
		handleError(ctxt, "A do-term contains a subterm which is not the last one, but has non-void type.\n\n"
			    +"1. the subterm: "+ts[i].toString(ctxt)
			    +"\n\n2. its type: "+tau.toString(ctxt));
	}

	return t.classify(ctxt, approx, spec);
    }
    
    public Expr dropAnnos(Context ctxt) {
	Expr[] nts = new Expr[ts.length];
	boolean changed = false;
	for (int i = 0, iend = ts.length; i < iend; i++) {
	    nts[i] = ts[i].dropAnnos(ctxt);
	    changed = changed || (nts[i] != ts[i]);
	}
	Expr nt = t.dropAnnos(ctxt);
	if (changed || nt != t)
	    return new Do(nts,nt);
	return this;
    }
    public void checkTermination(Context ctxt) {
	for (int i = 0, iend = ts.length; i < iend; i++) 
	    ts[i].checkTermination(ctxt);
        t.checkTermination(ctxt);
    }

    public java.util.Set getDependences() {
        java.util.Set s = t.getDependences();
	for (int i = 0, iend = ts.length; i < iend; i++) 
	    s.addAll(ts[i].getDependences());
        return s;
    }

    public void checkSpec(Context ctxt, boolean in_type){
	for (int i = 0, iend = ts.length; i < iend; i++) 
	    ts[i].checkSpec(ctxt,in_type);
	t.checkSpec(ctxt, in_type);
    }

    public void getFreeVarsComputational(Context ctxt, 
					 java.util.Collection vars) {
	for (int i = 0, iend = ts.length; i < iend; i++) 
	    ts[i].getFreeVarsComputational(ctxt,vars);
	t.getFreeVarsComputational(ctxt,vars);
    }

    public boolean defEqNoAnno(Context ctxt, Expr e, boolean spec) {
	e = e.defExpandTop(ctxt);
	if (e.construct != construct) {
	    ctxt.notDefEq(this,e);
	    return false;
	}

	Do ee = (Do)e;
	if (ee.ts.length != ts.length) {
	    ctxt.notDefEq(this,ee);
	    return false;
	}

	for (int i = 0, iend = ts.length; i < iend; i++) 
	    if (!ts[i].defEqNoAnno(ctxt,ee.ts[i],spec))
		return false;
	return t.defEqNoAnno(ctxt,ee.t,spec);
    }

    public Expr evalStep(Context ctxt) {
	Expr[] nts = new Expr[ts.length];
	for (int i = 0, iend = ts.length; i < iend; i++) {
	    nts[i] = ts[i].evalStep(ctxt);
	    if (nts[i] != ts[i]) {
		for (int j = i+1; j < iend; j++)
		    nts[j] = ts[j];
		return new Do(nts,t);
	    }
	}

	// all the void subterms are in normal form.

	return t.evalStep(ctxt);
    }

    public guru.carraway.Expr toCarraway(Context ctxt) {
	guru.carraway.Do D = new guru.carraway.Do();
	D.pos = pos;
	int tslen = ts.length;
	D.ts = new guru.carraway.Expr[tslen+1];
	int i = 0;
	for (; i < tslen; i++)
	    D.ts[i] = ts[i].toCarraway(ctxt);
	D.ts[i] = t.toCarraway(ctxt);
	
	return D;
    }
}
