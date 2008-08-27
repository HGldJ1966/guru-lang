package guru;

import java.util.*;

public class Abstraction extends VarListExpr{
    
    public Expr body;
    
    public Abstraction(int construct) {
	super(construct);
    }
    
    public Abstraction(int construct, Var[] vars, Expr[] types, Expr body) {
	super(construct, vars, types);
	this.body = body;
    }
    
    public Abstraction(int construct, Var v, Expr e, Expr body) {
	super(construct);
	this.body = body;
	vars = new Var[1];
	vars[0] = v;
	types = new Expr[1];
	types[0] = e;
    }

    public void do_print(java.io.PrintStream w, Context ctxt) {
	super.do_print(w,ctxt);
	w.print(" . ");
	body.print(w,ctxt);
    }

    public Abstraction coalesce(Context ctxt, boolean spec)
    {
    	Expr tmp = body; /*.defExpandTop(ctxt,false,spec); */
	if (tmp.construct == construct)
    	{
	    Abstraction tmpA = ((Abstraction) tmp).coalesce(ctxt,spec);
	    Var _vars[] = new Var[vars.length + tmpA.vars.length];
	    System.arraycopy(vars,0,_vars,0,vars.length);
	    System.arraycopy(tmpA.vars,0,_vars,vars.length,tmpA.vars.length); 
	    
	    Expr _types[] = new Expr[types.length + tmpA.types.length];
	    System.arraycopy(types,0,_types,0,types.length);
	    System.arraycopy(tmpA.types,0,_types,types.length,
			     tmpA.types.length);	
	    
	    return new Abstraction(construct, _vars, _types, tmpA.body);
	}
	else return this;
    }
    	
    public int numOcc(Expr e) {
	int n = body.numOcc(e);
	if (!isBound(e))
	    n += super.numOcc(e);
	return n;
    }

    // if this abstraction is (x_1 : A_1) ... (x_n : A_n).body, with n > 1,
    // return (x_2:A_2) ... (x_n:A_n).body, with construct ABSTRACTION
    // (several functions elsewhere depend on the returned Expr having
    // this construct).
    // 
    // If n = 1, return just body.  We assume n > 0.
    protected Expr next() {
	int iend = vars.length;
	if (iend == 1)
	    return body;
	iend--;
	Var[] varsp = new Var[iend];
	Expr[] typesp = new Expr[iend];
	for (int i = 0; i < iend; i++) {
	    varsp[i] = vars[i+1];
	    typesp[i] = types[i+1];
	}
	return new Abstraction(ABSTRACTION, varsp, typesp, body);
    }

    // We assume n > 0.
    public Expr instantiate(Expr e) {
	return next().subst(e,vars[0]);
    }

    public Expr subst(Expr e, Expr x) {
	VarListExpr vl = (VarListExpr)super.subst(e,x);
	boolean bound = false;
	for (int i = 0, iend = vl.vars.length; i < iend; i++)
	    if (x == vars[i])
		bound = true;
	Expr nb = bound ? body : body.subst(e,x);
	if (vl != this || nb != body)
	    return new Abstraction(ABSTRACTION, vl.vars, vl.types, nb);
	return this;
    }
    
    public Expr do_rewrite(Context ctxt, Expr e, Expr x, Stack boundVars) {
    	
    	for(int i = 0; i < vars.length; ++i)
    	{
    		boundVars.push(vars[i]);
    	}
    	Expr nBody = body.rewrite(ctxt, e, x, boundVars);
    	for(int i = 0; i < vars.length; ++i)
    	{
    		boundVars.pop();
    	}
    	return new Abstraction(construct, vars, types, nBody);
    }

    public Expr dropAnnos(Context ctxt) {
	VarListExpr vl = (VarListExpr)super.dropAnnos(ctxt);
	Expr b = body.dropAnnos(ctxt);
	if (vl != this || b != body)
	    return new Abstraction(ABSTRACTION, vl.vars, vl.types, b);
	return this;
    }

    // overridden just in FunTerm.
    protected boolean defEqNoAnno_check_arg_types() {
	return true;
    }

    public boolean defEqNoAnno(Context ctxt, Expr ee, boolean approx,
			       boolean spec) {

	ee = ee.defExpandTop(ctxt,true,spec);

	Abstraction e = null; // we assume iend > 0, so e does get assigned

	
	if (ctxt.getFlag("debug_def_eq")) {
	    ctxt.w.println("Abstraction testing def. eq. of: ");
	    ctxt.w.print("1. ");
	    print(ctxt.w,ctxt);
	    ctxt.w.println("");
	    ctxt.w.print("2. ");
	    ee.print(ctxt.w,ctxt);
	    ctxt.w.println(" {");
	    ctxt.w.flush();
	}

	// chew through e using e.next()
	for (int i = 0, iend = vars.length; i < iend; i++) {
	    if (ee.construct != construct && ee.construct != ABSTRACTION) {
		ctxt.notDefEq(this,ee);
		return false;
	    }
	    e = (Abstraction)ee;
	    Var v1 = vars[i], v2 = e.vars[0];
	    if (defEqNoAnno_check_arg_types())
		if (approx) {
		    if (!types[i].defEqNoAnnoApprox(ctxt, e.types[0], spec)) 
			return false;
		}
		else {
		    if (!types[i].defEqNoAnno(ctxt, e.types[0], spec)) 
			return false;
		}
	    
	    ee = e.next().subst(v1,v2);
	}
	
	// e is now just the substituted body of the original e.
	boolean ret = (approx 
		       ? body.defEqNoAnnoApprox(ctxt, ee, spec)
		       : body.defEqNoAnno(ctxt, ee, spec));
	if (ctxt.getFlag("debug_def_eq")) {
	    ctxt.w.println("} " + (new Boolean(ret)).toString());
	    ctxt.w.flush();
	}
	return ret;
    }

    public boolean defEqNoAnno(Context ctxt, Expr ee, boolean spec) {
	return defEqNoAnno(ctxt,ee,false,spec);
    }

    protected boolean defEqNoAnnoApprox(Context ctxt, Expr e,boolean spec) {
	return defEqNoAnno(ctxt,e,true,spec);
    }

    public isInstC isInstance(Context ctxt, Expr ee) {
	ee = ee.defExpandTop(ctxt);

	Abstraction e = null; // we assume iend > 0, so e does get assigned

	isInstC q, found = null;
	// chew through e using e.next()
	for (int i = 0, iend = vars.length; i < iend; i++) {
	    if (ee.construct != construct && ee.construct != ABSTRACTION)
		return new isInstC();
	    e = (Abstraction)ee;
	    q = types[i].isInstance(ctxt, e.types[0]);
	    if (!q.is)
		return q;
	    if (q.val != null)
		found = q;
	    Var v1 = vars[i], v2 = e.vars[0];
	    ee = e.next().subst(v1,v2);
	}
	q = body.isInstance(ctxt, ee);
	if (!q.is)
	    return q;
	if (q.val != null)
	    found = q;

	if (found == null)
	    return new isInstC(true);

	return found;
    }

    public void getFreeVarsComputational(Context ctxt, java.util.Collection v){
	body.getFreeVarsComputational(ctxt,v);

	for (int i = 0; i < vars.length; i++)
	    v.remove(vars[i]);
    }

    public java.util.Set getDependences() {
        java.util.Set s = super.getDependences();
        s.addAll(body.getDependences());
        return s;
    }

    public void checkSpec(Context ctxt, boolean in_type){
	for (int i = 0; i < vars.length; i++)
	    types[i].checkSpec(ctxt, in_type);
	body.checkSpec(ctxt, in_type);
    }

}
