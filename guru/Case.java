package guru;

import java.util.*;
import java.io.*;


public class Case extends Expr{
    
    public Const c;
    public Var[] x;
    public Expr body;

    public boolean impossible;

    public Case() {
	super(CASE);
    }
    
    public Case(Const c, Var[] x, Expr body, boolean impossible) {
	super(CASE);
	this.c = c;
	this.x = x;
	this.body = body;
	this.impossible = impossible;
    }

    public void print_pattern_var_types_if(java.io.PrintStream w, 
					   Context ctxt) {
	if (ctxt.getFlag("print_pattern_var_types")) {
	    w.print(" %- ");
	    for (int i = 0, iend = x.length; i < iend; i++) {
		Expr T = ctxt.getClassifier(x[i]);
		if (T == null)
		    break;
		if (i > 0)
		    w.print(", ");
		x[i].print(w,ctxt);
		w.print(" : ");
		T.print(w,ctxt);
	    }
	    w.print(" -% ");
	}
    }

    public void do_print(java.io.PrintStream w, Context ctxt) {
	c.print(w,ctxt);
	int iend = x.length;
	for (int i = 0; i < iend; i++) {
	    w.print(" ");
	    x[i].print(w,ctxt);
	}

	print_pattern_var_types_if(w,ctxt);

	w.print(" => ");

	if (impossible)
	    w.print("%- impossible -% ");

	for (int i = 0; i < iend; i++) 
	    ctxt.pushVar(x[i]);
	body.print(w,ctxt);
	for (int i = 0; i < iend; i++) 
	    ctxt.popVar(x[i]);
    }

    public int numOcc(Expr e) {
	int n = c.numOcc(e);
	if (!isBound(e))
	    n += body.numOcc(e);
	return n;
    }
    
    // if ee matches the pattern of this case, then return the
    // body with pattern variables replaced by matching subterms of ee.
    // Otherwise, return null.
    public Expr instantiate(Context ctxt, Expr ee) {
	int iend = x.length;
	if (iend == 0){ 
	    return (c == ee) ? body : null;
	}
	if (ee.construct != TERM_APP) {
	    return null;
	}
	
	TermApp a = (TermApp)((TermApp)ee).spineForm(ctxt,true,true,true);
	
	
	Var [] x2 = new Var[iend];
	int cnt=0;

	//TODD: i changed this so that it only assigns if not spec as well
	for (int i =0; i< iend; i++){
	    if (!x[i].isTypeOrKind(ctxt) && !x[i].isProof(ctxt) && !ctxt.isSpec(x[i])){
		x2[cnt] = x[i]; 
		cnt++;
	    }
	}
	Var [] x3 = new Var[cnt];
	System.arraycopy(x2,0,x3,0,cnt);
	
	//This part was changed to use x3 instead of x
	if (x3.length != a.X.length){
	    return null;
	}
	Expr b = body;

	for (int i = 0; i < x3.length; i++)
	    b = b.subst(a.X[i], x3[i]);
	return b;
    }

    public Case dropNoncompPatternVars(Context ctxt) {
	ArrayList nx = new ArrayList();
	boolean changed = false;
	for (int i = 0, iend = x.length; i < iend; i++) {
	    if (x[i].isProof(ctxt) || ctxt.isSpec(x[i])) 
		changed = true;
	    else 
		nx.add(x[i]);
	}
	if (!changed)
	    return this;
	return new Case(c, Parser.toVarArray(nx), body, impossible);
    }

    public boolean defEqNoAnno(Context ctxt, Expr ee, boolean spec) {
	if (ee.construct != CASE) {
	    ctxt.notDefEq(this,ee);
	    return false;
	}
	Case e = (Case)ee;
	Expr e_body = e.instantiate(ctxt, getPattern());
	if (e_body == null) {
	    ctxt.notDefEq(this,ee);
	    return false;
	}
	return body.defEqNoAnno(ctxt,e_body,spec);
    }

    public boolean isBound(Expr y) {
	for (int i = 0, iend = x.length; i < iend; i++)
	    if (y == x[i])
		return true;
	return false;
    }

    public Expr subst(Expr e, Expr y) {
	if (isBound(y))
	    return this;
	Expr nb = body.subst(e,y);
	if (nb != body)
	    return new Case(c, x, nb, impossible);
	return this;
    }
    public Expr do_rewrite(Context ctxt, Expr e, Expr y, Stack boundVars) {
    for (int i = 0, iend = x.length; i < iend; i++)
    {
    	boundVars.push(x[i]);
    }
	Expr nb = body.rewrite(ctxt,e,y,boundVars);
	for (int i = 0, iend = x.length; i < iend; i++)
    {
    	boundVars.pop();
    }
	if (nb != body)
	    return new Case(c, x, nb, impossible);
	return this;
    }

    public Expr getPattern() {
	if (x.length == 0)
	    return c;
	
	Expr ret = new TermApp(c, varArrayToExprArray(x));
	ret.pos = pos;
	return ret;
    }

    
    /* call during classification (only: otherwise we may
       incorrectly mark variables as specificational) to set
       specificationality of pattern vars. */
    public void setSpecOwnership(Context ctxt) {
	Expr cl = ctxt.getClassifier(c).defExpandTop(ctxt);
	for (int i = 0, iend = x.length; i < iend; i++) {
	    FunType a = (FunType)cl;
	    if (a.owned[0].status == Ownership.SPEC) 
		ctxt.markSpec(x[i]);
	    cl = a.instantiate(x[i]);
	}
    }

    // are all vars (including spec ones) present?
    public boolean allVarsPresent(Context ctxt) {
	Expr cl = ctxt.getClassifier(c).defExpandTop(ctxt);
	if (cl.construct != FUN_TYPE)
	    return true;
	FunType a = (FunType)cl;
	int xlen = x.length;
	return (a.vars.length == xlen);
    }

    /* if always is false, we will set them if they are not already set */
    public void setPatternVarTypes(Context ctxt, boolean always) {
	Expr cl = ctxt.getClassifier(c).defExpandTop(ctxt);
	int xlen = x.length;
	if (xlen == 0)
	    return;
	FunType a = (FunType)cl;
	if (a.vars.length > xlen) {
	    /* this must be an annotation-free term.  We should
	       set the classifiers to ! for benefit of calls
	       to dropAnnos() on them. */
	    Expr bang = new Bang();
	    for (int i = 0; i < xlen; i++) 
		if (always || ctxt.getClassifier(x[i]) == null) 
		    ctxt.setClassifier(x[i], bang);
	}
	else {
	    for (int i = 0, iend = a.vars.length; i < iend; i++) {
		a = (FunType)cl;
		if (always || ctxt.getClassifier(x[i]) == null) 
		    ctxt.setClassifier(x[i], a.types[0]);
		cl = a.instantiate(x[i]);
	    }
	}
    }

    public Expr dropAnnos(Context ctxt) {
	setPatternVarTypes(ctxt, false);
	Expr b = body.dropAnnos(ctxt);

	int xlen = x.length;

	Var [] x3 = x;
	boolean changed = false;
	if (xlen > 0) {
	    FunType f = (FunType)ctxt.getClassifier(c);
	    if (f.vars.length <= xlen) {
		/* if c accepts more args than given, we assume
		   annos have already been dropped */
		Var [] x2 = new Var[xlen];
		int cnt = 0;
		for (int i = 0; i < xlen; i++){
		    if (!x[i].isTypeOrKind(ctxt)
			&& !ctxt.isSpec(x[i])
			&& !x[i].isProof(ctxt)) {
			x2[cnt] = x[i];
			cnt++;
		    }
		    else
			changed = true;
		}
		x3 = new Var[cnt];
		System.arraycopy(x2,0,x3,0,cnt);
	    }
	}

	if (b != body || changed)
	    return new Case(c,x3,b,impossible);
	return this;
    }
    
    public void getFreeVarsComputational(Context ctxt, Collection vars) {
	body.getFreeVarsComputational(ctxt, vars);
	
	for (int j = 0; j < x.length; j++)
	    vars.remove(x[j]);
    }

    public void checkTermination(Context ctxt) {
        body.checkTermination(ctxt);
    }

    public java.util.Set getDependences() {
        return body.getDependences();
    }

    public void markSpec(Context ctxt){
		
	Expr e = ctxt.getClassifier(c);
	
	if (e.construct == Expr.FUN_TYPE) {
	    FunType ft = (FunType) e;

	    for (int i = 0; i < ft.vars.length; i++)
		if (ft.owned[i].status == Ownership.SPEC)
		    ctxt.markSpec(x[i]);
	}
    }

    public void checkSpec(Context ctxt, boolean in_type) {
	
	Expr e = ctxt.getClassifier(c);
	
	if (e.construct == Expr.FUN_TYPE) {
       
	    FunType ft = (FunType) e;

	    for (int i = 0; i < ft.vars.length; i++)
		if (ft.owned[i].status == Ownership.SPEC)
		    ctxt.markSpec(x[i]);
	}

	body.checkSpec(ctxt, in_type);
    }

    public void clearDefs(Context ctxt) {
	for (int j = 0, jend = x.length; j < jend; j++) {
	    if (ctxt.isMacroDefined(x[j]))
		ctxt.macroDefine(x[j],null);
	}
    }

    // return true iff we could refine the pattern's type with the scrutinee's.
    public boolean refine(Context ctxt, Expr scruttp,
			  int approx, boolean spec) {
	Expr pat = getPattern();
	Expr pattp = pat.classify(ctxt,approx,spec);
	
	Vector vars = new Vector();
	for (int j = 0, jend = x.length; j < jend; j++) 
	    vars.add(x[j]);
	

	if (ctxt.getFlag("debug_refine_cases")) {
	    ctxt.w.println("About to refine "
			   +pattp.toString(ctxt)+" with "
			   +scruttp.toString(ctxt));
	    ctxt.w.println("The pattern is: "+pat.toString(ctxt));
	    ctxt.w.flush();
	}

	boolean ret = refine(ctxt, pattp.dropAnnos(ctxt), 
			     scruttp.dropAnnos(ctxt), approx, spec, vars);

	// do not set impossible if it is already true
	if (!impossible)
	    impossible = !ret;

	if (ctxt.getFlag("debug_refine_cases")) {
	    if (ret)
		ctxt.w.println("Successfully refined "
			       +pattp.toString(ctxt)+" with "
			       +scruttp.toString(ctxt));
	    else
		ctxt.w.println("Could not refine "
			       +pattp.toString(ctxt)+" with "
			       +scruttp.toString(ctxt));
	    ctxt.w.flush();
	}

	ctxt.resetNotDefEq();
	
	return ret;
    }


    protected boolean refine(Context ctxt, Expr pattp, Expr scruttp,
			     int approx, boolean spec, Vector vars) {
	if (ctxt.getFlag("debug_refine_cases")) {
	    ctxt.w.println("Refining "+pattp.toString(ctxt)+" with "
			   +scruttp.toString(ctxt));
	    ctxt.w.flush();
	}

	pattp = pattp.defExpandTop(ctxt,true,spec);
	scruttp = scruttp.defExpandTop(ctxt,true,spec);
	if (pattp.construct == VAR) {
	    if (!pattp.defEqNoAnno(ctxt,scruttp,spec)) {
		Var v = (Var)pattp;
		if (vars.contains(v)) {
		    if (ctxt.getFlag("debug_refine_cases")) {
			ctxt.w.println(v.toString(ctxt)+" --> "
				       +scruttp.toString(ctxt));
			ctxt.w.flush();
		    }
		    ctxt.macroDefine(v,scruttp);
		}
	    }
	    return true;
	}
	switch(pattp.construct) {
	case CONST: {
	    if (scruttp.construct == VAR)
		return true;
	    if (scruttp.construct == CONST ||
		scruttp.construct == TYPE_APP)
		return pattp.defEq(ctxt,scruttp,spec);
	    if (scruttp.construct == TERM_APP) {
		TermApp scruttp1 = (TermApp)(((TermApp)scruttp)
					     .spineForm(ctxt,true,spec,true));
		if (scruttp1.head.construct == CONST
		    && ctxt.isTermCtor((Const)scruttp1.head))
		    // different constructors
		    return false;
	    }
	    return true;
	}
	case TYPE_APP: {
	    TypeApp pattp1 = (TypeApp)(((TypeApp)pattp)
				       .spineForm(ctxt,true,spec,true));
	    if (scruttp.construct == CONST)
		return false;

	    if (scruttp.construct != TYPE_APP)
		// must stop refining here
		return true;

	    TypeApp scruttp1 = (TypeApp)(((TypeApp)scruttp)
					 .spineForm(ctxt,true,spec,true));
	    if (!pattp1.head.defEq(ctxt,scruttp1.head,spec))
		return false;
	    
	    for (int i = 0, iend = scruttp1.X.length; i < iend; i++)
		if (!refine(ctxt,pattp1.X[i],scruttp1.X[i], approx, spec,
			    vars))
		    return false;
	    return true;
	}
	case TERM_APP: {
	    TermApp pattp1 = (TermApp)(((TermApp)pattp)
				       .spineForm(ctxt,true,spec,true));
	    if (pattp1.head.construct == CONST 
		&& ctxt.isTermCtor((Const)pattp1.head)
		&& scruttp.construct == CONST)
		// different constructors
		return false;

	    if (scruttp.construct != TERM_APP)
		// must stop refining here
		return true;

	    TermApp scruttp1 = (TermApp)(((TermApp)scruttp)
					 .spineForm(ctxt,true,spec,true));
	    if (!pattp1.head.defEq(ctxt,scruttp1.head,spec))
		return false;
	    
	    for (int i = 0, iend = scruttp1.X.length; i < iend; i++)
		if (!refine(ctxt,pattp1.X[i],scruttp1.X[i], approx, spec,
			    vars))
		    return false;
	    return true;
	}
	default:
	    /* we did not necessarily encounter a problem,
	       we just don't handle this case. */
	    return true;
	}	
    }

    public guru.carraway.Expr toCarraway(Context ctxt) {
	guru.carraway.Case C = new guru.carraway.Case();
	C.pos = pos;
	C.c = (guru.carraway.Sym)c.toCarraway(ctxt);
	int iend = x.length;
	guru.carraway.Sym[] nvars = new guru.carraway.Sym[iend];
	for (int i = 0; i < iend; i++) {
	    nvars[i] = ctxt.carraway_ctxt.newSym(x[i].name,x[i].pos);
	    ctxt.carraway_ctxt.pushVar(nvars[i]);
	}
	C.vars = nvars;
	C.body = body.toCarraway(ctxt);
	for (int i = 0; i < iend; i++) 
	    ctxt.carraway_ctxt.popVar(nvars[i]);
	return C;
    }

}
