package guru;

import java.util.*;
import java.io.*;

public class FunTerm extends FunAbstraction {
    public Var r; // for recursive calls, might be null
    public Expr T; /* for return type if r is non-null; definitely non-null
		      after classification */
    
    public FunTerm() {
	super(FUN_TERM);
    }
    
    public FunTerm(Var r, Expr T, FunAbstraction a) {
	super(FUN_TERM, a.owned, a.consumps, a.ret_stat, a);
	this.r = r;
	this.T = T;
    }

    public FunTerm(Var r, Expr T, Var x, Expr type, 
		   Ownership owned, int consump, Ownership ret_stat, Expr body) {
	super(FUN_TERM, x, type, owned, consump, ret_stat, body);
	this.r = r;
	this.T = T;
    }

    public FunTerm(Var r, Expr T, Var[] vars, Expr[] types, Ownership owned[],
		   int consumps[], Ownership ret_stat, Expr body) {
	super(FUN_TERM, vars, types, owned, consumps, ret_stat, body);
	this.r = r;
	this.T = T;
    }

    public int hashCode_h(Context ctxt) {
	ctxt.setVarHashCode(r);
	for (int i = 0, iend = vars.length; i < iend; i++)
	    ctxt.setVarHashCode(vars[i]);
	return body.hashCode_h(ctxt);
    }

    public boolean defEqNoAnno(Context ctxt, Expr ee, boolean spec) {
	Expr orig_ee = ee;
	ee = ee.defExpandTop(ctxt,true,spec);

	if (ee.construct != construct)
	    return super.defEqNoAnno(ctxt, ee, spec);

	FunTerm ft = (FunTerm) ee;

	if (ft.r == r || ft.r == null || r == null) {
	    return super.defEqNoAnno(ctxt, ee, spec);
	} else {
	    FunAbstraction nA = (FunAbstraction)super.subst(ft.r, r);
	    return ft.defEqNoAnno(ctxt, new FunTerm(ft.r, T, nA), spec);
	}
    }

    protected boolean defEqNoAnno_check_arg_types() {
	return false; /* we do not need to check equality of arg types
			 for a fun-term. */
    }

    public void do_print(java.io.PrintStream w, 
			 Context ctxt) {
	w.print("fun");
	if (r != null) {
	    w.print(" ");
	    r.print(w,ctxt);
	}
	print_varlist(w, ctxt);
	if (T != null) {
	    w.print(" : ");
	    if (ret_stat.status != Ownership.DEFAULT)
		w.print(ret_stat.toString(ctxt));
	    w.print(" ");
	    T.print(w,ctxt);
	}
	w.print(". ");
	body.print(w,ctxt);
    }

    public Expr subst(Expr e, Expr x) {
	if (x == r)
	    return this;
	FunAbstraction nA = (FunAbstraction)super.subst(e,x);
	Expr nT = (T == null ? null : T.subst(e,x));
	if (nA != this || nT != T)
	    return new FunTerm(r, nT, nA);
	return this;
    }
    
    public Abstraction coalesce(Context ctxt, boolean spec) {
	FunAbstraction a = (FunAbstraction)super.coalesce(ctxt, spec);
	FunTerm cur = this;
	while (true) {
	    if (cur.body.construct != construct)
		break;
	    cur = (FunTerm)cur.body;
	}
	return new FunTerm(r,cur.T,a);
    }

    public Expr do_rewrite(Context ctxt, Expr e, Expr x, Stack boundVars) {
	if (x == r)
	    return this;
	FunAbstraction nA = (FunAbstraction)super.do_rewrite(ctxt,e,x,boundVars);
	if (nA != this)
	    return new FunTerm(r, T, nA);
	return this;
    }

    public Expr dropAnnos(Context ctxt) {
	return dropAnnosInternal(ctxt,false);
    }

    // do not drop spec arguments from the inputs
    public Expr dropAnnosSpecial(Context ctxt) {
	return dropAnnosInternal(ctxt,true);
    }

    public Expr dropNoncompInputs(Context ctxt) {
	Expr ret = super.dropNoncompInputs(ctxt);
	if (ret == this || (ret.construct != ABSTRACTION))
	    return ret;
	ret = new FunTerm(r,T,(FunAbstraction)ret);
	ret.pos = pos;
	return ret;
    }

    protected Expr dropAnnosInternal(Context ctxt, boolean type_fam_abbrev) {
	Expr e= super.dropAnnos(ctxt);
		
	Abstraction f = (Abstraction)e;
	
	int iend = f.types.length;
	boolean changed = false;

	Expr[] ntypes;
	Var[] nvars;
	Ownership[] nowned;
	int[] nconsumps;
	if (type_fam_abbrev) {
	    ntypes = f.types;
	    nvars = f.vars;
	    nowned = owned;
	    nconsumps = consumps;
	}
	else {

	    int cnt = 0;
	    Expr[] types2 = new Expr[iend];
	    Var[] vars2 = new Var[iend];
	    Ownership[] owned2 = new Ownership[iend];
	    int consumps2[] = new int[iend];
	    
	    for (int i = 0; i < iend; i++) {
		if (f.vars[i].isTypeOrKind(ctxt) || f.vars[i].isProof(ctxt)
		    || (owned[i].status == Ownership.SPEC)) {
		    changed = true;
		}
		else{
		    if (f.types[i].construct != Expr.BANG)
			changed = true;
		    types2[cnt] = new Bang();
		    vars2[cnt] = f.vars[i];
		    owned2[cnt] = owned[i];
		    consumps2[cnt] = consumps[i];
		    cnt++;
		}
	    }
	    
	    
	    ntypes = new Expr[cnt];
	    nvars = new Var[cnt];
	    nowned = new Ownership[cnt];
	    nconsumps = new int[cnt];
	    
	    System.arraycopy(types2,0,ntypes,0,cnt);
	    System.arraycopy(vars2,0,nvars,0,cnt);
	    System.arraycopy(owned2,0,nowned,0, cnt);
	    System.arraycopy(consumps2,0,nconsumps,0, cnt);
	    
	    if (cnt == 0)
		return f.body;
	}
	
	if (f != this || changed || (T != null && T.construct != Expr.BANG))
	    return new FunTerm(r, new Bang(), nvars, ntypes, nowned, nconsumps,
			       ret_stat, f.body);
	
	return this;
    }


    // return the result of substituting the given expr for
    // the first var in this abstraction.
    public Expr instantiate(Expr e) {

	Expr ret = super.instantiate(e).subst(this,r);
	if (ret.construct == ABSTRACTION) 
	    return new FunTerm(null, null, (FunAbstraction)ret);
	return ret;
    }

    public void setClassifiers(Context ctxt) {
	super.setClassifiers(ctxt);
	if (r != null) {
	    Expr T1 = new FunType(vars, types, owned, consumps, ret_stat, T);
	    if (!T.isTrackedType(ctxt) && ret_stat.mustTrack())
		handleError(ctxt,"The return type for a recursive function is labeled for tracking,\n"
			    +"but its type is one we do not track.\n\n"
			    +"1. the return type: "+T.toString(ctxt)
			    +"\n\n2. its ownership status: "+ret_stat.toString(ctxt));
	    ctxt.setClassifier(r, T1);
	}
    }

    public Expr classify(Context ctxt, int approx, boolean spec) {
		
	checkClassifiers(ctxt, approx, spec);
	if (r != null) {
	    if (T == null)
		handleError(ctxt, "A recursive fun-term is missing its return type.\n"
			    +"1. the recursive function: "+r.toString(ctxt));
     

	    Expr T1 = new FunType(vars, types, owned, consumps, ret_stat, T);
	    T1.classify(ctxt, approx, spec); /* needed to set up spec 
						annotations in term apps
						in T1 */
	    if (ctxt.getClassifier(r) == null)
		ctxt.setClassifier(r, T1);
	}

	Expr bT = body.classify(ctxt, approx, spec);

	if (T == null)
	    T = bT;
	else if (!bT.defEq(ctxt, T, approx, spec))
	    handleError(ctxt,
			"The declared return type of a recursive fun-term"
			+" is not definitionally equal\nto the type"
			+" computed for the body of the fun-term.\n"
			+"1. The declared return type: "
			+T.toString(ctxt)+"\n"
			+"2. The type of the body: "+bT.toString(ctxt));

	if (!T.isTrackedType(ctxt) && ret_stat.mustTrack()) {// cf. FunAbstraction.checkClassifiers
	    handleError(ctxt, 
			"The declared type for a fun-term is "
			+"not a tracked type,\nbut the fun-term is marking"
			+" it as having some ownership\nstatus other than "
			+"the default.\n"
			+"1. the return type: "
			+T.toString(ctxt)+"\n"
			+"2. its ownership status: "
			+ret_stat.toString(ctxt));
	}

	return new FunType(vars, types, owned, consumps, ret_stat, T);
    }

    public void getFreeVarsComputational(Context ctxt, java.util.Collection v){
	super.getFreeVarsComputational(ctxt,v);

	if (r != null)
	    v.remove(r);
    }

    public void checkTermination(Context ctxt) {
	for (int i = 0, iend = vars.length; i < iend; i++) {
	    if (owned[i].status == Ownership.SPEC || 
		vars[i].isTypeOrKind(ctxt) ||
		types[i].isFormula(ctxt))
		continue;
	    /* we have reached a non-spec argument.  The fun-term will
	       definitely not turn into a non-fun-term when we drop
	       annotations. */
	    return;
	}
	body.checkTermination(ctxt);
    }

    public java.util.Set getDependences() {
        java.util.Set s = super.getDependences();
	if (T == null)
	    return s;
	
        s.addAll(T.getDependences());
        return s;
    }

    public void checkSpec(Context ctxt, boolean in_type, Position p){
	for (int i = 0; i < vars.length; i++){
	    if (owned[i].status == Ownership.SPEC)
		ctxt.markSpec(vars[i]);
	    //types[i].checkSpec(ctxt, in_type);
	}
	
	body.checkSpec(ctxt, in_type, pos);
    }

    // we assume r is non-null (Compile sets it if it is null).
    public guru.carraway.Expr toCarraway(Context ctxt) {
	guru.carraway.FunTerm F = new guru.carraway.FunTerm();
	F.pos = pos;

	guru.carraway.Context cctxt = ctxt.carraway_ctxt;
	F.f = cctxt.newSym(r.name,r.pos, true);
	cctxt.declareFunction(F.f);

	int iend = vars.length;
	guru.carraway.Sym[] nvars = new guru.carraway.Sym[iend];
	guru.carraway.Expr[] ntypes = new guru.carraway.Expr[iend];
	int[] nconsumps = new int[iend];
	for (int i = 0; i < iend; i++) {
	    if (types[i].construct == TYPE || types[i].construct == FUN_TYPE)
		ntypes[i] = types[i].toCarrawayType(ctxt,false);
	    else if (!types[i].isTrackedType(ctxt))
		ntypes[i] = new guru.carraway.Untracked();
	    else
		ntypes[i] = owned[i].toCarrawayType(ctxt,vars[i].pos);
	    nvars[i] = cctxt.newSym(vars[i].name,vars[i].pos,false);
	    cctxt.pushVar(nvars[i]);
	    nconsumps[i] = consumps[i];
	}
	    
	if (T == null) 
	    handleError(ctxt,"We are trying to compile a fun-term whose return type has not been computed.\n"
			+"Probably this is a trusted definition: try compiling with it not trusted, or \n"
			+"explicitly add the return type.");
	if (T.construct == VOID || T.construct == FUN_TYPE)
	    F.rettype = T.toCarrawayType(ctxt,true);
	else if (!T.isTrackedType(ctxt))
	    F.rettype = new guru.carraway.Untracked();
	/* else if (ret_stat.construct == Ownership.ABORT) 
	    F.rettype = new guru.carraway.Abort(); */
	else
	    F.rettype = ret_stat.toCarrawayType(ctxt,T.pos);
	F.consumps = nconsumps;
	F.types = ntypes;
	F.vars = nvars;
	F.body = body.toCarraway(ctxt);

	for (int i = 0; i < iend; i++) 
	    cctxt.popVar(nvars[i]);

	return F;
    }

    // this could only happen if this FunTerm defines a type family abbreviation.
    public guru.carraway.Expr toCarrawayType(Context ctxt, boolean dtype) {
	return body.toCarrawayType(ctxt,dtype);
    }

}

