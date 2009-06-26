package guru;

import java.util.Stack;
import java.util.ArrayList;

public class FunType extends FunAbstraction {
    
    public FunType() {
	super(FUN_TYPE);
    }
    
    public FunType(FunAbstraction a) {
	super(FUN_TYPE, a.owned, a.consumps, a.ret_stat, a);
    }

    public FunType(Var[] vars, Expr[] types, Ownership[] owned, 
		   int[] consumps, Ownership ret_stat, Expr body) {
	super(FUN_TYPE, vars, types, owned, consumps, ret_stat, body);
    }

    public FunType(Var var, Expr type, Ownership owned, int consump,
		   Ownership ret_stat, Expr body) {
	super(FUN_TYPE, var, type, owned, consump, ret_stat, body);
    }

    public int getArity() {
	int i = 0;
	Expr tmp = this;
	do {
	    i++;
	    tmp = ((Abstraction)tmp).next();
	}
	while (tmp.construct == ABSTRACTION || tmp.construct == FUN_TYPE);
	return i;
    }

    public void do_print(java.io.PrintStream w, Context ctxt) {
	w.print("Fun");
	print_varlist(w, ctxt);
	w.print(". ");
	
	if (ret_stat.status != Ownership.DEFAULT) {
	    w.print(ret_stat.toString(ctxt));
	    w.print(" ");
	}
	body.print(w,ctxt);
    }


    public Abstraction coalesce(Context ctxt, boolean spec) {
	FunAbstraction a = (FunAbstraction)super.coalesce(ctxt, spec);
	return new FunType(a);
    }

    public Expr subst(Expr e, Expr x) {
	FunAbstraction nA = (FunAbstraction)super.subst(e,x);
	if (nA != this)
	    return new FunType(nA);
	return this;
    }
    
    public Expr do_rewrite(Context ctxt, Expr e, Expr x, Stack boundVars) {
    	return this;
    }

    public Expr instantiate(Expr e) {
	Expr ret = super.instantiate(e);
	if (ret.construct == ABSTRACTION)
	    return new FunType((FunAbstraction)ret);
	return ret;
    }

    public Expr next() {
	Expr ret = super.next();
	if (ret.construct == ABSTRACTION)
	    return new FunType((FunAbstraction)ret);
	return ret;
    }

    public Expr dropAnnos(Context ctxt) {
	Abstraction a = (Abstraction) super.dropAnnos(ctxt);

	if (a != this)
	    return new FunType(a.vars, a.types, owned, consumps, ret_stat, a.body);

	return this;
    }

    public Expr dropNoncompInputs(Context ctxt) {
	Expr ret = super.dropNoncompInputs(ctxt);
	if (ret == this || (ret.construct != ABSTRACTION))
	    return ret;
	ret = new FunType((FunAbstraction)ret);
	ret.pos = pos;
	return ret;
    }

    public Expr classify(Context ctxt, int approx, boolean spec) {
	boolean did_set = checkClassifiers(ctxt, approx, spec);
	Expr c = body.classify(ctxt, approx, spec);

	// cf. FunAbstraction.checkClassifiers()
	if (did_set && !body.isTrackedType(ctxt)) {
	    if (ret_stat.mustTrack())
		handleError(ctxt, 
			    "The return type of a Fun-type is marked as "
			    +"having some ownership\nstatus other than "
			    +"the default, but the argument is not "
			    +"tracked.\n"
			    +"1. the return type: "
			    +body.toString(ctxt)+"\n"
			    +"2. its ownership status: "
			    +ret_stat.toString());
	}

	if (c.construct == TYPE || c.construct == TKIND 
	    || c.construct == FKIND)
	    return c;

	handleError(ctxt,
		    "The body of a Fun-type is not a type or kind.\n"+
		    "Its classifier is: "+c.toString(ctxt));
	return null;
    }
    
    public guru.carraway.Expr toCarrawayType(Context ctxt, boolean dtype) {
	guru.carraway.Context cctxt = ctxt.carraway_ctxt;
	guru.carraway.FunType F = new guru.carraway.FunType();
	F.pos = pos;
	int iend = vars.length;
	ArrayList vl = new ArrayList();
	ArrayList cl = new ArrayList();
	ArrayList tl = new ArrayList();
	int cur = 0;
	for (int i = 0; i < iend; i++) {
	    if (owned[i].status == Ownership.SPEC)
		continue;
	    guru.carraway.Sym v = cctxt.newSym(vars[i].name,vars[i].pos);
	    vl.add(v);
	    cctxt.pushVar(v);
	    Expr tp = types[i].defExpandTop(ctxt,false,false);

	    // if we are computing the corresponding Carraway datatype (as opposed
	    // to resource type), then we are supposed to use the datatype for this
	    // argument iff its resource type requires that we do.

	    guru.carraway.Expr resource_tp = owned[i].toCarrawayType(ctxt,types[i].pos);
	    if (tp.construct == TYPE)
		tl.add(new guru.carraway.Type());
	    else if (dtype) {
		if (resource_tp.need_datatype_for_ctor_arg_resource_type())
		    tl.add(tp.toCarrawayType(ctxt,true));
		else
		    tl.add(new guru.carraway.Untracked());
	    }
	    else
		tl.add(resource_tp);

	    cl.add(new Integer(consumps[i]));
	    cur++;
	}

	F.vars = guru.carraway.Parser.toSymArray(vl);
	F.consumps = Parser.toIntArray(cl);
	F.types = guru.carraway.Parser.toExprArray(tl);
	Expr tp = body.defExpandTop(ctxt,false,false);
	if (ret_stat.status == Ownership.DEFAULT && 
	    (tp.construct == FUN_TYPE || tp.construct == VOID || tp.construct == TYPE))
	    F.rettype = body.toCarrawayType(ctxt,dtype);
	else
	    F.rettype = ret_stat.toCarrawayType(ctxt, pos);
	
	for (int j = 0, jend = F.vars.length; j < jend; j++)
	    cctxt.popVar(F.vars[j]);

	return F;
    }
}
