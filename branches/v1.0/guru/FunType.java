package guru;

import java.util.Stack;

public class FunType extends FunAbstraction {
    
    public FunType() {
	super(FUN_TYPE);
    }
    
    public FunType(FunAbstraction a) {
	super(FUN_TYPE, a.owned, a.ret_stat, a);
    }

    public FunType(Var[] vars, Expr[] types, Ownership[] owned, 
		   Ownership ret_stat, Expr body) {
	super(FUN_TYPE, vars, types, owned, ret_stat, body);
    }

    public FunType(Var var, Expr type, Ownership owned, 
		   Ownership ret_stat, Expr body) {
	super(FUN_TYPE, var, type, owned, ret_stat, body);
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
	
	if (ret_stat.shouldPrint(ctxt)) {
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
	    return new FunType(a.vars, a.types, owned, ret_stat, a.body);

	return this;
    }

    public Expr dropNoncompInputs(Context ctxt) {
	Expr ret = super.dropNoncompInputs(ctxt);
	if (ret == this || (ret.construct != ABSTRACTION))
	    return ret;
	return new FunType((FunAbstraction)ret);
    }

    public Expr classify(Context ctxt, int approx, boolean spec) {
	boolean did_set = checkClassifiers(ctxt, approx, spec);
	Expr c = body.classify(ctxt, approx, spec);

	// cf. FunAbstraction.checkClassifiers()
	if (did_set && !body.isTrackedType(ctxt)) {
	    if (ret_stat.status != Ownership.NOT_TRACKED
		&& ret_stat.status != Ownership.UNOWNED)
		handleError(ctxt, 
			    "The return type of a Fun-type is marked as "
			    +"having some ownership\nstatus other than "
			    +"the default, but the argument is not "
			    +"tracked.\n"
			    +"1. the return type: "
			    +body.toString(ctxt)+"\n"
			    +"2. its ownership status: "
			    +ret_stat.toString());
	    ret_stat = new Ownership(Ownership.NOT_TRACKED);
	}

	if (c.construct == TYPE || c.construct == TKIND 
	    || c.construct == FKIND)
	    return c;

	handleError(ctxt,
		    "The body of a Fun-type is not a type or kind.\n"+
		    "Its classifier is: "+c.toString(ctxt));
	return null;
    }
}
