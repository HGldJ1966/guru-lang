package guru;

import java.util.*;
import java.io.*;

// a common parent class for FunTerm and FunType, 
public class FunAbstraction extends Abstraction {

    /* ownership annotations for the input variables */
    public Ownership[] owned;

    public static final int NOT_CONSUMED = guru.carraway.FunBase.NOT_CONSUMED;
    public static final int CONSUMED_RET_OK = guru.carraway.FunBase.CONSUMED_RET_OK;
    public static final int CONSUMED_NO_RET = guru.carraway.FunBase.CONSUMED_NO_RET;

    public int[] consumps; // values given above

    public Ownership ret_stat; /* ownership annotation for return value */

    public FunAbstraction(int construct) {
	super(construct);
    }
    
    public FunAbstraction(int construct, Var[] vars, Expr[] types, 
			  Ownership[] owned, int consumps[], Ownership ret_stat, Expr body) {
	super(construct, vars, types, body);
	this.owned = owned;
	this.consumps = consumps;
	this.ret_stat = ret_stat;
    }

    public FunAbstraction(int construct, Ownership[] owned, int consumps[], Ownership ret_stat,
			  Abstraction a) {
	super(construct, a.vars, a.types, a.body);
	this.owned = owned;
	this.consumps = consumps;
	this.ret_stat = ret_stat;
    }
    
    public FunAbstraction(int construct, Var v, Expr e, Ownership owned, int consump,
			  Ownership ret_stat, Expr body) {
	super(construct, v, e, body);
	this.owned = new Ownership[1];
	this.owned[0] = owned;
	this.consumps = new int[1];
	this.consumps[0] = consump;
	this.ret_stat = ret_stat;
    }

    public void setClassifiers(Context ctxt) {
	super.setClassifiers(ctxt);
    }

    public boolean checkClassifiers(Context ctxt, int approx, boolean spec) {
        boolean did_set = super.checkClassifiers(ctxt,approx,spec);
        if (!did_set)
            // we did not set any classifiers, so no need to check ownership.
            return false;

        for (int i = 0, iend = vars.length; i < iend; i++) {
            Expr T = ctxt.getClassifier(vars[i]);
            if (!T.isTrackedType(ctxt) && owned[i].mustTrack()) {
		handleError(ctxt, 
			    "An argument is marked as having "
			    +"some ownership status\nother than "
			    +"the default or spec, but the argument is "
			    +"not tracked.\n"
			    +"1. the argument: "
			    +vars[i].toString(ctxt)+"\n"
			    +"2. its type: "+types[i].toString(ctxt)+"\n"
			    +"3. its ownership status: "
			    +owned[i].toString(ctxt));
	    }
	}
	return true;
    }

    public boolean defEqNoAnno(Context ctxt, Expr ee, boolean approx,
			       boolean spec) {
	if (!super.defEqNoAnno(ctxt,ee,approx,spec))
	    return false;


	FunAbstraction f1 = (FunAbstraction)coalesce(ctxt, spec);

	FunAbstraction f2 = (FunAbstraction)ee.defExpandTop(ctxt,true,spec);
	f2 = (FunAbstraction)f2.coalesce(ctxt, spec);

	if (spec)
	    return true;

	for (int i = 0, iend = f1.vars.length; i < iend; i++) 
	    if (f1.owned[i].status != f2.owned[i].status ||
		f1.consumps[i] != f2.consumps[i]) {
		ctxt.notDefEq(f1,f2);
		return false;
	    }
	return true;
    }

    public Abstraction coalesce(Context ctxt, boolean spec) {
	Abstraction a = (Abstraction)super.coalesce(ctxt, spec);
	ArrayList v = new ArrayList();
	ArrayList v2 = new ArrayList();
	FunAbstraction cur = this;
	while (true) {
	    for (int i = 0, iend = cur.owned.length; i < iend; i++) {
		v.add(cur.owned[i]);
		v2.add(new Integer(cur.consumps[i]));
	    }
	    if (cur.body.construct != construct)
		break; // out of while
	    cur = (FunAbstraction)cur.body;
	}

	Ownership[] nowned = Parser.toOwnershipArray(v);
	int[] nconsumps = Parser.toIntArray(v2);

	if (nowned.length != a.vars.length)
	    handleError(ctxt,"Internal error: FunAbstraction misbuilt."
			+"\n1. original FunAbstraction: "+toString(ctxt)
			+"\n2. Abstraction: "+a.toString(ctxt));

	return new FunAbstraction(construct, nowned, nconsumps, cur.ret_stat, a);
    }

    public void print_varlist(java.io.PrintStream w, Context ctxt) {
	int iend = vars.length;
	for (int i = 0; i < iend; i++) {
	    w.print("(");
	    switch (consumps[i]) {
	    case CONSUMED_RET_OK:
		break;
		
	    case CONSUMED_NO_RET:
		w.print("^ ");
		break;

	    case NOT_CONSUMED:
		w.print("! ");
		break;
	    }
		
	    if (owned[i].status != Ownership.DEFAULT)
		w.print(owned[i].toString(ctxt)+" ");
	    vars[i].print(w, ctxt);
	    
	    if (types[i].construct != BANG){
		w.print(" : ");
		types[i].print(w, ctxt);
	    }
	    w.print(")");
	}
    }

    // return the result of substituting the given expr for
    // the first var in this abstraction.
    public Expr instantiate(Expr e) {
	Expr ret = super.instantiate(e);
	if (ret.construct == ABSTRACTION) {
	    int iend = owned.length - 1;
	    Ownership[] owned2 = new Ownership[iend];
	    int[] consumps2 = new int[iend];
	    for (int i = 0; i < iend; i++) {
		owned2[i] = owned[i+1];
		consumps2[i] = consumps[i+1];
	    }
	    return new FunAbstraction(ABSTRACTION, owned2, consumps2, ret_stat,
				      (Abstraction)ret);
	}
	return ret;
    }

    protected Expr next() {
	Expr e = super.next();
	if (e.construct == ABSTRACTION) {
	    int iend = vars.length - 1;
	    Ownership[] owned2 = new Ownership[iend];
	    int[] consumps2 = new int[iend];
	    for (int i = 0; i < iend; i++) {
		owned2[i] = owned[i+1];
		consumps2[i] = consumps[i+1];
	    }
	    return new FunAbstraction(ABSTRACTION, owned2, consumps2, ret_stat,
				      (Abstraction)e);
	}
	return e;
    }

    /* drop all non-computational inputs: spec. args and proof args,
       but not type args, since these are actually computational in
       our compiled version. */
    public Expr dropNoncompInputs(Context ctxt) {
	ArrayList vs = new ArrayList();
	ArrayList ts = new ArrayList();
	ArrayList os = new ArrayList();
	ArrayList cs = new ArrayList();
	boolean changed = false;
	for (int i = 0, iend = vars.length; i < iend; i++) {
	    if (vars[i].isProof(ctxt) || owned[i].status == Ownership.SPEC) 
		changed = true;
	    else {
		vs.add(vars[i]);
		ts.add(types[i]);
		os.add(owned[i]);
		cs.add(new Integer(consumps[i]));
	    }
	}
	if (vs.size() == 0)
	    return body;

	if (!changed)
	    return this;
	return new FunAbstraction(ABSTRACTION, Parser.toVarArray(vs),
				  Parser.toExprArray(ts),
				  Parser.toOwnershipArray(os),
				  Parser.toIntArray(cs),
				  ret_stat, body);
    }

    public Expr do_rewrite(Context ctxt, Expr e, Expr x, Stack boundVars) {
	Abstraction a = (Abstraction)super.do_rewrite(ctxt,e,x,boundVars);
	if (a != this)
	    return new FunAbstraction(ABSTRACTION, owned, consumps, ret_stat, a);
	return this;
    }

    public Expr subst(Expr e, Expr x) {
	Abstraction ret = (Abstraction)super.subst(e,x);
	if (ret != this) 
	    return new FunAbstraction(ABSTRACTION,owned,consumps,ret_stat,ret);
	return this;
    }

    public void checkSpec(Context ctxt, boolean in_type, Position p){
	super.checkSpec(ctxt, in_type, pos);
	for (int i = 0; i < vars.length; i++)
	    if (owned[i].status == Ownership.SPEC)
		ctxt.markSpec(vars[i]);
    }

}
