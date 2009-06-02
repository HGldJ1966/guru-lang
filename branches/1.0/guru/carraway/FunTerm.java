package guru.carraway;

import guru.Position;
import java.util.Collection;
import java.util.Iterator;

public class FunTerm extends FunBase {
    public Sym f;
    public Expr body;

    public FunTerm(){
	super(FUN_TERM);
    }

    public FunTerm(String exact_name, Expr body, Position p){
	super(FUN_TERM,p);
	f = new Sym(exact_name, exact_name);
	this.body = body;
    }

    public void do_print(java.io.PrintStream w, Context ctxt) {
	if (ctxt.stage <= 2) {
	    f.print(w,ctxt);
	    super.do_print(w,ctxt);
	    w.println(" :=");
	    w.print("  ");
	    body.print(w,ctxt);
	}
	else {
	    rettype.print(w,ctxt);
	    w.print(" ");
	    f.print(w,ctxt);
	    super.do_print(w,ctxt);
	    w.println(" {");
	    body.print(w,ctxt);
	    if (body.construct != DO && body.construct != MATCH)
		w.println(";");
	    w.println("}\n");
	}   
    }    

    public Expr simpleType(Context ctxt) {
	checkTypes(ctxt);

	FunType F = new FunType();
	int iend = vars.length;
	F.vars = new Sym[iend];
	F.types = new Expr[iend];
	F.consumps = consumps;

	for (int i = 0; i < iend; i++) {
	    F.types[i] = types[i].applySubst(ctxt);
	    F.vars[i] = ctxt.newSym(vars[i].output_name);
	    ctxt.setSubst(vars[i],F.vars[i]);
	}

	F.rettype = rettype.applySubst(ctxt);

	for (int i = 0; i < iend; i++) 
	    ctxt.setSubst(vars[i],null);

	ctxt.setType(f,F);

	Expr bT = body.simpleType(ctxt);
	if (!bT.eqType(ctxt, rettype))
	    classifyError(ctxt,"The expected and computed return types of a function do not match.\n\n"
			  +"1. the expected return type: "+rettype.toString(ctxt)
			  +"\n\n2. the computed return type: "+bT.toString(ctxt));

	return F;
    }

    public Sym simulate_h(Context ctxt, Position p) {
	ctxt.checkpointRefs();

	Sym[] prev = new Sym[vars.length];
	for (int i = 0, iend = vars.length; i < iend; i++) {
	    Expr T = types[i];
	    if (T.consumable()) {
		Sym r = ctxt.newRef(vars[i].pos,
				    (consumps[i] == NOT_CONSUMED || consumps[i] == CONSUMED_NO_RET),
				    (consumps[i] == CONSUMED_NO_RET || consumps[i] == CONSUMED_RET_OK));
		prev[i] = ctxt.getSubst(vars[i]);
		ctxt.setSubst(vars[i],r);
		if (T.construct == PIN)
		    ctxt.pin(r,((Pin)T).pinned);
	    }
	}

	Sym r = body.simulate(ctxt,pos);

	Context.RefStat u = null;
	if (r != null)
	    u = ctxt.refStatus(r);

	Collection c = ctxt.restoreRefs();

	for (int i = 0, iend = vars.length; i < iend; i++) 
	    if (prev[i] != null)
		ctxt.setSubst(vars[i],prev[i]);

	if (r == null) 
	    return null;
	    
	if (u != null && u.non_ret)
	    simulateError(ctxt,"An input designated as not to be returned is being returned.\n\n"
			  +"1. the corresponding reference was created at: "+r.posToString());
	
	if (ctxt.getFlag("debug_simulate")) {
	    ctxt.w.println("Dropping pre-existing references dropped in the body of a function:");
	    ctxt.w.flush();
	}
	Iterator it = c.iterator();
	while(it.hasNext()) {
	    u = (Context.RefStat)it.next();
		
	    if (u.created) {
		if (u.ref == r) 
		    continue;
		if (u.non_ret)
		    // the only place this could have been introduced is for an input variable for this function
		    continue;
		simulateError(ctxt,"A function is leaking a reference.\n\n"
			      +"1. the function: "+f.toString(ctxt)
			      +("\n\n1. the reference "+(ctxt.getFlag("debug_refs") ? r.toString(ctxt) + ", " : "is ")
				+"created at: "+r.posToString()));
	    }
	    else {
		// drop the reference from the context as it will exist after processing this function.
		if (ctxt.refStatus(u.ref) != null) 
		    ctxt.dropRef(u.ref, pos);
	    }
	}
	return ctxt.voidref;
    }

    public Expr linearize(Context ctxt, guru.Position p, Sym dest) {
	for (int i = 0, iend = types.length; i < iend; i++)
	    types[i] = types[i].flattenType(ctxt);
	rettype = rettype.flattenType(ctxt);
	body = body.linearize(ctxt,p,ctxt.returnf);
	return this;
    }
}