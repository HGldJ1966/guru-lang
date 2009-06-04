package guru.carraway;
import guru.Position;

public class Case extends Expr {
    public Sym c;
    public Sym[] vars;
    public Expr body;

    Position lastpos;

    public Case(){
	super(CASE);
    }

    // used during compilation
    public Case(Sym c, Expr body, Position p) {
	super(CASE);
	this.c = c;
	this.body = body;
	this.pos = p;
    }

    public void do_print(java.io.PrintStream w, Context ctxt) {
	if (ctxt.stage <= 2) {
	    c.print(w,ctxt);
	    for(int i = 0, iend = vars.length; i < iend; i++) {
		w.print(" ");
		vars[i].print(w,ctxt);
	    }
	    w.print(" => ");
	    body.print(w,ctxt);
	}
	else {
	    w.print("case op_");
	    c.print(w,ctxt);
	    w.println(": {\n");
	    body.print(w,ctxt);
	    w.print("break;");
	    w.println("} /* case "+c.toString(ctxt)+" */");
	}
    }    

    public Expr simpleType(Context ctxt) {
	classifyError(ctxt,"Internal error: Case.simpleType() is being called directly, instead of from Match.");
	return null;
    }

    // Match will take care of checkpointing the state.
    public Sym simulate_h(Context ctxt, Position p) {
	Sym ret = null;
	if (vars.length == 0) 
	    ret = body.simulate(ctxt,pos);
	else {
	    FunType f = (FunType)ctxt.getType(c);
	    
	    // introduce references for the pattern vars of consumable type
	    
	    Sym[] fprev = new Sym[vars.length];
	    Sym[] prev = new Sym[vars.length];
	    for (int i = 0, iend = vars.length; i < iend; i++) {
		Expr T = f.types[i].applySubst(ctxt);
		fprev[i] = ctxt.getSubst(f.vars[i]);
		prev[i] = ctxt.getSubst(vars[i]);
		if (T.consumable()) {
		    Sym r = ctxt.newRef(vars[i]);
		    ctxt.setSubst(f.vars[i],r); // so substituted pin-types will mention r
		    ctxt.setSubst(vars[i],r);
		    
		    // pin as appropriate

		    if (T.construct == PIN) 
			ctxt.pin(r,((Pin)T).pinned);
		}
	    }
	    ret = body.simulate(ctxt,pos);
	    for (int i = 0, iend = vars.length; i < iend; i++) {
		ctxt.setSubst(f.vars[i],fprev[i]);
		ctxt.setSubst(vars[i],prev[i]);
	    }
	}

	if (ret == null)
	    return null;
	
	if (ret != ctxt.voidref) {
	    Context.RefStat u = ctxt.refStatus(ret);
	    if (u.non_ret)
		simulateError(ctxt,"A match-case is returning a non-returnable reference.\n\n"
			      +"1. the case: "+c.toString(ctxt)
			      +"\n\n2. "+ret.refString(ctxt));
	}
	return ret;
    }
}