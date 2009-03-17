package guru.carraway;
import guru.Position;

public class Case extends Expr {
    public Sym c;
    public Sym[] vars;
    public Expr body;

    public Case(){
	super(CASE);
    }

    public void print(java.io.PrintStream w, Context ctxt) {
	c.print(w,ctxt);
	for(int i = 0, iend = vars.length; i < iend; i++) {
	    w.print(" ");
	    vars[i].print(w,ctxt);
	}
	w.print(" => ");
	body.print(w,ctxt);
    }    

    public Expr simpleType(Context ctxt) {
	classifyError(ctxt,"Internal error: Case.simpleType() is being called directly, instead of from Match.");
	return null;
    }

    // Match will take care of checkpointing the state.
    public Sym simulate(Context ctxt, Position p) {
	if (vars.length == 0)
	    return body.simulate(ctxt,pos);

	FunType f = (FunType)ctxt.getType(c);

	for (int i = 0, iend = vars.length; i < iend; i++) {
	    Expr T = f.types[i].applySubst(ctxt);
	    if (T.consumable()) {
		Sym r = ctxt.newRef(vars[i].pos);
		ctxt.setSubst(vars[i],r);
		if (T.construct == PIN)
		    ctxt.pin(r,((Pin)T).pinned);
	    }
	}
	return body.simulate(ctxt,pos);
    }
}