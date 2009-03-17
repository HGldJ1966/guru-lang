package guru.carraway;
import guru.Position;

public class InitTerm extends Expr {
    public Context.InitH h;
    public Sym rttype;
    public Sym scrut;
    public Sym var;

    public InitTerm(){
	super(INIT_TERM);
    }

    public InitTerm(Sym init, Sym rttype, Sym scrut, Sym var) {
	super(INITTERM);
	this.init = init;
	this.rttype = rttype;
	this.scrut = scrut;
	this.var = var;
    }

    public Expr simpleType(Context ctxt) {
	FunType f = (FunType)h.F;
	if (scrut == null) {
	    if (f.rettype == PIN) 
		classifyError(ctxt,"A non-variable scrutinee is being used, where initialization of one of its subdata\n"
			      +"requires a variable for the scrutinee.\n\n"
			      +"1. the pattern variable for the subdatum: "+var.toString(ctxt)
			      +"\n\n2. the init function used: "+h.init.toString(ctxt)
			      +"\n\n3. the init function's type: "+f.toString(ctxt));
	}
	else 
	    ctxt.setSubst(f.vars[1], scrut);
	
	// init terms are constructed internally by Match, so they do not need to be type checked.

	return f.rettype.applySubst(ctxt);
    }

    public void print(java.io.PrintStream w, Context ctxt) {
	w.print("(");
	h.init.print(w,ctxt);
	w.print(" ");
	rttype.print(w,ctxt);
	w.print(" ");
	scrut.print(w,ctxt);
	w.print(" ");
	var.print(w,ctxt);
	w.print(")");
    }    

    public Sym simulate(Context ctxt, Position p) {
	Sym r = var.simulate(ctxt,pos);
	
	if (scrut != null) {
	    if (!ctxt.isPinning(r)) {
		/* if r is already pinning another variable, then
		   we do not consider it to be pinning the scrutinee */
		Sym r2 = scrut.simulate(ctxt,pos);
		Sym[] x = new Sym[1];
		x[0] = r2;
		ctxt.pin(r,x);
	    }
	}

	return r;
    }

}