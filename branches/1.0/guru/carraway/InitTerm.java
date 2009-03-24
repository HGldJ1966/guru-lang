package guru.carraway;
import guru.Position;
import java.util.Collection;

public class InitTerm extends Expr {
    public Context.InitH h;
    public Sym rttype;
    public Sym scrut;
    public Sym scruttp;
    public Sym ctor;
    public Sym field;
    public Sym var;

    public InitTerm(){
	super(INIT_TERM);
    }

    public InitTerm(Context.InitH h, Sym rttype, Sym scrut, Sym scruttp, Sym ctor, Sym field, Sym var) {
	super(INIT_TERM);
	this.h = h;
	this.rttype = rttype;
	this.scrut = scrut;
	this.scruttp = scruttp;
	this.ctor = ctor;
	this.field = field;
	this.var = var;
    }

    public Expr simpleType(Context ctxt) {
	if (h != null) {
	    FunType f = (FunType)h.F;
	    ctxt.setSubst(f.vars[1], scrut);
	
	    // init terms are constructed internally by Match, so they do not need to be type checked.
	    return f.rettype.applySubst(ctxt);
	}
	
	return ctxt.getType(var);
    }

    public void do_print(java.io.PrintStream w, Context ctxt) {
	if (h == null) {
	    if (ctxt.stage < 2) 
		var.print(w,ctxt);
	    else {
		var.print(w,ctxt);
		w.print(" = ((");
		scruttp.print(w,ctxt);
		w.print("_");
		ctor.print(w,ctxt);
		w.print(" *)");
		scrut.print(w,ctxt);
		w.print(")->");
		field.print(w,ctxt);
		w.print("");
	    }
	}
	else {
	    // actually calling the init function
	    if (ctxt.stage < 2) {
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
	    else {
		var.print(w,ctxt);
		w.print(" = ");
		h.init.print(w,ctxt);
		w.print("(");
		rttype.print(w,ctxt);
		w.print(", ");
		scrut.print(w,ctxt);
		w.print(", ");
		w.print("((");
		scruttp.print(w,ctxt);
		w.print("_");
		ctor.print(w,ctxt);
		w.print(" *)");
		scrut.print(w,ctxt);
		w.print(")->");
		field.print(w,ctxt);
		w.print(")");
	    }
	}
    }    

    public Sym simulate_h(Context ctxt, Position p) {
	if (h == null)
	    return var;

	Sym r = var.simulate(ctxt,pos);
	
	if (!ctxt.isPinning(r)) {
	    /* if r is already pinning another variable, then
	       we do not consider it to be pinning the scrutinee */
	    Sym r2 = scrut.simulate(ctxt,pos);
	    Sym[] x = new Sym[1];
	    x[0] = r2;
	    ctxt.pin(r,x);
	}

	return r;
    }

    public Expr linearize(Context ctxt, guru.Position p, Sym dest, Collection decls, Collection defs) {
	return this;
    }
}