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

    /* -- var is the variable that will be initialized, 
       -- field is the name of the field from the scrutinee that will be extracted for the initialization
       -- scrut is the scrutinee, with scruttp its type
       -- ctor is which ctor built the scrutinee
       -- rttype is the runtime type of the variable (var).
    */
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
	    Sym prev = ctxt.getSubst(h.F.vars[1]);
	    ctxt.setSubst(h.F.vars[1], scrut);
	
	    // init terms are constructed internally by Match, so they do not need to be type checked.
	    Expr ret = h.F.rettype.applySubst(ctxt);
	    ctxt.setSubst(h.F.vars[1], prev);;
	    return ret;
	}
	
	return ctxt.getType(var);
    }

    public void do_print(java.io.PrintStream w, Context ctxt) {
	if (h == null) {
	    if (ctxt.stage <= 2) 
		var.print(w,ctxt);
	    else {
		if (ctxt.getFlag("output_ocaml"))
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
	}
	else {
	    // actually calling the init function
	    if (ctxt.stage <= 2) {
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
		if (ctxt.getFlag("output_ocaml"))
		    var.print(w,ctxt);
		else {
		    String field_access = 
			"(("+scruttp.toString(ctxt)+"_"+ctor.toString(ctxt)
			+" *)"+ scrut.toString(ctxt)+")->";

		    var.print(w,ctxt);
		    w.print(" = ");
		    h.init.print(w,ctxt);
		    w.print("(");
		    if (ctxt.isVar((Sym)rttype))
			w.print(field_access);
		    rttype.print(w,ctxt);
		    w.print(", ");
		    scrut.print(w,ctxt);
		    w.print(", ");
		    w.print(field_access);
		    field.print(w,ctxt);
		    w.print(")");
		    
		    if (h.take_pointer) {
			w.println(";");
			w.print(field_access);
			field.print(w,ctxt);
			w.print(" = 0");
		    }
		    else
			w.println("");
		}
	    }
	}
    }    

    public Sym simulate_h(Context ctxt, Position p) {
	if (h == null)
	    return var;

	Sym r = var.simulate(ctxt,pos);
	
	Context.RefStat u = ctxt.refStatus(ctxt.getSubst(scrut));
	if (!u.consume && h.must_consume_scrut)
	    simulateError(ctxt,p,"An Init function requires the scrutinee to be consumed, but "
			  +"this match's\nscrutinee is marked not to be consumed.\n\n"
			  +"1. the init function: "+h.init.toString(ctxt));

	Sym v = h.F.vars[1];
	Sym prev = ctxt.getSubst(v);
	ctxt.setSubst(v, scrut);
	Expr rettype = h.F.rettype.applySubst(ctxt);
	ctxt.setSubst(v,prev);
	if (rettype.construct == PIN) 
	    ctxt.pin(r,((Pin)rettype).pinned);

	return r;
    }

    public Expr linearize(Context ctxt, guru.Position p, Sym dest, Collection decls, Collection defs) {
	return this;
    }
}