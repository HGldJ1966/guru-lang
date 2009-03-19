package guru.carraway;
import guru.Position;

import java.util.HashMap;
import java.util.Collection;

public class Sym extends Expr {
    public String name;
    public String output_name;

    public Sym(String name, String output_name) {
	super(SYM);
        this.name = name;
	this.output_name = output_name;
    }

    public void do_print(java.io.PrintStream w, Context ctxt) {
	if (ctxt.stage >= 2 && ctxt.isAttribute(this)) {
	    w.print("void *");
	    return;
	}

	String n = (ctxt.getFlag("print_input_names") ? name : output_name);

	if (!ctxt.getFlag("print_vars_subst")) {
	    w.print(n);
	    return;
	}
	Sym s = ctxt.getSubst(this);
	if (s != null)
	    s.print(w,ctxt);
	else
	    w.print(n);
    }    

    public String refString(Context ctxt) {
	return ((ctxt.getFlag("debug_refs") ?
		toString(ctxt) + ", " : 
		"a reference ")
		+"created at: "+posToString());
    }

    public Expr simpleType(Context ctxt) {
	Expr T = ctxt.getType(this);
	if (T == null)
	    classifyError(ctxt,"Missing type for a symbol.\n\n"
			+"1. the symbol: "+toString(ctxt));
	return T;
    }

    public boolean eqType(Context ctxt, Expr T) {
	if (T.construct == ABORT)
	    return true;
	if (T.construct != SYM)
	    return false;
	return eq(ctxt,(Sym)T);
    }

    public boolean eq(Context ctxt, Sym s) {
	Sym s1 = ctxt.getSubst(this);
	if (s1 != null)
	    return s1.eq(ctxt,s);

	Sym s2 = ctxt.getSubst(s);
	if (s2 != null)
	    return eq(ctxt,s2);

	return s1 == s2;
    }

    public boolean nonBindingOccurrence_h(Context ctxt, Sym s) {
	Sym s1 = ctxt.getSubst(this);
	if (s1 != null)
	    return s1.nonBindingOccurrence(ctxt,s);
	Sym s2 = ctxt.getSubst(s);
	if (s2 != null)
	    return nonBindingOccurrence(ctxt,s2);
	return this == s;
    }

    public Expr applySubst(Context ctxt) {
	Sym s1 = ctxt.getSubst(this);
	if (s1 != null)
	    return s1.applySubst(ctxt);
	return this;
    }

    public Sym simulate_h(Context ctxt, Position p) {
	if (ctxt.isCtor(this)) 
	    // 0-ary constructors create new references
	    return ctxt.newRef(p);
	return (Sym)applySubst(ctxt);
    }

    public Expr linearize(Context ctxt, Position p, Sym dest, Collection decls, Collection defs) {
	Expr e;
	if (ctxt.isCtor(this))
	    e = new App(this,p);
	else
	    e = this;
	return linearize_return(ctxt,e,p,dest);
    }
}
