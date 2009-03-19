package guru.carraway;
import guru.Position;

import java.util.Collection;

public class Let extends Expr {

    public Sym x;
    public Expr t1,t2;

    // linearization may leave t2 null, or t1 and t2 null.

    public Let(){
	super(LET);
    }

    public Let(Sym x, Expr t1, Expr t2){
	super(LET);
	this.x = x;
	this.t1 = t1;
	this.t2 = t2;
    }

    // this represents an assignment
    public Let(Sym x, Expr t1, Position p) {
	super(LET);
	this.x = x;
	this.t1 = t1;
	this.pos = p;
    }

    // this represents a variable declaration.
    public Let(Sym x, Position p) {
	super(LET);
	this.x = x;
	this.pos = p;
    }

    public Expr simpleType(Context ctxt) {
	Expr T = t1.simpleType(ctxt);
	if (T.construct == VOID)
	    classifyError(ctxt,"A let-term is defining a variable of type void.\n\n"
			  +"1. the variable: "+x.toString(ctxt)
			  +"\n\n2. the term it is defined to equal: "+t1.toString(ctxt));
	ctxt.setType(x,T);
	return t2.simpleType(ctxt);
    }

    public void do_print(java.io.PrintStream w, Context ctxt) {
	if (t1 == null) {
	    Expr T = ctxt.getType(x);
	    if (T != null && T.construct == TYPE)
		w.print("int ");
	    else
		w.print("void *");
	    x.print(w,ctxt);
	    if (t2 != null)
		compileError(ctxt,"Internal error: a Let term is malformed (t1 is null but t2 is not).");
	}
	else if (t2 == null) {
	    x.print(w,ctxt);
	    w.print(" = ");
	    t1.print(w,ctxt);
	}
	else {
	    w.print("let ");
	    x.print(w,ctxt);
	    w.print(" = ");
	    t1.print(w,ctxt);
	    w.print(" in ");
	    t2.print(w,ctxt);
	}
    }    

    public Sym simulate_h(Context ctxt, Position p) {
	Sym r = t1.simulate(ctxt,pos);
	if (r == null)
	    // abort occurred in t1
	    return null;
	Sym prev = ctxt.getSubst(x);
	ctxt.setSubst(x,r);
	r = t2.simulate(ctxt,pos);
	ctxt.setSubst(x,prev);
	return r;
    }

    public Expr linearize(Context ctxt, guru.Position p, Sym dest, Collection decls, Collection defs) {
	decls.add(x);
	Expr nt1 = t1.linearize(ctxt,pos,x,decls,defs);
	if (dest == null) {
	    defs.add(nt1);
	    return t2.linearize(ctxt,pos,dest,decls,defs);
	}
	else
	    // we are at the top-level
	    return new Do(nt1, t2.linearize(ctxt,pos,dest,decls,defs), pos);
    }
}