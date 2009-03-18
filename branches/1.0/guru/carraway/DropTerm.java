package guru.carraway;
import guru.Position;
import java.util.Collection;
import java.util.Iterator;

public class DropTerm extends Expr {
    public Sym del;
    public Sym rttype;
    public Sym var;

    public DropTerm(){
	super(DROP_TERM);
    }

    public DropTerm(Sym del, Sym rttype, Sym var) {
	super(DROP_TERM);
	this.del = del;
	this.rttype = rttype;
	this.var = var;
    }

    public Expr simpleType(Context ctxt) {
	// drop terms are constructed internally by Match, so they do not need to be type checked.

	return new Void();
    }

    public void print(java.io.PrintStream w, Context ctxt) {
	w.print("(");
	del.print(w,ctxt);
	w.print(" ");
	rttype.print(w,ctxt);
	w.print(" ");
	var.print(w,ctxt);
	w.print(")");
    }    

    public Sym simulate_h(Context ctxt, Position p) {
	Sym r = var.simulate(ctxt,pos);
	
	Position pp = ctxt.wasDropped(r);
	if (pp != null)
	    simulateError(ctxt,"The scrutinee of a match is already dropped by the time a match-case ends.\n\n"
			  +"1. it was dropped at: "+pp.toString());
	Collection c = ctxt.dropRef(r,pos);

	if (c != null && c.size() > 0) {
	    Iterator it = c.iterator();
	    simulateError(ctxt,"The scrutinee of a match is still pinned when it is dropped at the end of a match-case.\n\n"
			  +"1. a pinning reference was created at: "+((Sym)it.next()).posToString());
	}

	return ctxt.voidref;
    }

}