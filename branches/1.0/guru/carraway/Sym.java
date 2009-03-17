package guru.carraway;
import guru.Position;

public class Sym extends Expr {
    public String name;

    public Sym(String name){
	super(SYM);
        this.name = name;
    }

    public void print(java.io.PrintStream w, Context ctxt) {
	Sym s = ctxt.getSubst(this);
	if (s != null)
	    s.print(w,ctxt);
	else
	    w.print(name);
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

    public boolean nonBindingOccurrence(Context ctxt, Sym s) {
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
	    s1.applySubst(ctxt);
	return this;
    }

    public Sym simulate(Context ctxt, Position p) {
	if (ctxt.isCtor(this)) 
	    // 0-ary constructors create new references
	    return ctxt.newRef(p);
	return (Sym)applySubst(ctxt);
    }

}