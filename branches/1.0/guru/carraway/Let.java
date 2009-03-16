package guru.carraway;

public class Let extends Expr {

    public Sym x;
    public Expr t1,t2;

    public Let(){
	super(LET);
    }

    public Expr simpleType(Context ctxt) {
	ctxt.setType(x,t1.simpleType(ctxt));
	return t2.simpleType(ctxt);
    }

    public void print(java.io.PrintStream w, Context ctxt) {
	w.print("let ");
	x.print(w,ctxt);
	w.print(" = ");
	t1.print(w,ctxt);
	w.print(" in ");
	t2.print(w,ctxt);
    }    

    public Sym simulate(Context ctxt) {
	Sym r = t1.simulate(ctxt);
	if (r == null)
	    // abort occurred in t1
	    return null;
	ctxt.setSubst(x,r);
	r = t2.simulate(ctxt);
	ctxt.setSubst(x,null);
	return r;
    }
}