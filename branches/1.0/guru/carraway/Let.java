package guru.carraway;
import guru.Position;

public class Let extends Expr {

    public Sym x;
    public Expr t1,t2;

    public Let(){
	super(LET);
    }

    public Let(Sym x, Expr t1, Expr t2){
	super(LET);
	this.x = x;
	this.t1 = t1;
	this.t2 = t2;
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

    public Sym simulate(Context ctxt, Position p) {
	Sym r = t1.simulate(ctxt,pos);
	if (r == null)
	    // abort occurred in t1
	    return null;
	ctxt.setSubst(x,r);
	r = t2.simulate(ctxt,pos);
	ctxt.setSubst(x,null);
	return r;
    }
}