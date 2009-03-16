package guru.carraway;

public class Void extends Expr {

    public Void(){
	super(VOID);
    }

    public void print(java.io.PrintStream w, Context ctxt) {
	w.print("void");
    }    

    public Expr simpleType(Context ctxt) {
	return new Type();
    }

    public boolean eqType(Context ctxt, Expr T) {
	if (T.construct == ABORT)
	    return true;
	return T.construct == VOID;
    }

    public Expr applySubst(Context ctxt) {
	return this;
    }

    public boolean nonBindingOccurrence(Context ctxt, Sym s) {
	return false;
    }
}