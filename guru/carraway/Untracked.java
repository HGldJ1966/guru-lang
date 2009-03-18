package guru.carraway;

public class Untracked extends Expr {

    public Untracked(){
	super(UNTRACKED);
    }

    public void print(java.io.PrintStream w, Context ctxt) {
	w.print("untracked");
    }    

    public Expr simpleType(Context ctxt) {
	return new Type();
    }

    public boolean eqType(Context ctxt, Expr T) {
	if (T.construct == ABORT)
	    return true;
	return T.construct == UNTRACKED;
    }

    public Expr applySubst(Context ctxt) {
	return this;
    }

    public boolean nonBindingOccurrence_h(Context ctxt, Sym s) {
	return false;
    }
}