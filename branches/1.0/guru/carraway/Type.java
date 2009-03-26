package guru.carraway;

public class Type extends Expr {

    public Type(){
	super(TYPE);
    }

    public void do_print(java.io.PrintStream w, Context ctxt) {
	if (ctxt.stage <= 2)
	    w.print("type");
	else
	    w.print("int");
    }    

    public boolean nonBindingOccurrence_h(Context ctxt, Sym s) {
	return false;
    }

    public Expr applySubst(Context ctxt) {
	return this;
    }

    public Expr simpleType(Context ctxt) {
	classifyError(ctxt,"There is no classifier for type.");
	return null;
    }

    public boolean eqType(Context ctxt, Expr T) {
	if (T.construct == ABORT)
	    return true;
	return T.construct == TYPE;
    }

}