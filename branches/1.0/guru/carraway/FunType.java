package guru.carraway;

public class FunType extends FunBase {
    public FunType(){
	super(FUN_TYPE);
    }

    public void print(java.io.PrintStream w, Context ctxt) {
	w.print("Fun");
	super.print(w,ctxt);
    }    

    public Expr simpleType(Context ctxt) {
	checkTypes(ctxt);
	return new Type();
    }

    public boolean eqType(Context ctxt, Expr T) {
	if (T.construct == ABORT)
	    return true;
	if (T.construct != FUN_TYPE)
	    return false;

	FunType f = (FunType)T;
	if (f.vars.length != vars.length)
	    return false;
	
	for (int i = 0, iend = vars.length; i < iend; i++) {
	    if (!f.types[i].eqType(ctxt,types[i]))
		return false;
	    ctxt.setSubst(f.vars[i],vars[i]);
	}
	return f.rettype.eqType(ctxt,rettype);
    }

    public boolean nonBindingOccurrence_h(Context ctxt, Sym s) {
	for (int i = 0, iend = vars.length; i < iend; i++) 
	    if (types[i].nonBindingOccurrence(ctxt,s)) 
		return true;
	return rettype.nonBindingOccurrence(ctxt,s);
    }

    public Expr applySubst(Context ctxt) {
	FunType f = new FunType();
	int iend = vars.length;
	f.vars = new Sym[iend];
	f.types = new Expr[iend];
	f.non_rets = new boolean[iend];
	f.consumes = new boolean[iend];

	for (int i = 0; i < iend; i++) {
	    f.vars[i] = (Sym)vars[i].applySubst(ctxt);
	    f.types[i] = types[i].applySubst(ctxt);
	    f.non_rets[i] = non_rets[i];
	    f.consumes[i] = consumes[i];
	}
	f.rettype = rettype.applySubst(ctxt);

	return f;
    }
}