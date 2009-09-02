package guru.carraway;

public class FunType extends FunBase {
    public FunType(){
	super(FUN_TYPE);
    }

    public void do_print(java.io.PrintStream w, Context ctxt) {
	if (ctxt.stage <= 2)
	    w.print("Fun");
	super.do_print(w,ctxt);
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
	    if (f.consumps[i] != consumps[i])
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
	f.consumps = new int[iend];

	for (int i = 0; i < iend; i++) {
	    f.vars[i] = (Sym)vars[i].applySubst(ctxt);
	    f.types[i] = types[i].applySubst(ctxt);
	    f.consumps[i] = consumps[i];
	}
	f.rettype = rettype.applySubst(ctxt);

	return f;
    }

    public Expr flattenType(Context ctxt) {
	Sym n = ctxt.newSym("funtp",pos,true);
	ctxt.declareConst(n);

	// build flattened FunType F

	FunType F = new FunType();
	F.pos = pos;
	int iend = vars.length;
	F.vars = new Sym[iend];
	F.types = new Expr[iend];
	F.consumps = new int[iend];
	for (int i = 0; i < iend; i++) {
	    F.vars[i] = vars[i];
	    F.types[i] = types[i].flattenType(ctxt);
	    F.consumps[i] = consumps[i];
	}
	F.rettype = rettype.flattenType(ctxt);

	// add new TypeDef command (we'll process it later, in Function)

	TypeDef C = new TypeDef();
	C.pos = pos;
	C.c = n;
	C.T = F;
	ctxt.new_typedefs.add(C);

	return n;
    }

}