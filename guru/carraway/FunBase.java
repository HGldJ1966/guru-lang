package guru.carraway;

abstract public class FunBase extends Expr {
    public Sym[] vars;
    public Expr[] types;
    public boolean[] specs;
    public boolean[] consumes;
    public Expr rettype;

    public FunBase(int construct){
	super(construct);
    }

    protected void checkTypes(Context ctxt) {
	for (int i = 0, iend = types.length; i < iend; i++) {
	    if (types[i].construct != TYPE) {
		if (types[i].construct == VOID)
		    classifyError(ctxt,"A local variable is declared with type \"void\"..\n\n"
				  +"1. the local variable: "+vars[i].toString(ctxt));
		Expr T = types[i].simpleType(ctxt);
		if (T.construct != TYPE)
		    classifyError(ctxt,"The expression given as the type of a local variable is not a type.\n\n"
				  +"1. the local variable: "+vars[i].toString(ctxt)
				  +"\n2. its type: "+types[i].toString(ctxt)
				  +"\n3. the type of that type: "+T.toString(ctxt));
	    }
	    ctxt.setType(vars[i],types[i]);
	}
	if (rettype.construct != TYPE) {
	    Expr T = rettype.simpleType(ctxt);
	    if (T.construct != TYPE)
		classifyError(ctxt,"The expression given as a return type is not a type.\n\n"
			      +"1. the expression: "+rettype.toString(ctxt)
			      +"\n2. its type: "+T.toString(ctxt));
	}
    }

    public void print(java.io.PrintStream w, Context ctxt) {
	for(int i = 0, iend = vars.length; i < iend; i++) {
	    w.print("(");
	    if (specs[i])
		w.print("^ ");
	    if (consumes[i])
		w.print("! ");
	    vars[i].print(w,ctxt);
	    w.print(" : ");
	    types[i].print(w,ctxt);
	    w.print(")");
	}
	w.print(" . ");
	rettype.print(w,ctxt);
    }    

}