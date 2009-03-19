package guru.carraway;

abstract public class FunBase extends Expr {
    public Sym[] vars;
    public Expr[] types;
    public boolean[] non_rets;
    public boolean[] consumes;
    public Expr rettype;

    public FunBase(int construct){
	super(construct);
    }

    // create a base for a "void -> void" function.
    public FunBase(int construct, guru.Position p){
	super(construct);
	vars = new Sym[0];
	types = new Expr[0];
	non_rets = new boolean[0];
	consumes = new boolean[0];
	rettype = new Void();
	this.pos = p;
    }

    protected void checkTypes(Context ctxt) {
	for (int i = 0, iend = types.length; i < iend; i++) {
	    if (types[i].construct != TYPE) {
		if (types[i].construct == VOID)
		    classifyError(ctxt,"An input variable is declared with type \"void\"..\n\n"
				  +"1. the input variable: "+vars[i].toString(ctxt));
		if (non_rets[i] && types[i].construct == PIN)
		    classifyError(ctxt,"An input variable is marked as not to be returned, but its type is a pin-type.\n\n"
				  +"1. the input variable: "+vars[i].toString(ctxt)
				  +"\n\n2. its type: "+types[i].toString(ctxt));
		    
		Expr T = types[i].simpleType(ctxt);
		if (T.construct != TYPE)
		    classifyError(ctxt,"The expression given as the type of an input variable is not a type.\n\n"
				  +"1. the local variable: "+vars[i].toString(ctxt)
				  +"\n2. its type: "+types[i].toString(ctxt)
				  +"\n3. the type of that type: "+T.toString(ctxt));
	    }
	    if (!consumes[i])
		ctxt.setNotConsumed(vars[i]);
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

    public void do_print(java.io.PrintStream w, Context ctxt) {
	if (ctxt.stage < 2) {
	    for(int i = 0, iend = vars.length; i < iend; i++) {
		w.print("(");
		if (!consumes[i])
		    w.print("! ");
		else if (non_rets[i])
		    w.print("^ ");
		vars[i].print(w,ctxt);
		w.print(" : ");
		types[i].print(w,ctxt);
		w.print(")");
	    }
	    w.print(" . ");
	    rettype.print(w,ctxt);
	}
	else {
	    w.print("(");
	    for(int i = 0, iend = vars.length; i < iend; i++) {
		types[i].print(w,ctxt);
		w.print(" ");
		vars[i].print(w,ctxt);
		if (i < iend - 1)
		    w.print(", ");
	    }
	    w.print(")");
	}
    }    

}