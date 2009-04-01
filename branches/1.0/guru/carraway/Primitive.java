package guru.carraway;

public class Primitive extends Command {
    public Sym s;
    public Expr T;
    String delim, code;

    public Primitive() {
	super(PRIMITIVE);
    }

    public void process(Context ctxt) {
	Expr cT = T.simpleType(ctxt);
	if (T.construct == Expr.SYM && !ctxt.isAttribute((Sym)T))
	    handleError(ctxt,"The expression given for a primitive is a symbol but not an attribute.\n\n"
			+"1. the primitive: "+s.toString(ctxt)
			+"\n\n2. the expression: "+T.toString(ctxt)
			+"\n\n3. its type: "+cT.toString(ctxt));
	if (cT.construct != Expr.TYPE)
	    handleError(ctxt,"The expression given for a primitive is not a type.\n\n"
			+"1. the primitive: "+s.toString(ctxt)
			+"\n\n2. the expression: "+T.toString(ctxt)
			+"\n\n3. its type: "+cT.toString(ctxt));
	ctxt.addPrimitive(s,T,code);

	if (T.construct == Expr.SYM) 
	    // we need to add a reference here for simulation purposes.
	    ctxt.setSubst(s, ctxt.newRef(pos));

	if (!ctxt.getFlag("output_ocaml")) {
	    ctxt.cw.println(code);
	    ctxt.cw.println("");
	    ctxt.cw.flush();
	}
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("Primitive ");
	print_h(w,ctxt);
    }

    public void print_h(java.io.PrintStream w, 
			Context ctxt) {
	w.print(s.toString(ctxt)+" : ");
	T.print(w,ctxt);
	w.print(" <<");
	w.println(delim);
	w.println(code);
	w.println(delim);
    }

}