package guru.carraway;
import guru.Position;

public class Init extends Command {
    Primitive init;

    public Init() {
	super(INIT);
    }

    public void process(Context ctxt) {
	if (init.T.construct != Expr.FUN_TYPE)
	    handleError(ctxt,"The expression given for the type in an Init-command is not a Fun-type.\n\n"
			+"\n\n1. the expression: "+init.T.toString(ctxt));
	FunType f = (FunType)init.T;

	if (f.vars.length != 3) 
	    handleError(ctxt,"The expression given for the type in an Init-command does not have exactly 3 inputs.\n\n"
			+"\n\n1. the expression: "+f.toString(ctxt));
	
	if (f.types[0].construct != Expr.TYPE)
	    handleError(ctxt,"The type of the first input in an Init-command is not \"type\".\n\n"
			+"\n\n1. the type: "+f.types[0].toString(ctxt));
	
	if (f.types[1].construct != Expr.SYM || !ctxt.isAttribute((Sym)f.types[1])) 
	    handleError(ctxt,"The type of the second input in an Init-command is not an attribute.\n\n"
			+"\n\n1. the type: "+f.types[1].toString(ctxt));

	if (f.specs[1] || f.consumes[1])
	    handleError(ctxt,"The second input in an Init-command is labeled specificational or consumed.");
	
	if (f.types[2].construct != Expr.SYM || !ctxt.isAttribute((Sym)f.types[2])) 
	    handleError(ctxt,"The type of the third input in an Init-command is not an attribute.\n\n"
			+"\n\n1. the type: "+f.types[2].toString(ctxt));

	if (f.specs[2] || !f.consumes[2])
	    handleError(ctxt,"The third input in an Init-command is labeled specificational or not consumed.");

	if (f.rettype.construct == PIN) {
	    Pin p = (Pin)f.rettype;

	    if (p.pinned.length != 1 || p.pinned[0] != f.vars[1]) 
		handleError(ctxt,"The return type in an Init-command is pinning something other than just the second argument.");
	}

	String n = ctxt.name("init_"+f.types[1].toString(ctxt)+"_"+f.types[2].toString(ctxt));

	if (!init.s.name.equals(n))
	    handleError(ctxt,"An init function's name is different from the required one.\n\n"
			+"1. the given name: "+init.s.toString(ctxt)
			+"\n\n2. the required name: "+n);

	Position p = ctxt.addInit(init.s, (Sym)f.types[1],(Sym)f.types[2],f,init.code);
	if (p != null) 
	    handleError(ctxt,"A previous Init-command is being shadowed.\n\n"
			+"1. the new command is at: "+init.T.posToString()
			+"\n\n2. the previous one is at: "+p.toString());
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("Init ");
	init.print_h(w,ctxt);
    }

}