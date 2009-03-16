package guru.carraway;
import guru.Position;
import java.util.Collection;
import java.util.Iterator;

public class App extends Expr {

    public Sym head;
    public Expr[] args;

    public App(){
	super(APP);
    }

    public void print(java.io.PrintStream w, Context ctxt) {
	w.print("(");
	head.print(w,ctxt);
	for (int i = 0, iend = args.length; i < iend; i++) {
	    w.print(" ");
	    args[i].print(w,ctxt);
	}
	w.print(")");
    }    

    public Expr simpleType(Context ctxt) {
	Expr hT = ctxt.getType(head);
	if (hT == null)
	    classifyError(ctxt,"The head of an application is missing a type.\n\n"
			+"1. the head: "+head.toString(ctxt));
	FunType F = (FunType)hT;
	if (F.vars.length != args.length)
	    classifyError(ctxt,"The head of an application does not accept as many arguments as given.\n\n"
			    +"1. the head: "+head.toString(ctxt)
			    +"\n2. its type: "+ctxt.getType(head).toString(ctxt)
			    +"\n3. the number of arguments: "+(new Integer(args.length)).toString());
	for (int i = 0, iend = args.length; i < iend; i++) {
	    Expr T = args[i].simpleType(ctxt);
	    if (!F.types[i].eqType(ctxt,T))
		classifyError(ctxt,"The type computed for an argument does not match the expected type.\n\n"
			    +"1. the argument: "+args[i].toString(ctxt)
			    +"\n2. its type: "+T.toString(ctxt)
			    +"\n2. the expected type: "+F.types[i].toString(ctxt));
	    if (F.nonBindingOccurrence(ctxt, F.vars[i])) {
		// dependent type here
		if (args[i].construct != SYM || !ctxt.isVar((Sym)args[i]))
		    classifyError(ctxt,"The type for an application will depend on an argument which is not a variable.\n\n"
				+"1. the argument: "+args[i].toString(ctxt)
				+"\n\n2. the type of the head: "+F.toString(ctxt));
		
		ctxt.setSubst(F.vars[i],(Sym)args[i]);
	    }
	}

	return F.rettype.applySubst(ctxt);
    }

    public Sym simulate(Context ctxt) {
	FunType f = (FunType) ctxt.getType(head);

	Sym[] rs = new Sym[args.length];
	for (int i = 0, iend = args.length; i < iend; i++) 
	    rs[i] = args[i].simulate(ctxt);

	Collection[] rs_pinnedby = new Collection[args.length];
	for (int i = 0, iend = args.length; i < iend; i++) 
	    if (f.consumes[i] && 
		f.types[i].construct != UNTRACKED &&
		f.types[i].construct != TYPE) {
		// this is a reference we are supposed to consume
		Position p = ctxt.wasDropped(rs[i]);
		if (p != null) 
		    simulateError(ctxt,"A reference that was already consumed is being consumed again.\n\n"
				  +"1. the reference created at: "+rs[i].posToString()
				  +"\n\n2. first consumed at: "+p.toString());
		rs_pinnedby[i] = ctxt.dropRef(rs[i], pos);
	    }
	
	for (int i = 0, iend = args.length; i < iend; i++) 
	    if (rs_pinnedby[i].size() > 0) {
		Iterator it = rs_pinnedby[i].iterator();
		simulateError(ctxt,"A pinned reference is being consumed.\n\n"
			      +"1. the reference created at: "+rs[i].posToString()
			      +"\n\n2. pinned by the reference created at: "+((Sym)it.next()).posToString());
	    }

	return ctxt.newRef(pos);
    }
}