package guru.carraway;

public class Datatype extends Command {
    Sym tp;
    Sym[] ctors;
    Expr[] types;
    Expr[] rttypes;

    public Primitive del;

    public Datatype() {
	super(DATATYPE);
    }

    public static FunType buildDropType(Expr tp) {
	FunType F = new FunType();
	F.vars = new Sym[2];
	F.types = new Expr[2];
	F.consumes = new boolean[2];
	
	F.vars[0] = new Sym("A");
	F.vars[1] = new Sym("r");
	
	F.types[0] = new Type();
	F.types[1] = tp;
	
	F.consumes[0] = F.consumes[1] = true;
	
	F.rettype = new Void();
	return F;
    }

    public void process(Context ctxt) {
	if (del != null) {
	    String s = ctxt.name("delete_"+tp.name);
	    if (!del.s.name.equals(s))
		handleError(ctxt,"The delete function given for a datatype is not named as required."
			    +"\n\n1. the given name: "+del.s.toString(ctxt)
			    +"\n\n2. the required name: "+s);
	    
	    FunType F = buildDropType(tp);

	    if (!del.T.eqType(ctxt,F)) 
		handleError(ctxt, "The type given for the delete function for a datatype is not of the expected form.\n\n"
			    +"1. the type given: "+del.T.toString(ctxt)
			    +"\n\n2. the expected form: "+F.toString(ctxt));
	    
	    del.process(ctxt);
	    ctxt.addDatatype(tp,del.s);
	}
	else
	    ctxt.addDatatype(tp,ctors,types,rttypes);
    }

    public void print(java.io.PrintStream w, Context ctxt) {
	w.print("Datatype ");
	tp.print(w,ctxt);
	if (del != null) {
	    w.println(" with ");
	    del.print_h(w,ctxt);
	}
	else {
	    w.print(" := ");
	    boolean first = true;
	    for (int i = 0, iend = ctors.length; i < iend; i++) {
		w.println("");
		if (first) {
		    w.print("   ");
		    first = false;
		}
		else
		    w.print(" | ");
		ctors[i].print(w,ctxt);
		w.print(" : ");
		types[i].print(w,ctxt);
		if (rttypes[i] != null) {
		    w.print(" & ");
		    rttypes[i].print(w,ctxt);
		}
	    }
	    w.println(".");
	}
    }
}
