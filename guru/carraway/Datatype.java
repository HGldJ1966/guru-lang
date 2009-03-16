package guru.carraway;

public class Datatype extends Command {
    Sym tp;
    Sym[] ctors;
    Expr[] types;
    Expr[] rttypes;

    public Datatype() {
	super(DATATYPE);
    }

    public void process(Context ctxt) {
	ctxt.addDatatype(tp,ctors,types,rttypes);
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("Datatype ");
	tp.print(w,ctxt);
	w.print(" = ");
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
