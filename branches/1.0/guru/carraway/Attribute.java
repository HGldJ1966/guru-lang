package guru.carraway;

public class Attribute extends Command {
    public Sym s;

    public Primitive drop;

    public Attribute() {
	super(ATTRIBUTE);
    }

    public void process(Context ctxt) {
	String ss = ctxt.name("drop_"+s.name);
	if (!drop.s.name.equals(ss))
	    handleError(ctxt,"The drop function given for an attribute is not named as required."
			+"\n\n1. the given name: "+drop.s.toString(ctxt)
			+"\n\n2. the required name: "+ss);
	FunType F = Datatype.buildDropType(s);

	if (!drop.T.eqType(ctxt,F)) 
	    handleError(ctxt, "The type given for the drop function for an attribute is not of the expected form.\n\n"
			+"1. the type given: "+drop.T.toString(ctxt)
			+"\n\n2. the expected form: "+F.toString(ctxt));

	// need to add the attribute first, since it is mentioned in the type of the drop function.
	ctxt.addAttribute(s,drop.s);
	drop.process(ctxt);
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	w.println("Attribute "+s.toString(ctxt)+" with ");
	drop.print(w,ctxt);
    }


}