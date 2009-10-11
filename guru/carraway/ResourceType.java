package guru.carraway;

public class ResourceType extends Command {
    public Sym s;

    public Primitive drop;

    protected static boolean first_attribute = true;

    public ResourceType() {
	super(ATTRIBUTE);
    }

    public FunType buildDropType(Context ctxt) {
	FunType F = new FunType();
	F.vars = new Sym[2];
	F.types = new Expr[2];
	F.consumps = new int[2];
	
	F.vars[0] = ctxt.newSym("A",false);
	F.vars[1] = ctxt.newSym("r",false);
	
	F.types[0] = new Type();
	F.types[1] = s;
	
	F.consumps[0] = FunBase.CONSUMED_RET_OK;
	F.consumps[1] = FunBase.CONSUMED_NO_RET;
	
	F.rettype = new Void();
	return F;
    }

    public void process(Context ctxt) {
	ctxt.stage = 0;
	String ss = ctxt.name("consume_"+s.name);
	if (!drop.s.output_name.equals(ss))
	    handleError(ctxt,"The drop function given for an attribute is not named as required."
			+"\n\n1. the given name: "+drop.s.name
			+"\n\n2. the output version: "+drop.s.output_name
			+"\n\n3. the output version should be: "+ss);
	FunType F = buildDropType(ctxt);

	if (!drop.T.eqType(ctxt,F)) 
	    handleError(ctxt, "The type given for the drop function for an attribute is not of the expected form.\n\n"
			+"1. the type given: "+drop.T.toString(ctxt)
			+"\n\n2. the expected form: "+F.toString(ctxt));

	// need to add the attribute first, since it is mentioned in the type of the drop function.
	ctxt.addResourceType(s,drop.s);
	if (first_attribute) {
	    if (!ctxt.getFlag("output_ocaml")) {
		ctxt.cw.println("#include <limits.h>\n\n"
				+"#define ctor(x) (*((int *)x) & 255)\n"
				+"#define op(x) (*((int *)x))\n\n"
				+"void inc(void *x) {\n"
				+"  unsigned tmp = *((int *)x) | 255;\n"
				+"  if (tmp != UINT_MAX) *((int *)x) = *((int *)x) + 256;\n"
				+"}\n\n"
				+"void dec(void *x) {\n"
				+"  unsigned tmp = *((int *)x) | 255;\n"
				+"  if (tmp != UINT_MAX) *((int *)x) = *((int *)x) - 256;\n"
				+"}\n");
		ctxt.cw.flush();
	    }
	    first_attribute = false;
	}

	drop.process(ctxt);
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	w.println("ResourceType "+s.toString(ctxt)+" with ");
	drop.print(w,ctxt);
    }


}