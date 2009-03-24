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

    public FunType buildDeleteType(Context ctxt) {
	FunType F = new FunType();
	F.vars = new Sym[1];
	F.types = new Expr[1];
	F.consumps = new int[1];
	
	F.vars[0] = ctxt.newSym("r");
	
	F.types[0] = tp;
	
	F.consumps[0] = FunBase.CONSUMED_NO_RET;
	
	F.rettype = new Void();
	return F;
    }

    public void process(Context ctxt) {
	if (del != null) {
	    String s = ctxt.name("delete_"+tp.name);
	    del.s.output_name = del.s.name;
	    if (!del.s.name.equals(s))
		handleError(ctxt,"The delete function given for a datatype is not named as required."
			    +"\n\n1. the given name: "+del.s.toString(ctxt)
			    +"\n\n2. the required name: "+s);
	    
	    FunType F = buildDeleteType(ctxt);

	    if (!del.T.eqType(ctxt,F)) 
		handleError(ctxt, "The type given for the delete function for a datatype is not of the expected form.\n\n"
			    +"1. the type given: "+del.T.toString(ctxt)
			    +"\n\n2. the expected form: "+F.toString(ctxt));
	    
	    ctxt.addDatatype(tp,del.s); // add first so tp is declared
	    del.process(ctxt);
	}
	else 
	    ctxt.addDatatype(tp,ctors,types,rttypes);

	ctxt.stage = 2;
	
	ctxt.commentBox(tp.name);

	boolean first_type = (ctxt.type_num == 1);

	ctxt.cw.println("#define "+tp.toString(ctxt)+" "+(new Integer(ctxt.type_num++)).toString()+"\n");

	if (first_type) 
	    ctxt.cw.println("char *carraway_mem_start = 0;\n"+
			    "char *carraway_mem_end = 0;\n"+
			    "inline char *carraway_alloc(int numchars) {\n"+
			    "  char *ret;\n"+
			    "  if (carraway_mem_end - carraway_mem_start < numchars)  \n"+
			    "    brk((carraway_mem_end = carraway_mem_end + 16384)); \n"+
			    "  ret = carraway_mem_start; \n"+
			    "  carraway_mem_start += numchars; \n"+
			    "  return ret; \n"+
			    "}");

	if (del == null) {
	    for (int i = 0, iend = ctors.length; i < iend; i++) {
		ctxt.cw.println("#define op_"+ctors[i].toString(ctxt)+" "+(new Integer(i)).toString()+"\n");
		ctxt.cw.println("typedef struct {");
		ctxt.cw.println("  int opval;");
		Expr T = ctxt.getCtorRuntimeType(ctors[i]);
		FunType F = null;
		int jend = 0;
		if (T.construct == Expr.FUN_TYPE) {
		    F = (FunType)T;
		    jend = F.vars.length;
		}
		if (F != null) 
		    for (int j = 0; j < jend; j++) 
			ctxt.cw.println("  void *"+F.vars[j].toString(ctxt)+";");

		String ctor_tp = tp.toString(ctxt)+"_"+ctors[i].toString(ctxt);
		ctxt.cw.println("} "+ctor_tp+";\n");

		// emit function to build data

		ctxt.cw.print("void *"+ctors[i].toString(ctxt)+"(");
		if (F != null) {
		    boolean first = true;
		    for (int j = 0; j < jend; j++) {
			if (first) 
			    first = false;
			else
			    ctxt.cw.print(", ");
			ctxt.cw.print("void *"+F.vars[j].toString(ctxt));
		    }
		}
		ctxt.cw.println(") {");
		ctxt.cw.println("  "+ctor_tp+" *x = ("+ctor_tp+" *)carraway_alloc(4*"+(new Integer(jend+1)).toString()+");");
		ctxt.cw.println("  x->opval = 256 + op_"+ctors[i].toString(ctxt)+";");
		if (F != null) 
		    for (int j = 0; j < jend; j++) {
			String v = F.vars[j].toString(ctxt);
			ctxt.cw.println("  x->"+v+" = "+v+";");
		    }
		ctxt.cw.println("  return x;");
		ctxt.cw.println("}\n");
	    }
	}

	ctxt.cw.flush();
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
