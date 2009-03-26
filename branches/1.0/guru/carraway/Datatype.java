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
	    if (!del.s.output_name.equals(s))
		handleError(ctxt,"The delete function given for a datatype is not named as required."
			    +"\n\n1. the given name: "+del.s.name
			    +"\n\n1. the output version: "+del.s.output_name
			    +"\n\n2. the output version should be: "+s);
	    
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

	ctxt.stage = 3;
	
	ctxt.commentBox(tp.name);

	ctxt.cw.println("#define "+tp.toString(ctxt)+" "+(new Integer(ctxt.type_num++)).toString()+"\n");

	if (del == null) {

	    int num_untracked = 0;
	    int num_ctors = ctors.length;
	    for (int i = 0; i < num_ctors; i++) 
		if (types[i].construct == Expr.UNTRACKED)
		    num_untracked++;
	    String tpstr = tp.toString(ctxt);
	    if (0 < num_untracked && num_untracked < num_ctors) 
		handleError(ctxt, "A datatype is declared with some untracked and some tracked constructors.\n\n"
			    +"1. the datatype: "+tpstr);

	    // emit definition of tags for ctors

	    for (int i = 0; i < num_ctors; i++) 
		ctxt.cw.println("#define op_"+ctors[i].toString(ctxt)+" "+(new Integer(i)).toString()+"\n");

	    if (num_untracked == num_ctors) {
		// this is a special case, since we do no allocation or deallocation

		for (int i = 0; i < num_ctors; i++) {
		    String ctr = ctors[i].toString(ctxt);
		    ctxt.cw.println("#define "+ctr+"() op_"+ctr);
		    ctxt.cw.println("#define clear_"+tpstr+"_"+ctr+"(x) \n");
		}

		ctxt.cw.println("#define delete_"+tpstr+"(x) \n"); 
		ctxt.cw.flush();
		return;
	    }

	    // tracked data

	    for (int i = 0; i < num_ctors; i++) {
		
		// emit the ctor's struct

		ctxt.cw.println("typedef struct {");
		ctxt.cw.println("  int opval;");
		Expr T = ctxt.getCtorRuntimeType(ctors[i]);
		FunType R = null;
		FunType F = null;
		int jend = 0;
		if (T.construct == Expr.FUN_TYPE) {
		    R = (FunType)T;
		    F = (FunType) types[i];
		    jend = R.vars.length;
		}
		if (R != null) 
		    for (int j = 0; j < jend; j++) 
			ctxt.cw.println("  void *"+F.vars[j].toString(ctxt)+";");

		String ctor_tp = tpstr+"_"+ctors[i].toString(ctxt);
		ctxt.cw.println("} "+ctor_tp+";\n");

		// sz, fl, and flptr are used if we emit code using free lists
		String sz = new Integer(jend).toString();
		String fl = "free_"+sz;
		/* for size 0 ctors (with no subdata) we abuse the opval field for the
		   next pointer of the free list.  Otherwise, we use the first subdatum pointer. */ 
		String flind = (jend == 0 ? "0" : "1");
		
		if (!ctxt.getFlag("use_malloc")) {

		    // emit the free list and delete function

		    if (!ctxt.free_lists_emitted.contains(sz)) {
			// we need to emit the free list and delete function.
			ctxt.free_lists_emitted.add(sz);
			ctxt.cw.println("void *"+fl+" = (void *)0;\n");
			ctxt.cw.println("void delete_"+sz+"(void *_x) {");
			ctxt.cw.println("  void **x = (void **)_x;");
			ctxt.cw.println("  x["+flind+"] = "+fl+";");
			ctxt.cw.println("  "+fl+" = x;");
			ctxt.cw.println("}\n");
		    }
		    ctxt.cw.println("#define delete_"+ctor_tp+" delete_"+sz+"\n");
		}

		// emit the clear() function

		if (R == null) 
		    // nothing to clear for 0-ary ctor
		    ctxt.cw.println("#define clear_"+ctor_tp+"(x) \n");
		else {
		    ctxt.cw.println("void clear_"+ctor_tp+"(void *_x) {");
		    ctxt.cw.println("  "+ctor_tp+" *x = ("+ctor_tp+" *)_x;");
		    for (int j = 0; j < jend; j++) {
			String v = F.vars[j].toString(ctxt);
			Expr Tj = F.types[j];
			if (Tj.consumable()) {
			    Sym Tjh = (Tj.construct == Expr.PIN ? ((Pin)Tj).s : (Sym)Tj);
			    Sym df = ctxt.getDropFunction(Tjh);
			    Expr rttype = R.types[j];
			    String rttypestr = rttype.toString(ctxt);
			    if (ctxt.isVar((Sym)rttype))
				rttypestr = "x->"+rttypestr;
			    ctxt.cw.println("  "+df.toString(ctxt)+"("+rttypestr+", x->"+v+");");
			}
		    }
		    ctxt.cw.println("}\n");
		}

		// emit function to build data

		ctxt.cw.print("void *"+ctors[i].toString(ctxt)+"(");
		if (R != null) {
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
		ctxt.cw.println("  "+ctor_tp+" *x;");
		String bstr = "sizeof(void *)*"+(new Integer(jend+1)).toString();
		if (ctxt.getFlag("use_malloc")) 
		    ctxt.cw.println("  x = ("+ctor_tp+" *)malloc("+bstr+");");
		else {
		    ctxt.cw.println("  if ("+fl+") {");
		    ctxt.cw.println("    x = ("+ctor_tp+" *)"+fl+";");
		    ctxt.cw.println("    "+fl+" = ((void **)x)["+flind+"];");
		    ctxt.cw.println("    clear_"+ctor_tp+"(x);");
		    ctxt.cw.println("  }");
		    ctxt.cw.println("  else");
		    ctxt.cw.println("    x = ("+ctor_tp+" *)carraway_alloc("+bstr+");");
		}

		ctxt.cw.println("  x->opval = 256 + op_"+ctors[i].toString(ctxt)+";");
		if (R != null) 
		    for (int j = 0; j < jend; j++) {
			String v = F.vars[j].toString(ctxt);
			ctxt.cw.println("  x->"+v+" = "+v+";");
		    }
		ctxt.cw.println("  return x;");
		ctxt.cw.println("}\n");

	    }

	    // now emit the delete function for the datatype

	    ctxt.cw.println("void delete_"+tpstr+"(void *x) {");
	    ctxt.cw.println("  *(int *)x = ("+tpstr+" << 8) | ctor(x); // store the type here for benefit of clear()");
	    ctxt.cw.println("  switch ctor(x) {");
	    for (int i = 0; i < num_ctors; i++) {
		String ctr = ctors[i].toString(ctxt);
		ctxt.cw.println("  case op_"+ctr+": ");
		if (ctxt.getFlag("use_malloc")) {
		    ctxt.cw.println("    clear_"+tpstr+"_"+ctr+"(x);");
		    ctxt.cw.println("    free(x);");
		}
		else
		    ctxt.cw.println("    delete_"+tpstr+"_"+ctr+"(x);");
		ctxt.cw.println("    break;\n");
	    }
	    ctxt.cw.println("}");
	    ctxt.cw.println("}\n");
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
