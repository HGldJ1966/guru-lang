package guru.carraway;

public class Datatype extends Command {
    public Sym tp;
    public Sym[] ctors;
    public Expr[] types;
    public Expr[] rttypes;

    public Primitive del;

    public int FREE_LIST_MAX = 10;

    public Datatype() {
	super(DATATYPE);
    }

    public FunType buildDeleteType(Context ctxt) {
	FunType F = new FunType();
	F.vars = new Sym[1];
	F.types = new Expr[1];
	F.consumps = new int[1];
	
	F.vars[0] = ctxt.newSym("r",false);
	
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

	ctxt.stage = 0;

	ctxt.commentBox(tp.name);

	if (del == null) {
	    for (int i = 0, iend = ctors.length; i < iend; i++) {
		types[i].comment_expr(ctors[i],ctxt,true);
		rttypes[i].comment_expr(ctors[i],ctxt,true);
	    }
	}

	ctxt.stage = 3;
	
	if (!ctxt.getFlag("output_ocaml")) 
	    ctxt.cw.println("#define "+tp.toString(ctxt)+" "+(new Integer(ctxt.type_num++)).toString()+"\n");

	if (del == null) {

	    String tpstr = tp.toString(ctxt);
	    int num_ctors = ctors.length;

	    if (ctxt.getFlag("output_ocaml")) {
		ctxt.cw.println("type "+tpstr+" = ");
		for (int i = 0; i < num_ctors; i++) {
		    ctxt.cw.print("| "+ctors[i].toString(ctxt));
		    Expr T = ctxt.getCtorRuntimeType(ctors[i]);
		    if (T.construct == Expr.FUN_TYPE) {
			ctxt.cw.print(" of ");
			FunType F = (FunType)T;
			for (int j = 0, jend = F.types.length; j < jend; j++) {
			    if (j != 0)
				ctxt.cw.print(" * ");
			    F.types[j].print(ctxt.cw,ctxt);
			}
		    }
		    ctxt.cw.println("");
		}
		ctxt.cw.println(";;");
	    }
	    else {

		// emit C code for datatypes

		int num_untracked = 0;
		for (int i = 0; i < num_ctors; i++) 
		    if (types[i].construct == Expr.UNTRACKED)
			num_untracked++;
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
			    ctxt.cw.println("  void *"+R.vars[j].toString(ctxt)+";");

		    String ctor_tp = tpstr+"_"+ctors[i].toString(ctxt);
		    ctxt.cw.println("} "+ctor_tp+";\n");

		    // emit selectors for the ctor's struct

		    if (R != null) {
			for (int j = 0; j < jend; j++) {
			    ctxt.cw.print("#define select_"+tp.name+"_"+ctors[i].name+"_"+R.vars[j].name+"(x) ");
			    ctxt.cw.println("((("+ctor_tp+" *)x)->"+R.vars[j].toString(ctxt)+")");
			}
			ctxt.cw.println("");
		    }

		    String fl = "free_"+ctor_tp;
		
		    ctxt.cw.println("#define carraway_malloc(x) malloc(x)");
		    ctxt.cw.println("#define carraway_free(x) free(x)");
		    ctxt.cw.println("#define guru_malloc(x) carraway_malloc(x)");
		    ctxt.cw.println("#define guru_free(x) carraway_free(x)");
		    
		    // emit prototype for the clear() function
		    
		    if (R == null)
			// nothing to clear for 0-ary ctor
			ctxt.cw.println("#define clear_"+ctor_tp+"(x) \n");
		    else 
			ctxt.cw.println("void clear_"+ctor_tp+"(void *_x);");
			
		    // emit the free list and delete function

		    ctxt.cw.println("int "+fl+"_len = 0;");
		    ctxt.cw.println("void *"+fl+" = (void *)0;\n");
		    ctxt.cw.println("void delete_"+ctor_tp+"(void *_x) {");
		    ctxt.cw.println("  if ("+fl+"_len > "+FREE_LIST_MAX+") {");
		    ctxt.cw.println("    clear_"+ctor_tp+"(_x);");
		    ctxt.cw.println("    carraway_free(_x);");
		    ctxt.cw.println("  }");
		    ctxt.cw.println("  else {");
		    ctxt.cw.println("    void **x = (void **)_x;");
		    ctxt.cw.println("    x[0] = "+fl+";");
		    ctxt.cw.println("    "+fl+" = x;");
		    ctxt.cw.println("    "+fl+"_len++;");
		    ctxt.cw.println("  }");
		    ctxt.cw.println("}\n");
		    
		    // emit the clear function

		    if (R != null)  {
			ctxt.cw.println("void clear_"+ctor_tp+"(void *_x) {");
			ctxt.cw.println("  "+ctor_tp+" *x = ("+ctor_tp+" *)_x;");
			for (int j = 0; j < jend; j++) {
			    String v = R.vars[j].toString(ctxt);
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
			    ctxt.cw.print("void *"+R.vars[j].toString(ctxt));
			}
		    }
		    ctxt.cw.println(") {");
		    ctxt.cw.println("  "+ctor_tp+" *x;");
		    String bstr = "sizeof(void *)*"+(new Integer(jend+1)).toString();
		    ctxt.cw.println("  if ("+fl+") {");
		    ctxt.cw.println("    x = ("+ctor_tp+" *)"+fl+";");
		    ctxt.cw.println("    "+fl+" = ((void **)x)[0];");
		    ctxt.cw.println("    "+fl+"_len--;");
		    ctxt.cw.println("    clear_"+ctor_tp+"(x);");
		    ctxt.cw.println("  }");
		    ctxt.cw.println("  else");
		    ctxt.cw.println("    x = ("+ctor_tp+" *)carraway_malloc("+bstr+");");

		    ctxt.cw.println("  x->opval = 256 + op_"+ctors[i].toString(ctxt)+";");
		    if (R != null) 
			for (int j = 0; j < jend; j++) {
			    String v = R.vars[j].toString(ctxt);
			    ctxt.cw.println("  x->"+v+" = "+v+";");
			}
		    ctxt.cw.println("  return x;");
		    ctxt.cw.println("}\n");

		}

		// now emit the delete function for the datatype

		ctxt.cw.println("void delete_"+tpstr+"(void *x) {");
		ctxt.cw.println("  switch ctor(x) {");
		for (int i = 0; i < num_ctors; i++) {
		    String ctr = ctors[i].toString(ctxt);
		    ctxt.cw.println("  case op_"+ctr+": ");
		    ctxt.cw.println("    delete_"+tpstr+"_"+ctr+"(x);");
		    ctxt.cw.println("    break;\n");
		}
		ctxt.cw.println("}");
		ctxt.cw.println("}\n");
	    }
	    ctxt.cw.flush();
	} 
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
		w.flush();
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
