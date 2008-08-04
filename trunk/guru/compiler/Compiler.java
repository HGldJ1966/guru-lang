package guru.compiler;

import guru.*;
import java.util.*;
import java.io.*;

public class Compiler {

    // set by compile()
    PrintStream os;
    File root;

    boolean dbg, dbg_emit, dbg_emit_details;

    int abortnum;

    Const stdintp;
    Const next_char;
    Const print_char;
    Const booltp;
    Const chartp;
    Const mkchar;
    Const eqchar;
    Const nattp;

    Const cur_fun;
    Var[] cur_fun_vars;

    HashMap type_names;

    public Compiler() { 
	cur_fun = null;
    }

    public void handleError(Context ctxt, Position p, String msg) {
	if (p != null)
	    System.out.print(p.toString() + ": c");
	else
	    System.out.print("C");
		
	System.out.println("ompiler error.\n"+msg);
	ctxt.printDefEqErrorIf();
	System.exit(6);
    }

    protected String name(String n) {
	int iend = n.length() + 1;
	char[] buf = new char[iend];
	buf[0] = 'g';
	for (int i = 1; i < iend; i++) {
	    char c = n.charAt(i-1);
	    if (c <= 47) 
		c += 65;
	    else if (c >= 58 && c <= 64)
		c += 97-58;
	    if ((c >= 91 && c <= 94) || c == 96)
		c += 104-91;
	    else if (c >= 123)
		c -= 4;
	    buf[i] = c;
	}
	return new String(buf);
    }

    protected void emitname(String n) {
	os.print(name(n));
    }

    protected void nl() {
	os.println("");
    }

    protected void emitNoopIncDec(PrintStream os, String n) {
	n = name(n);
	os.print("#define inc_");
	os.print(n);
	os.println("(x) ");
	nl();
	
	os.print("#define dec_");
	os.print(n);
	os.println("(x) ");
	nl();

	os.print("void *pinc_");
	os.print(n);
	os.println("(void *x) { return x; }");
	nl();
	
	os.print("void pdec_");
	os.print(n);
	os.println("(void *x) { }");
	nl();
    }

    protected void emitFlatInductive(Context ctxt, Const d) {
	os.print("typedef char ");
	emitname(d.name);
	os.println(";");
	nl();
	os.print("#define getop_");
	emitname(d.name);
	os.println("(x) x");
	nl();

	emitNoopIncDec(os, d.name);

	Iterator it = ctxt.getTermCtors(d).iterator();

	while (it.hasNext()) {
	    Const c = (Const)it.next();
	    
	    os.print("#define ");
	    emitname(c.name);
	    os.print("() ");

	    os.print(ctxt.getWhichTermCtor(c).toString());
	    os.println("");
	    os.println("");
	}
    }

    protected String argname(int which) {
	return "arg"+(new Integer(which)).toString();
    }
    protected void emitarg(int which) {
	os.print(argname(which));
    }
	

    // assuming T is either a Const or a TypeApp, return its head.
    protected Const headType(Expr T) {
	if (T.construct == Expr.CONST)
	    return (Const)T;
	return headType(((TypeApp)T).head);
    }


    protected void emitIncDefinedToPinc(boolean do_inc, String name) {
	String w = do_inc ? "inc" : "dec";
	os.print("#define "+w+"_");
	emitname(name);
	os.print("(x) p"+w+"_");
	emitname(name);
	os.println("(x)");
	nl();
    }

    protected void emitAddToFreeList(Const c, String x, boolean must_clear) {
	String freelist = name(c.name)+"_free";
	
	os.println("  "+x+"->op = (int)"+freelist+";");
	os.print("  "+freelist+" = (("+name(c.name)+"_struct *)");
	
	if (must_clear)
	    os.print("((int)"+x+" | 1)");
	else
	    os.print(x);
	os.println(");");
    }

    protected void emitInductive(Context ctxt, Const d, String which) {

	if (ctxt.numTermCtors(d) > 256)
	    handleError(ctxt, d.pos,
			"Compilation is restricted to datatypes with <= 256"
			+" constructors.");

	// emit typedef for the core struct
	os.println("/*****************************************************");
	os.println(" * Type definitions for datatype "+d.name);
	os.println(" *   ");
	os.println(" * Type name is "+which);
	os.println(" *****************************************************/");
	nl();
	os.print("#define type_name_"+name(d.name)+" "+which);
	nl();

	if (ctxt.isFlat(d)) {
	    emitFlatInductive(ctxt,d);
	    return;
	}

	// emit macro to get the operator
	os.print("#define getop_");
	emitname(d.name);
	os.println("(x) (x->op & 255)");
	nl();

	// emit typedef for the type to use in code
	os.print("typedef ");
	emitname("core");
	os.print(" *");
	emitname(d.name);
	os.println(";");
	nl();

	// emit the inc functions

	os.print("inline void *pinc_");
	emitname(d.name);
	os.println("(void *x) { ");
	os.println("  inc_core(x);");
	os.println("  return x;");
	os.println("}");
	nl();

	emitIncDefinedToPinc(true, d.name);

	Iterator it = ctxt.getTermCtors(d).iterator();
	while (it.hasNext()) {

	    // emit type and free list for each constructor

	    Const c = (Const)it.next();

	    os.print("typedef struct ");
	    String c_struct = c.name + "_struct";
	    emitname(c_struct);
	    os.println(" {");
	    os.print("  ");
	    emitname("core");
	    os.println(" core;");
	    /* the call to defExpandTop is needed because flattenTypes
	       has replaced the original Fun-types with uses of
	       defined Consts. */
	    Expr T = ctxt.getClassifier(c).defExpandTop(ctxt);
	    int ar_c = ctxt.getArity(c);
	    Expr cur = T;
	    for (int i = 0; i < ar_c; i++) {
		FunType f = (FunType)cur;
		os.print("  ");
		compileType(ctxt,f.types[0]);
		os.print(" ");
		emitarg(i);
		os.println(";");
		cur = f.next();
	    }
		
	    os.print("} ");
	    emitname(c_struct);
	    os.println(";");
	    nl();

	    // declare free list
	    String freelist = name(c.name)+"_free";
	    emitname(c_struct);
	    os.print(" *");
	    os.println(freelist+" = 0;");
	    nl();
	}

	// emit dec code
	os.print("inline void pdec_");
	emitname(d.name);
	os.print("(void *_x) {");
	String tmp = name(d.name);
	os.println("  "+tmp+ " x = ("+tmp+") _x;");
	os.println("  dec_core(x);");
        os.println("  if (x->op < 256) {");
	os.print("  switch (getop_");
	emitname(d.name);
	os.println("(x)){");
	it = ctxt.getTermCtors(d).iterator();
	while (it.hasNext()) {
	    // emit code to put x on the appropriate free list.
	    Const c = (Const)it.next();

	    os.print("  case ");
	    int i = ctxt.getWhichTermCtor(c).intValue();
	    os.print((new Integer(i)).toString());
	    os.println(": {");
	    emitAddToFreeList(c,"x",true /* must clear */);
	    os.println("  break;");
	    os.println("  }");
	}
	os.println("  }");
	os.println("  }");
	os.println("}");
	nl();

	emitIncDefinedToPinc(false, d.name);

	it = ctxt.getTermCtors(d).iterator();
	while (it.hasNext()) {

	    // emit code for each constructor

	    Const c = (Const)it.next();

	    // emit code to clear a node
	    
	    String c_struct = c.name + "_struct";

	    os.print("inline void ");
	    emitname(c.name);
	    os.print("_clear(");
	    emitname(c_struct);
	    os.println(" *x) {");
	    Expr cT = ctxt.getClassifier(c);
	    if (cT.construct == Expr.FUN_TYPE) {
		FunType F = (FunType)cT;
		
		int jend =  F.vars.length;

		// first declare type variables
		for (int j = 0; j < jend; j++) {
		    Var v = F.vars[j];
		    Expr T = ctxt.getClassifier(v);
		    if (T.construct == Expr.TYPE) {
			/* add a definition for this one since we may
			   use it later */
			os.print("  "+name("type")+" "+name(v.name));
			os.println(" = x->"+argname(j)+";");
		    }
		}
		
		// now emit calls to dec.
		for (int j = 0; j < jend; j++) {
		    Var v = F.vars[j];
		    Expr T = ctxt.getClassifier(v);
		    if (!T.isTrackedType(ctxt))
			continue;
		    emitCallDec(T, "x->"+argname(j));
		}
	    }
	    os.println("}");
	    nl();

	    // emit code for constructor
	    emitname(d.name);
	    os.print(" ");
	    emitname(c.name);
	    
	    if (cT.construct == Expr.FUN_TYPE) 
		print_args(ctxt, (FunType)cT, true);
	    else
		os.print("()");
	    
	    String freelist = name(c.name)+"_free";

	    os.println(" {");
	    os.print("  ");
	    emitname(c_struct);
	    os.println(" *ret;");
	    os.println(" int do_clear;");
	    os.println("  if ("+freelist+") {");
	    os.println("    ret = "+freelist+";");
            os.println("    do_clear = ((int)ret) & 1;");
	    os.println("    if (do_clear)");
	    os.println("      ret = ("+name(c_struct)+" *)((int)ret & ~1);");
	    

	    /* it is critical that we update the free list before
	       we clear ret (if we will clear it), because clearing
	       can add things to the free list. */

	    os.println("    "+freelist
		       +" = ("+name(c_struct)+" *)ret->core.op;");
	    os.println("    if (do_clear) ");
	    os.println("      "+name(c.name)+"_clear(ret);");
	    os.println("  }");
	    os.println("  else");
	    os.print("    ret = (");
	    emitname(c_struct);
	    os.print(" *)guru_alloc(sizeof(");
	    emitname(c_struct);
	    os.println("));");
	    os.print("  ret->core.op = 256 + ");
	    os.print(ctxt.getWhichTermCtor(c).toString());
	    os.println(";");
	    int ar_c = ctxt.getArity(c);
	    for (int i = 0; i < ar_c; i++) {
		os.print("  ret->");
		emitarg(i);
		os.print(" = ");
		emitarg(i);
		os.println(";");
	    }
	    os.print("  return (");
	    emitname(d.name);
	    os.println(") ret;");
	    os.println("}");
	    nl();
	} // end for each term constructor
    }

    /* free variable with (emitted) name x, known to be built from term
       ctor c. */
    protected void emitCallFree(Const c, String x) {
	String freelist = name(c.name)+"_free";
	os.println("  "+x+"->op = (int)"+freelist+";");
	os.println("  "+freelist+" = ("+name(c.name)+"_struct *)"+x+";");
	//os.println("  free("+x+");");
    }	

    protected void emitCallDec(Expr T, String x) {
	if (T.construct == Expr.VAR)
	    os.println("  polydec["+name(((Var)T).name) +"]("+x+");");
	//os.println("  polydec("+name(((Var)T).name) +", "+x+");");
	else {
	    Const c = headType(T);
	    os.print("  dec_");
	    emitname(c.name);
	    os.println("("+x+");");
	}
    }

    /* assuming T is a tracked type (including a variable), emit code
       to inc x of that type. */
    protected void emitCallInc(Expr T, String x, boolean mk_stmt) {
	if (mk_stmt)
	    os.print("  ");
	else
	    os.print("(");
	if (T.construct == Expr.VAR) {
	    Var v = (Var)T;
	    os.print("polyinc["+name(v.name)+"]("+x+")");
	    //os.print("polyinc("+name(v.name)+", "+x+")");
	}
	else {
	    Const c = (Const)headType(T);
	    if (!mk_stmt)
		os.print("("+name(c.name)+") ");
	    os.print("inc_"+name(c.name)+"("+x+")");
	}
	if (mk_stmt)
	    os.print(";");
	else
	    os.print(")");
    }

    // c should be a defined type constant
    protected void emitTypeDef(Context ctxt, Const c, String which) {
	Expr T = ctxt.getDefBody(c);/*.defExpandTop(ctxt);*/
	os.println("/*****************************************************");
	os.println(" * Type definition of "+c.name);
	os.println(" *   ");
	os.println(" * Type name is "+which);
	os.println(" *****************************************************/");
	nl();
	os.print("#define type_name_"+name(c.name)+" "+which);
	nl();
	os.print("typedef ");
	if (T.construct == Expr.FUN_TYPE) {
	    FunType f = (FunType)T;
	    compileType(ctxt, f.body);
	    os.print(" (*");
	    emitname(c.name);
	    os.print(")(");
	    for (int i = 0, iend = f.types.length; i < iend; i++) {
		if (i > 0)
		    os.print(", ");
		compileType(ctxt, f.types[i]);
	    }
	    os.println(");");
	}
	else {
	    String s = compileTypeStr(ctxt, T);
	    os.print(s+" ");
	    emitname(c.name);
	    os.println(";");
	    nl();

	    os.print("#define getop_");
	    emitname(c.name);
	    os.println(" getop_"+s+"");
	}
	nl();
	
	// emit pdec and pinc functions

	if (T.isTrackedType(ctxt)) {
	    os.print("void *pinc_");
	    emitname(c.name);
	    os.print("(void *x) { return ");
	    emitCallInc(T, "x", true);
	    os.println(" }");
	    nl();
	    
	    os.print("void pdec_");
	    emitname(c.name);
	    os.print("(void *x) { ");
	    emitCallDec(T, "x");
	    os.println(" }");
	    nl();

	    emitIncDefinedToPinc(true, c.name);
	    emitIncDefinedToPinc(false, c.name);
	}
	else 
	    emitNoopIncDec(os, c.name);

    }

    protected void print_args(Context ctxt, Expr[] X, Expr[] types,
			      Ownership[] owned,
			      boolean at_call) {
	int printed = 0;
	os.print("(");
	for (int i = 0, iend = X.length; i < iend; i++) {
	    /* spec args handled in EtaExpand now: 
	    if (owned[i].status == Ownership.SPEC)
	    continue; */
	    if (printed++ > 0)
		os.print(", ");
	    if (at_call)
		os.print("(");
	    compileType(ctxt, types[i]);
	    if (at_call)
		os.print(")");
	    else
		os.print(" ");
	    if (X[i].construct == Expr.CAST) 
		// just avoid printing two casts
		compile(ctxt, ((Cast)X[i]).t, null, false);
	    else
		compile(ctxt, X[i], null, false);
	}
	os.print(")");
    }

    protected void print_args(Context ctxt, FunType T, boolean anon) {
	os.print("(");
	int ar = T.getArity();
	FunType cur = T;
	for (int i = 0; i < ar; i++) {
	    if (i > 0)
		os.print(", ");
	    compileType(ctxt, cur.types[0]);
	    os.print(" ");
	    if (anon)
		emitarg(i);
	    else
		emitname(cur.vars[0].name);
	    if (i < ar-1)
		cur = (FunType)cur.next();
	}
	os.print(")");
    }

    protected void introduceCase(Context ctxt, String scrut_name, 
				 Const c, Var[] vars, boolean consume) {
	os.print("  case ");
	int which = ctxt.getWhichTermCtor(c).intValue();
	os.print((new Integer(which)).toString());
	os.print(": { /* ");
	os.print(c.name);
	int jend = vars.length;
	for (int j = 0; j < jend; j++)
	    os.print(" "+vars[j].name);
	os.println(" */");
	for (int j = 0; j < jend; j++) {
	    os.print("  ");
	    Var v = vars[j];
	    Expr T = ctxt.getClassifier(v);
	    if (dbg_emit_details) {
		ctxt.w.println("Introducing pattern variable "
			       +v.toString(ctxt)+" : "
			       + T.toString(ctxt));
		ctxt.w.flush();
	    }
	    compileType(ctxt, T);
	    os.print(" ");
	    emitname(v.name);
	    os.print(" = ((");
	    emitname(c.name+"_struct");
	    os.print(" *) ");
	    os.print(scrut_name);
	    os.print(")->");
	    emitarg(j);
	    os.println(";");
	}
	if (consume) {
	    os.println("  if (((" + name("core") + " *)"
		       +scrut_name+")->op < 512) {");
	    emitAddToFreeList(c, scrut_name, false /* must clear */);
	    os.println("  }");
	    os.println("  else {");
	    os.println("  dec_core(("+name("core")+" *)"+scrut_name+");");
	    for (int j = 0; j < jend; j++) {
		Var v = vars[j];
		Expr T = ctxt.getClassifier(v);
		if (v.isTypeOrKind(ctxt) || v.isProof(ctxt))
		    continue;
		emitCallInc(T, name(v.name), true);
		nl();
	    }
	    os.println("  }");
	    nl();
	}
    }

    protected void compile(Context ctxt, Expr t, String return_str,
			   boolean returning) {
	if (dbg_emit_details) {
	    ctxt.w.println("Emitting term: { "+t.toString(ctxt) + " : " 
			   + (t.classify(ctxt,Expr.APPROX_TRIVIAL,false)
			      .toString(ctxt)));
	    ctxt.w.flush();
	}
	switch (t.construct) {
	case Expr.TERM_APP: {
	    TermApp a = (TermApp)t;
	    Expr h = a.head;
	    FunType Th = (FunType)(h.classify(ctxt,Expr.APPROX_TRIVIAL,false)
				   .defExpandTop(ctxt,false,false));
	    if (return_str != null) {
		if (returning && cur_fun != null && a.head == cur_fun) {
		    // this is a tail call
		    int iend = cur_fun_vars.length;
		    if (a.X.length != iend)
			handleError(ctxt, t.pos,
				    "Internal compiler error: a (tail) call"
				    +" is made with the wrong number of args."
				    +"\n1. the call: "+a.toString(ctxt));
		    // emit assignments to args
		    for (int i = 0; i < iend; i++) {
			/* spec args handled in EtaExpand now:
			   if (Th.owned[i].status == Ownership.SPEC)
			  continue; */
			emitname(cur_fun_vars[i].name);
			os.print(" = ");
			compile(ctxt, a.X[i], null, false);
			os.println(";");
		    }
		    os.print("  goto ");
		    emitname(cur_fun.name + "_start");
		    os.println(";");
		    break; // out of switch
		}
		os.print(return_str);
	    }

	    compile(ctxt, a.head, null, false);
	    print_args(ctxt, a.X, Th.types, Th.owned, true /* at call */);
	    if (return_str != null)
		os.println(";");
	    break;
	}
	case Expr.LET: {
	    Let l = (Let)t;
	    String v = name(l.x1.name);
	    os.println("  {");
	    // should be a Const, thanks to FlattenTypes
	    String Tstr = compileTypeStr(ctxt, ctxt.getClassifier(l.x1));

	    // declare the let-bound variable
	    os.println("  " + Tstr + " " + v + ";");

	    String s = v + " = ";
	    compile(ctxt, l.t1, s, false);
	    compile(ctxt, l.t2, return_str, returning);
	    os.println("  } // let "+v);
	    break;
	}
	case Expr.MATCH: {
	    Match m = (Match)t;
	    
	    /* we need to consume the scrutinized cell if CheckRefs
	       identified that it is unowned at this point. */

	    boolean consume = (m.scrut_stat.status == Ownership.UNOWNED
			       || m.scrut_stat.status == Ownership.UNIQUE);
	    
	    if (dbg_emit_details) {
		ctxt.w.println("Scrutinee's status in this match-term is: "
			       +m.scrut_stat.toString(ctxt));
		ctxt.w.flush();
	    }

	    // ensured by AddLets
	    Var scrut = (Var)m.t;
	    Expr T = ctxt.getClassifier(scrut);

	    os.print("  switch (getop_");
	    compileType(ctxt,T);
	    os.print("(");
	    emitname(scrut.name);
	    os.println(")) {");

	    Case[] C = m.C;
	    for (int i = 0, iend = C.length; i < iend; i++) {
		Case aC = C[i];

		introduceCase(ctxt, name(scrut.name), aC.c, aC.x,
			      consume);

		compile(ctxt,aC.body,return_str,returning);
		os.println("  break;");
		os.println("  }");
	    }
	    os.println("  default: fprintf(stderr,\"Aborting "
		       +(new Integer(abortnum++)).toString()
		       +"\\n\"); exit(1);");
	    os.println("} /* end switch */");
	    break;
	}
	case Expr.CONST: {
	    Const c = (Const)t;
	    if (return_str != null)
		os.print(return_str);
	    if (c.isTypeOrKind(ctxt))
		os.print(typeName(ctxt,t));
	    else {
		emitname(c.name);
		if (ctxt.isTermCtor(c) && ctxt.getArity(c) == 0)
		    os.print("()");
	    }
	    if (return_str != null)
		os.println(";");
	    break;
	}
	case Expr.VAR: {
	    if (return_str != null)
		os.print(return_str);
	    if (t.isProof(ctxt))
		emitname("bang");
	    else
		emitname(((Var)t).name);
	    if (return_str != null)
		os.println(";");
	    break;
	}
	case Expr.STRING_EXPR: {
	    StringExpr s = (StringExpr)t;
	    compile(ctxt, s.expand(ctxt), return_str, returning);
	    break;
	}
	case Expr.INC: {
	    Inc i = (Inc)t;
	    Var v = (Var)i.t; // guaranteed by AddLets
	    if (return_str != null)
		os.print(return_str);
	    emitCallInc(ctxt.getClassifier(v), name(v.name), false);
	    if (return_str != null)
		os.println(";");
	    break;
	}
	case Expr.DEC: {
	    Dec d = (Dec)t;
	    Var v = (Var)d.I; // guaranteed by AddLets
	    emitCallDec(ctxt.getClassifier(v), name(v.name));
	    os.println("");
	    compile(ctxt,d.t,return_str,returning);
	    break;
	}
	case Expr.CAST: {
	    Cast e = (Cast)t;
	    if (return_str != null) {
		return_str = (return_str + " (" 
			      + compileTypeStr(ctxt,e.T) + ")");
		compile(ctxt,e.t,return_str,returning);
	    }
	    else {
		os.print("((");
		compileType(ctxt,e.T);
		os.print(")");
		compile(ctxt,e.t,return_str,returning);
		os.print(")");
	    }
	    break;
	}
	case Expr.ABORT: {
	    Abort a = (Abort)t;
	    os.println("  fprintf(stdout,\"abort\\n\"); exit(1);\n");
	    os.print("  return ((");
	    compileType(ctxt,a.T);
	    os.println(")0);");
	    break;
	}
	default:
	    // we expect this to be an annotation which we will drop
	    if (return_str != null)
		os.print(return_str);
	    if (t.isTypeOrKind(ctxt))
		os.print(typeName(ctxt, t));
	    else
		emitname("bang");
	    if (return_str != null)
		os.println(";");
	    break;
	}
	if (dbg_emit_details) {
	    ctxt.w.println("}");
	    ctxt.w.flush();
	}
    }

    protected String typeName(Context ctxt, Expr T) {
	switch (T.construct) {
	case Expr.FUN_TYPE:
	    handleError(ctxt, T.pos,
			"Internal error: encountered a Fun-type in an "
			+"unexpected position.");
	    break;
	case Expr.CONST:
	    return (String)type_names.get(((Const)T).name);
	case Expr.VAR:
	    return name(((Var)T).name);
	case Expr.TYPE:
	    return name("type");
	case Expr.TYPE_APP:
	    return typeName(ctxt,((TypeApp)T).head);
	default:
	    handleError(ctxt, T.pos,
			"Internal error: unexpected type construct in a"
			+" term.\n"
			+"1. the putative type: "+T.toString(ctxt));
	}
	return null; // should not be reached
    }

    protected String compileTypeStr(Context ctxt, Expr T) {
	switch (T.construct) {
	case Expr.FUN_TYPE:
	    handleError(ctxt, T.pos,
			"Internal error: encountered a Fun-type in an "
			+"unexpected position.\n"
			+"1. the type: "+T.toString(ctxt));
	    break;
	case Expr.CONST:
	    return name(((Const)T).name);
	case Expr.VAR:
	    /*	    if (ctxt.isMacroDefined((Var)T))
	      return compileTypeStr(ctxt,ctxt.getDefBody((Var)T)); */
	    return "void *";
	case Expr.TYPE:
	    return name("type");
	case Expr.TYPE_APP:
	    return compileTypeStr(ctxt,((TypeApp)T).head);
	default:
	    // we expect this to be a formula
	    return name("proof");
	}
	return null; // should not be reached
    }

    protected void compileType(Context ctxt, Expr T) {
	os.print(compileTypeStr(ctxt,T));
    }

    protected void compileFun(Context ctxt, Define D) {
	FunTerm f = (FunTerm)D.G;

	FunType ftp = (FunType)(f.classify(ctxt,Expr.APPROX_TRIVIAL,false)
				.defExpandTop(ctxt,false,false));
	compileType(ctxt,ftp.body);
	os.print(" ");
	emitname(D.c.name);
	print_args(ctxt, f.vars, f.types, f.owned, false /* at call */);
	os.println(" {");
	Expr body = f.body;
	if (f.r != null) {
	    body = body.subst(D.c,f.r);
	    cur_fun = D.c; 
	    cur_fun_vars = f.vars;
	    emitname(cur_fun.name+"_start");
	    os.println(": {");
	}
	else
	    cur_fun = null;
	/*if (dbg) {
	    ctxt.w.println("Compiling body of "+D.c.name);
	    ctxt.w.flush();
	    }*/
	compile(ctxt,body, "  return ",true);
	if (cur_fun != null)
	    os.println("}");
	os.println("}");
	os.println("");
    }

    protected void printContext(String msg, Context ctxt) {
	ctxt.w.println("% ---------------------------------");
	ctxt.w.print("% ");
	ctxt.w.println(msg);
	ctxt.w.println("");
	Iterator it = ctxt.getTypeCtors().iterator();
	while(it.hasNext()) {
	    Const c = (Const)it.next();
	    ctxt.w.println("Inductive type: "+c.toString(ctxt));
	}

        it = ctxt.getDefinedConsts().iterator();
	while(it.hasNext()) {
	    Const c = (Const)it.next();
	    
	    Expr body = (ctxt.isOpaque(c) ? c : ctxt.getDefBody(c));
	    
	    Expr T = ctxt.getClassifier(c);
	    
	    Define D = new Define(ctxt.isOpaque(c), ctxt.isTrusted(c),
				  ctxt.isTypeFamilyAbbrev(c),
				  ctxt.isPredicate(c),
				  c, T, body, body.dropAnnos(ctxt));
	    
	    D.print(ctxt.w, ctxt);
	}
	ctxt.w.print("% end of ");
	ctxt.w.println(msg);
	ctxt.w.println("");

	ctxt.w.flush();
    }

    protected void copyTypeDefs(Context src, Context dst) {
	Iterator it = src.getDefinedConsts().iterator();
	while (it.hasNext()) {
	    Const c = (Const)it.next();
	    Expr T = src.getDefBody(c);
	    if (T.isTypeOrKind(src) || src.isTypeFamilyAbbrev(c) ||
		src.isPredicate(c)) {
		dst.define(c,src.getClassifier(c),T,T.dropAnnos(dst));
		if (src.isOpaque(c))
		    dst.makeOpaque(c);
		if (src.isTypeFamilyAbbrev(c))
		    dst.markTypeFamilyAbbrev(c);
		if (src.isPredicate(c))
		    dst.markPredicate(c);
		if (src.isUntracked(c)) 
		    dst.makeUntracked(c);
	    }
	}
    }

    protected String stubFileName(Const c) {
	return "stub/" + name(c.name) + ".h";
    }

    protected void emitStubInclude(Context ctxt, Const c) {
	if (dbg) {
	    ctxt.w.print("Emitting stub for ");
	    c.print(ctxt.w,ctxt);
	    ctxt.w.println("");
	    ctxt.w.flush();
	}

	os.print("#include \"");
	os.print(stubFileName(c));
	os.println("\"\n");
    }

    protected PrintStream openStubFile(Context ctxt, Const c) {
	File f = new File(root.getAbsolutePath() + "/" + stubFileName(c));

	try {
	    return new PrintStream(new FileOutputStream(f));
	}
	catch (IOException e) {
	    e.printStackTrace();
	    handleError(ctxt, null, "Problem opening stub file for writing:\n"
			+ e.getMessage());
	}
	return null;
    }

    protected void emitStubStdintp(Context ctxt) {
	PrintStream ss = openStubFile(ctxt, stdintp);
	
	String stp = stdintp.name;

	ss.print("typedef int ");
	ss.print(name(stp));
	ss.println(";\n");

	emitNoopIncDec(ss, stp);

	ss.close();
    }

    protected void emitStubChartp(Context ctxt) {
	PrintStream ss = openStubFile(ctxt, chartp);
	
	String stp = chartp.name;

	ss.print("typedef char ");
	ss.print(name(stp));
	ss.println(";\n");

	emitNoopIncDec(ss, stp);

	ss.close();
    }

    protected void emitStubMkchar(Context ctxt) {
	PrintStream ss = openStubFile(ctxt, mkchar);
	
	String stp = mkchar.name;

	ss.print(name(chartp.name));
	ss.print(" ");
	ss.print(name(stp));
	String gbool = name(booltp.name);
	ss.print("(");
	for (int i = 6; i >= 0; i--) {
	    if (i != 6)
		ss.print(", ");
	    ss.print(gbool + " b"+(new Integer(i)).toString());
	}
	ss.println(") {");
	ss.print("  return ");
	for (int i = 0; i < 7; i++) {
	    if (i != 0)
		ss.print(" | ");
	    String istr = (new Integer(i)).toString();
	    ss.print("(b"+istr+" << "+istr+")");
	}
	ss.println(";");
	ss.println("}");
	ss.println("");
    }


    protected void emitStubEqchar(Context ctxt) {
	PrintStream ss = openStubFile(ctxt, eqchar);

	ss.print(name(booltp.name));
	ss.print(" ");
	ss.print(name(eqchar.name));
	ss.print("(");
	ss.print(name(chartp.name));
	ss.print(" c1,");
	ss.print(name(chartp.name));
	ss.println(" c2) {");
	ss.println("  return (c1 == c2);");
	ss.println("}");
    }

    protected void emitStubNextchar(Context ctxt) {
	PrintStream ss = openStubFile(ctxt, next_char);
	String Stdintp = name(stdintp.name);

	String gct = name("getc_t");
	ss.print(gct);
	ss.print(" ");
	ss.print(name(next_char.name));
	ss.println("("+Stdintp+" in) {");                    //, "+gct+" c
	ss.println("  char c = fgetc_unlocked(stdin);");
	ss.println("  if (c == EOF)  ");
        ss.println("    return "+name("getc_none")+"();");
	ss.println("  else");
	ss.println("    return ggetc_char(c & 127, in);");
	ss.println("}\n");

	ss.close();
    }

    protected void emitStubPrintchar(Context ctxt) {
	PrintStream ss = openStubFile(ctxt, print_char);
	String charstr = name("char");

	ss.print(charstr);
	ss.print(" ");
	ss.print(name(print_char.name));
	ss.println("("+charstr+" c) {");
	ss.println("  fputc(c, stdout);");
	ss.println("}\n");
    }

    protected Const lookupStd(Context ctxt, String name) {
	Const tmp = (Const)ctxt.lookup(name);
	if (tmp == null)
	    handleError(ctxt, null,
			"Definition missing for the type \""+name+"\", "
			+"needed for compilation.");
	return tmp;
    }

    protected void emitInitPolyIncDec(Context ctxt) {
	Collection c = type_names.keySet();
	String csz = (new Integer(c.size())).toString();

	os.println("  polydec = (polydec_fun *)guru_alloc(sizeof(polydec_fun)*"
		   +csz+");");

	Iterator it = c.iterator();
	while (it.hasNext()) {
	    String tp = (String)it.next();
	    String num = (String)type_names.get(tp);
	    os.print("  polydec["+num+"] = pdec_");
	    emitname(tp);
	    os.println(";");
	}
	nl();

	os.println("  polyinc = (polyinc_fun *)guru_alloc(sizeof(polyinc_fun)*"
		   +csz+");");

	it = c.iterator();
	while (it.hasNext()) {
	    String tp = (String)it.next();
	    String num = (String)type_names.get(tp);
	    os.print("  polyinc["+num+"] = pinc_");
	    emitname(tp);
	    os.println(";");
	}
	nl();
    }

    public void compile(File root, 
			Context ctxt1, PrintStream os, Const cmain) {

	this.os = os;
	this.dbg = ctxt1.getFlag("Debug_compiler");
	this.dbg_emit = ctxt1.getFlag("debug_compiler_emit") || this.dbg;
	this.dbg_emit_details = ctxt1.getFlag("debug_compiler_emit_details");
	this.root = root;
	this.abortnum = 0;

	// find standard constants
	stdintp = lookupStd(ctxt1, "stdin_t");
	nattp = lookupStd(ctxt1, "nat");
	next_char = lookupStd(ctxt1, "next_char");
	print_char = lookupStd(ctxt1, "print_char");
	eqchar = lookupStd(ctxt1,"eqchar");
	chartp = lookupStd(ctxt1,"char");
	mkchar = lookupStd(ctxt1,"mkchar");
	booltp = lookupStd(ctxt1,"bool");

	/* make sure the type of cmain is correct. */

	Expr ctp = ctxt1.getClassifier(cmain);
	Expr req = new FunType(new Var("unused"),stdintp,
			       new Ownership(Ownership.UNIQUE), 
			       new Ownership(Ownership.UNOWNED), nattp);
	if (!ctp.defEq(ctxt1, req))
	    handleError(ctxt1, cmain.pos,
			"The type for a program to compile is not "
			+ "definitionally equal"
			+" to\nthe required type for main programs."
			+"\n1. the given type: "+ctp.toString(ctxt1)
			+"\n2. the required type: "+req.toString(ctxt1));

	if (dbg) {
	    ctxt1.w.println("Compilation beginning.");
	    ctxt1.w.flush();
	}

	if (ctxt1.getFlag("compiler_print_initial_context"))
	    printContext("Initial context.", ctxt1);

	/*
	 * phase 1: eta-expand cmain, pulling in definitions from ctxt1
	 *          to ctxt2.
	 */ 

	if (dbg) {
	    ctxt1.w.println("Copying type defs.");
	    ctxt1.w.flush();
	}

	Context ctxt2 = new Context(ctxt1);
	ctxt2.clearDefs();
	ctxt2.clearCtors();

	if (dbg) {
	    ctxt1.w.println("Eta expanding.");
	    ctxt1.w.flush();
	}

	EtaExpand ee = new EtaExpand(ctxt1, ctxt2);
	Expr e2 = ee.expand(cmain);

	if (dbg)
	    printContext("After eta-expansion.", ctxt2);

	/*
	 * Check that we have no free variables after eta-expansion.
	 */

	Iterator it = ctxt2.getDefinedConsts().iterator();
	while(it.hasNext()) {
	    Const c = (Const)it.next();
	    Expr body = ctxt2.getDefBody(c);
	    Expr bodyno = ctxt2.getDefBodyNoAnnos(c);
	    Expr T = ctxt2.getClassifier(c);
	 
	    if (body.isTypeOrKind(ctxt2) || ctxt2.isOpaque(c))
		// we have already emitted the type definitions.
		continue;

	    HashSet h = new HashSet();
	    body.getFreeVarsComputational(ctxt2,h);

	    if (ctxt2.getFlag("debug_compiler_free_vars")) {
		ctxt2.w.print("Free variables (no annos) for "
			      +c.toString(ctxt2)+":");
		Iterator it2 = h.iterator();
		while(it2.hasNext()) {
		    Expr v = (Expr)it2.next();
		    ctxt2.w.print(" ");
		    v.print(ctxt2.w,ctxt2);
		}
		ctxt2.w.println("");
		ctxt2.w.flush();
	    }

	    Define D = new Define(false,false,false,false,c,null,body,bodyno);
	    if (h.size() > 0) {
		Iterator hit = h.iterator();
		handleError(ctxt2, body.pos,
			    "After eta-expansion, a top-level function "
			    +"contains free variables.\n"
			    +"(Note that they could be arising from inc"
			    +" or dec, in which case\nthey will not be "
			    +"printed below.)\n"
			    +"\n1. the function: "+c.toString(ctxt2)
			    +"\n2. a free variable: "
			    +((Var)hit.next()).toString(ctxt2)
			    +"\n3. the function's definition:\n"
			    +D.toString(ctxt2));
	    }
	}

	/*
	 * phase 2: split applications by arity, so we can cast them
	 *          properly.
	 */

	if (dbg) {
	    ctxt2.w.println("Splitting by arity.");
	    ctxt2.w.flush();
	}

	Context ctxt3 = new Context(ctxt2);
	ctxt3.clearDefs();
	SplitByArity sba = new SplitByArity();
	sba.process(ctxt2,ctxt3);
	
	if (dbg)
	    printContext("After splitting applications by arity.", ctxt3);

	/*
	 * check reference usage (does not modify ctxt3)
	 */

	if (dbg) {
	    ctxt3.w.println("Starting reference checking.");
	    ctxt3.w.flush();
	}


	CheckRefs cr = new CheckRefs();
	cr.checkRefs(ctxt3);

	if (dbg) {
	    ctxt3.w.println("Reference checking successful.");
	    ctxt3.w.flush();
	    printContext("After reference checking.", ctxt3);
	}

	/*
	 * phase 3: add let-terms as needed for nested matches and such,
	 *          and pull them to return positions.
	 */

	Context ctxt4 = new Context(ctxt3);
	ctxt4.clearDefs();
	AddLets al = new AddLets();
	al.process(ctxt3,ctxt4);

	if (dbg)
	    printContext("After adding let-terms.", ctxt4);

	/*
	 * phase 4: uniquify vars.
	 */

	Context ctxt5 = new Context(ctxt4); // do not clear defs.
	UniquifyVars uv = new UniquifyVars();
	uv.process(ctxt5);
	
	if (dbg)
	    printContext("After uniquifying vars.", ctxt5);

	/*
	 * phase 5: flatten types.
	 */

	Context ctxt6 = new Context(ctxt5);
	ctxt6.clearDefs();
	FlattenTypes ft = new FlattenTypes();
	ft.process(ctxt5,ctxt6);

	if (dbg) {
	    printContext("After flattening types.", ctxt6);
	    
	    ctxt6.w.println("Inductive types:");
	    it = ctxt6.getTypeCtors().iterator();
	    while(it.hasNext()) {
		Const d = (Const)it.next();
		ctxt6.w.println(d.toString(ctxt6)+": ");
		Iterator it2 = ctxt6.getTermCtors(d).iterator();
		while (it2.hasNext()) {
		    Const c = (Const)it2.next();
		    Expr T = ctxt6.getClassifier(c);
		    ctxt6.w.println("  "+c.toString(ctxt6)+" : "
				    +T.toString(ctxt6));
		}
	    }
	}

	Context ctxt = ctxt6; // whichever is the last context
	Collection types = ft.getTypes(); // the types to emit.

	if (dbg) {
	    ctxt.w.println("% ------------------------------------");
	    ctxt.w.println("% Types from flattening.\n");
	    it = types.iterator();
	    while(it.hasNext()) {
		Const d = (Const)it.next();

		Expr body = ctxt.getDefBody(d);
		if (body == null)
		    ctxt.w.println(d.name);
		else {
		    Define D = new Define(false, false, false, false,
					  d, ctxt.getClassifier(d), 
					  body, ctxt.getDefBodyNoAnnos(d));
		    D.print(ctxt.w, ctxt);
		}
		ctxt.w.flush();
	    }
	    ctxt.w.println("% End types from flattening.\n");
	}

	/*
	 * Now emit code.
	 */

	os.println("#include <stdio.h>");
	os.println("#include <stdlib.h>");
	os.println("#include <signal.h>");
	nl();

	// emit guru allocator code

	os.println("char *guru_mem_start = 0;");
	os.println("char *guru_mem_end = 0;");
	
	os.println("inline char *guru_alloc(int numchars) {");
	os.println("  char *ret;");
	os.println("  if (guru_mem_end - guru_mem_start < numchars) ");
	os.println("     brk((guru_mem_end = guru_mem_end + 16384));");
	os.println("  ret = guru_mem_start;");
	os.println("  guru_mem_start += numchars;");
	os.println("  return ret;");
	os.println("}");
	//os.println("#define guru_alloc(x) malloc(x)");
	nl();
	
	/*
	 * emit special global types
	 */

	os.print("typedef int ");
	emitname("type");
	os.println(";");
	nl();

	os.print("typedef char ");
	emitname("proof");
	os.println(";");
	nl();

	emitname("proof");
	os.print(" ");
	emitname("bang");
	os.println(" = 0;");
	nl();

	os.print("typedef struct ");
	emitname("core");
	os.println(" {");
	os.println("  int op;");
	os.print("} ");
	emitname("core");
	os.println(";");
	nl();

	os.println("inline void inc_core("+name("core")+" *x) {");
	os.println("  x->op = x->op + 256;");
	os.println("}");
	nl();

	os.println("inline void dec_core("+name("core")+" *x) {");
	os.println("  x->op = x->op - 256;");
	os.println("}");
	nl();

	// forward declarations of polydec and polyinc function table
	os.println("typedef void(*polydec_fun)(void *);");
	nl();
	os.println("polydec_fun* polydec;"); 
	nl();
	os.println("typedef void *(*polyinc_fun)(void *);");
	nl();
	os.println("polyinc_fun* polyinc;"); 


	/* forward declarations of polydec and polyinc
	os.println("void polydec("+name("type")+", void *);");
	os.println("void *polyinc("+name("type")+", void *);");
	nl(); */


	/*
	 * emit user datatypes and defined types, and populate type_names table
	 */

	if (dbg_emit) {
	    ctxt.w.println("% ------------------------------------");
	    ctxt.w.println("% Emitting types.\n");
	    ctxt.w.flush();
	}

	it = types.iterator();
	int typecnt = 0;
	type_names = new HashMap();

	while(it.hasNext()) {
	    Const d = (Const)it.next();

	    String s = (new Integer(typecnt++)).toString();
	    type_names.put(d.name, s);

	    if (ctxt.isOpaque(d)) {

		/* if (d == stdintp) 
		    emitStubStdintp(ctxt);
		else if (d == chartp) 
		  emitStubChartp(ctxt); */

		emitStubInclude(ctxt, d);
		os.println("#define type_name_"+name(d.name)+" "+s);
		nl();
		continue;
	    }

	    if (dbg_emit) {
		ctxt.w.println("Emitting: "+d.toString(ctxt));
		ctxt.w.flush();
	    }

	    if (ctxt.isTypeCtor(d))
		emitInductive(ctxt, d, s);
	    else
		emitTypeDef(ctxt, d, s);
	}

	// emit type defs for function types

	/*
	 * emit code
	 */

	if (dbg_emit) {
	    ctxt.w.println("% ------------------------------------");
	    ctxt.w.println("% Emitting code.\n");
	    ctxt.w.flush();
	}

	it = ctxt.getDefinedConsts().iterator();
	Vector to_init = new Vector();
	while(it.hasNext()) {
	    Const c = (Const)it.next();
	    Expr body = ctxt.getDefBody(c);
	    Expr T = ctxt.getClassifier(c);
	 
	    if (c.isTypeOrKind(ctxt) || ctxt.isTypeFamilyAbbrev(c))
		// we have already emitted the type definitions.
		continue;

	    if (ctxt.isOpaque(c)) {
		/*
		  if (c == next_char) 
		    emitStubNextchar(ctxt);
 		  else if (c == print_char) 
		    emitStubPrintchar(ctxt);
		  else if (c == eqchar) 
		    emitStubEqchar(ctxt);
		  else if (c == mkchar) 
		    emitStubMkchar(ctxt);
		*/
		emitStubInclude(ctxt,c);
		continue;
	    }

	    if (dbg_emit) {
		ctxt.w.println("Emitting: "+c.toString(ctxt));
		ctxt.w.flush();
	    }

	    Define D = new Define(false, false, false, false,
				  c, T, body, body.dropAnnos(ctxt));

	    if (D.G.construct == Expr.FUN_TERM)
		compileFun(ctxt,D);
	    else {
		compileType(ctxt, D.A);
		os.print(" ");
		emitname(D.c.name);
		os.println(";\n");
		to_init.add(D);
	    }		
	}

	if (false) {

	    /* emit code for polyinc, polydec */
	    
	    Collection c = type_names.keySet();
	    os.println("void polydec(int tp, void *x) {");
	    os.println("  switch(tp) {");
	    
	    it = c.iterator();
	    while (it.hasNext()) {
		String tp = (String)it.next();
		String num = (String)type_names.get(tp);
		os.print("  case "+num+": pdec_");
		emitname(tp);
		os.println("(x); return; ");
	    }
	    os.println("  exit(1); }");
	    os.println("}");
	    nl();
	    
	    os.println("void *polyinc(int tp, void *x) {");
	    os.println("  switch(tp) {");
	    
	    it = c.iterator();
	    while (it.hasNext()) {
		String tp = (String)it.next();
		String num = (String)type_names.get(tp);
		os.print("  case "+num+": return pinc_");
		emitname(tp);
		os.println("(x); ");
	    }
	    os.println("  exit(1); }");
	    os.println("}");
	    nl();
	} // if false

	/*
	 * emit code for main()
	 */

        os.println("void sighandler(int signum) {");
	os.println("  fprintf(stderr,\"\\nInterrupted.\\n\");");
	os.println("  exit(1);");
	os.println("}");
	nl();

	os.println("int main(int argn, char **argv) {");

	os.println("  signal(SIGINT, sighandler);");
        os.println("  guru_mem_start = guru_mem_end = (char *)sbrk(0);");
	nl();

	emitInitPolyIncDec(ctxt);

	it = to_init.iterator();
	while (it.hasNext()) {
	    Define D = (Define)it.next();
	    String return_str = "  " + name(D.c.name) + " = ";
	    compile(ctxt, D.G,return_str,false);
	}
	os.println("");

	os.print("  ");
	emitname(cmain.name);
	os.println("(1 /* dummy for stdin */);\n");

	os.println("  return 0;\n}\n");
    }
    
}

