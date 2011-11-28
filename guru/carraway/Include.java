package guru.carraway;

import guru.Position;
import guru.IncludeHelper;
import java.io.File;
import java.util.Hashtable;
import java.util.Collection;
import java.util.Iterator;

public class Include {
    public static int MAX_RELEASE_CALL_DEPTH = 1024;

    public static void start_emit(Context ctxt) {
	ctxt.cw.println("void *carraway_malloc(int x) { return malloc(x); }");
	ctxt.cw.println("void carraway_free(void *x) { free(x); }");
	ctxt.cw.println("#define guru_malloc(x) carraway_malloc(x)");
	ctxt.cw.println("#define guru_free(x) carraway_free(x)");
	ctxt.cw.println("void release_clear(int tp, void *x);\n\n");
	
	if (!ctxt.getFlag("output_ocaml")) 
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

	ctxt.cw.println("#include \"release_no_clear.c\"\n\n");

	ctxt.cw.flush();
    }

    protected static void emit_release_switch_statement(Context ctxt, boolean clear, String eol) {
	java.io.PrintStream cw = clear ? ctxt.cw : ctxt.cw2;

	String clear_str = clear ? "_clear" : "_no_clear";

	Collection opaque_dtps = ctxt.getOpaqueDatatypes();
	Collection ind_dtps = ctxt.getInductiveDatatypes();

	cw.println("switch (tp) {"+eol);

	Iterator it = null;

	if (clear) {
	    it = opaque_dtps.iterator();
	    while (it.hasNext()) {
		Sym tp = (Sym)it.next();
		cw.println("  case "+tp.toString(ctxt)+": "+ctxt.getDeleteFunction(tp).toString(ctxt)+"(x); break;"+eol);
	    }
	}
	// we do not delete primitive types when releasing but not clearing

	it = ind_dtps.iterator();
	while (it.hasNext()) {
	    Sym tp = (Sym)it.next();
	    String tpstr = tp.toString(ctxt);
	    cw.println("  case "+tpstr+": delete_"+tpstr+clear_str+"(x); break;"+eol);
	}
	cw.println("}"+eol);
	cw.flush();
    }

    public static void finish_emit(Context ctxt) {
	// define release() and release_no_clear()

	ctxt.stage = 3;
	
	//	ctxt.cw2.println("inline void release_no_clear(int tp, void *x) {\n");
	ctxt.cw2.println("#define release_no_clear(tp, x) do {\\");
	emit_release_switch_statement(ctxt,false,"\\");
	ctxt.cw2.println("} while(0)\n\n");

	ctxt.cw.println("void **release_worklist = 0;");
	ctxt.cw.println("int release_call_depth = 0;");
	ctxt.cw.println("");
	ctxt.cw.println("void release_clear(int tp, void *x) {");
	ctxt.cw.println("int worklist_initially_empty;\n"+
			"void **node;\n"+
			"if (release_call_depth > "+MAX_RELEASE_CALL_DEPTH+") {\n"+
			"  // we must queue this release request\n"+
			"  node = guru_malloc(3*sizeof(void *));\n"+
			"  node[0] = tp;\n"+
			"  node[1] = x;\n"+
			"  node[2] = release_worklist;\n"+
			"  release_worklist = node;\n"+
			"  return;\n"+
			"}\n"+
			"\n"+
			"release_call_depth++;\n"+
			"do {\n");
	emit_release_switch_statement(ctxt,true,"");
	ctxt.cw.println("if (release_worklist) {\n"+
			"  node = release_worklist;\n"+
			"  tp = node[0];\n"+
			"  x = node[1];\n"+
			"  release_worklist = node[2];\n"+
			"  carraway_free(node);\n"+
			"}\n"+
			"else\n"+
			"  break;\n /* out of while loop */\n"+
			"} while (1);");
	ctxt.cw.println("release_call_depth--;");
	ctxt.cw.println("}\n");

	// write main() to call all the inits.

	Collection inits = ctxt.getGlobalInits();
	Iterator it = inits.iterator();
	ctxt.cw.println("int main(int argc, char **argv) {");

	while(it.hasNext()) {
	    String init_func = (String)it.next();
	    ctxt.cw.println("  "+init_func+"();");
	}
	ctxt.cw.println("return 0;");
	ctxt.cw.println("}\n");
	ctxt.cw.flush();
	ctxt.cw2.flush();
    }


}
