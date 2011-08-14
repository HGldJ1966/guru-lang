package guru.carraway;

import guru.Position;
import guru.IncludeHelper;
import java.io.File;
import java.util.Hashtable;
import java.util.Collection;
import java.util.Iterator;

public class Include extends Command {
    protected IncludeHelper h;
    public boolean the_cmd_line_file;
    
    public static int MAX_RELEASE_CALL_DEPTH = 1024;

    public Include(String filename, boolean the_cmd_line_file) {
	super(INCLUDE);
	h = new IncludeHelper(filename);
	this.the_cmd_line_file = the_cmd_line_file;
    }

    public Include(File f, File root) {
	super(INCLUDE);
	h = new IncludeHelper(f,root);
	the_cmd_line_file = false;
    }

    public static void start_emit(Context ctxt) {
	ctxt.cw.println("void release(int tp, void *x, int clear);\n");
	ctxt.cw.println("void *carraway_malloc(int x) { return malloc(x); }");
	ctxt.cw.println("void carraway_free(void *x) { free(x); }");
	ctxt.cw.println("#define guru_malloc(x) carraway_malloc(x)");
	ctxt.cw.println("#define guru_free(x) carraway_free(x)");
	
	ctxt.cw.flush();
    }

    public static void finish_emit(Context ctxt) {
	// define release()

	ctxt.stage = 3;
	
	Collection opaque_dtps = ctxt.getOpaqueDatatypes();
	Collection ind_dtps = ctxt.getInductiveDatatypes();

	ctxt.cw.println("void **release_worklist = 0;");
	ctxt.cw.println("int release_call_depth = 0;");
	ctxt.cw.println("");
	ctxt.cw.println("void release(int tp, void *x, int clear) {");
	ctxt.cw.println("int worklist_initially_empty;\n"+
			"void **node;\n"+
			"if (release_call_depth > "+MAX_RELEASE_CALL_DEPTH+") {\n"+
			"  // we must queue this release request\n"+
			"  node = guru_malloc(4*sizeof(void *));\n"+
			"  node[0] = tp;\n"+
			"  node[1] = clear;\n"+
			"  node[2] = x;\n"+
			"  node[3] = release_worklist;\n"+
			"  release_worklist = node;\n"+
			"  return;\n"+
			"}\n"+
			"\n"+
			"release_call_depth++;\n"+
			"do {\n");
	ctxt.cw.println("switch (tp) {");
	Iterator it = opaque_dtps.iterator();
	while (it.hasNext()) {
	    Sym tp = (Sym)it.next();
	    ctxt.cw.println("  case "+tp.toString(ctxt)+": "+ctxt.getDeleteFunction(tp).toString(ctxt)+"(x); break;");
	}
	it = ind_dtps.iterator();
	while (it.hasNext()) {
	    Sym tp = (Sym)it.next();
	    String tpstr = tp.toString(ctxt);
	    ctxt.cw.println("  case "+tpstr+": delete_"+tpstr+"(x,clear); break;");
	}
	ctxt.cw.println("}");
	ctxt.cw.println("if (release_worklist) {\n"+
			"  node = release_worklist;\n"+
			"  tp = node[0];\n"+
			"  clear = node[1];\n"+
			"  x = node[2];\n"+
			"  release_worklist = node[3];\n"+
			"  carraway_free(node);\n"+
			"}\n"+
			"else\n"+
			"  break;\n /* out of while loop */\n"+
			"} while (1);");
	ctxt.cw.println("release_call_depth--;");
	ctxt.cw.println("}\n");

	// write main() to call all the inits.

	Collection inits = ctxt.getGlobalInits();
	it = inits.iterator();
	ctxt.cw.println("int main(int argc, char **argv) {");

	while(it.hasNext()) {
	    String init_func = (String)it.next();
	    ctxt.cw.println("  "+init_func+"();");
	}
	ctxt.cw.println("return 0;");
	ctxt.cw.println("}\n");
	ctxt.cw.flush();
    }

    public void process(Context ctxt) {
	String err = h.process(ctxt);

	if (err != null)
	    handleError(ctxt,err);

	pos = new Position(0,0,h.f.getName());

	if (h.included)
	    // we have already included this file
	    return;

	Parser P = new Parser(false);

	try {
	    String s = h.ifile.getPath();
	    P.openFile(s);
	    String err1 = ctxt.pushFile(s);
	    if (err1 != null)
		handleError(ctxt, err1);
	} 
	catch (Exception e) {
	    handleError(ctxt, "Error opening file:\n"+e.toString());
	}
	P.setContext(ctxt);

	Command c = null;

	// initial declarations go in the top-level output file

	if (the_cmd_line_file && !ctxt.getFlag("output_ocaml")) 
	    start_emit(ctxt);
	
	while(true) {
	    try {
		c = P.readCommand();
	    } 
	    catch (Exception e) {
                e.printStackTrace();
		handleError(ctxt, "Error reading file:\n"+e.toString());
	    }

	    if (c == null)
		break;
	    c.process(ctxt);
	    if (ctxt.getFlag("print_parsed")) {
		c.print(ctxt.w, ctxt);
		ctxt.w.println("");
		ctxt.w.flush();
	    }
	}
	if (the_cmd_line_file) 
	    finish_emit(ctxt);

	ctxt.popFile();
    	h.finished(ctxt);
    }
    
    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	if (h.included) w.println("Include \"" + h.ifile.getPath() + "\".");
    }
}
