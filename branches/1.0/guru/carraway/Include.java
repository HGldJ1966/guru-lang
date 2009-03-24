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

	// we need to write predeclare the release function.
	if (the_cmd_line_file) 
	    ctxt.cw.println("void release(int tp, void *x);\n");
	
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
	if (the_cmd_line_file) {

	    // define release()

	    ctxt.cw.println("void release(int tp, void *x) {");
	    ctxt.cw.println("switch (tp) {");
	    
	    Collection dtps1 = ctxt.getDatatypes1();
	    Iterator it = dtps1.iterator();
	    while (it.hasNext()) {
		Sym tp = (Sym)it.next();
		ctxt.cw.println("  case "+tp.toString(ctxt)+": "+ctxt.getDeleteFunction(tp).toString(ctxt)+"(x); break;");
	    }
	    ctxt.cw.println("}");
	    ctxt.cw.println("}\n");

	    // write main() to call all the inits.

	    Collection inits = ctxt.getGlobalInits();
	    it = inits.iterator();
	    ctxt.cw.println("int main(int argc, char **argv) {");
	    ctxt.cw.println("carraway_mem_start = carraway_mem_end = (char *)sbrk(0);");

	    while(it.hasNext()) {
		String init_func = (String)it.next();
		ctxt.cw.println("  "+init_func+"();");
	    }
	    ctxt.cw.println("}\n");
	}

	ctxt.popFile();
    	h.finished(ctxt);
    }
    
    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	if (h.included) w.println("Include \"" + h.ifile.getPath() + "\".");
    }
}
