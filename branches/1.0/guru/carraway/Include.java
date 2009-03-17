package guru.carraway;

import guru.Position;
import guru.IncludeHelper;
import java.io.File;
import java.util.Hashtable;

public class Include extends Command {
    protected IncludeHelper h;
    public boolean trusted;
    
    public Include() {
	super(INCLUDE);
	h = new IncludeHelper();
    }

    public Include(String filename) {
	super(INCLUDE);
	h = new IncludeHelper(filename);
    }

    public Include(File f, File root) {
	super(INCLUDE);
	h = new IncludeHelper(f,root);
    }

    public void process(Context ctxt) {
	String err = h.process(ctxt);

	if (err != null)
	    handleError(ctxt,err);

	pos = new Position(0,0,h.f.getName());

	if (h.included)
	    // we have already included this file
	    return;

	Parser P = new Parser(trusted);

	String prev_file = ctxt.getCurrentFile();

	try {
	    String s = h.ifile.getPath();
	    P.openFile(s);
	    String err1 = ctxt.setCurrentFile(s);
	    if (err1 != null)
		handleError(ctxt, err1);
	} 
	catch (Exception e) {
	    handleError(ctxt, "Error opening file:\n"+e.toString());
	}
	P.setContext(ctxt);
	Command c = null;
	
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
	ctxt.setCurrentFile(prev_file);
    	h.finished(ctxt);
    }
    
    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	if (h.included) w.println("Include \"" + h.ifile.getPath() + "\".");
    }
}
