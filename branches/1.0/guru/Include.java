package guru;

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

	try {
	    P.openFile(h.ifile.getPath());
	} 
	catch (Exception e) {
	    handleError(ctxt, "Error opening file:\n"+e.toString());
	}
	
	boolean did_trust_hypjoins = ctxt.getFlag("trust_hypjoins");
	if( trusted && !did_trust_hypjoins )
		ctxt.setFlag( "trust_hypjoins" );
	
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
    	h.finished(ctxt);
    	if( trusted && !did_trust_hypjoins )
    		ctxt.unsetFlag( "trust_hypjoins" );
    }
    
    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	if (h.included) w.println("Included " + h.ifile.getPath() + ".");
    }
}
