package guru;

import java.io.File;
import java.util.Hashtable;


public class Include extends Command {
    public String filename;
    public File f, root, ifile;
    public static Hashtable includeHash = new Hashtable(); 
    public boolean included;
    public boolean trusted;
    
    public Include() {
	super(INCLUDE);
    }

    public Include(String file) {
	super(INCLUDE);
	filename = file;
    }

    public void process(Context ctxt) {
	if (f == null) {
	    File tmp = null;
	    try {
		tmp = (new File(filename)).getCanonicalFile();
		root = tmp.getParentFile();
	    }
	    catch (Exception e) {
		handleError(ctxt, "Cannot open file "+f+".");
	    }
	    f = new File(tmp.getName());
	    pos = new Position(0,0,tmp.getName());
	}

	included = false;
	Parser P = new Parser(trusted);
	ifile = (f.isAbsolute() 
		    ? f
		    : (new File(root.getAbsolutePath() + "/" + f.getPath())));
	try {
	    ifile = ifile.getCanonicalFile();
	} 
	catch (Exception e) {
	    handleError(ctxt, "Error opening file:\n"+e.toString());
	}

	if (includeHash.containsKey(ifile)) 
	    return;
	
	if (!ifile.isFile())
	    handleError(ctxt, "Cannot include " + ifile.getPath()
			+ ": it is not a file.");
	if (!ifile.canRead())
	    handleError(ctxt, "Cannot include " + ifile.getPath() + 
			": the file cannot be read.");
	
	String ifile_path = ifile.getPath();

	try {
	    P.openFile(ifile_path);
	} 
	catch (Exception e) {
	    handleError(ctxt, "Error opening file:\n"+e.toString());
	}
	P.setContext(ctxt);
	Command c = null;
	
	if (ctxt.getFlag("show_includes")) {
	    ctxt.w.println("Including "+ifile_path);
	    ctxt.w.flush();
	}

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
    	includeHash.put(ifile, new Boolean(true));
    	included = true;
    }
    
    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	if (included) w.println("Included " + ifile.getPath() + ".");
    }
}
