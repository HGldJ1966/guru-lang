package guru;

import java.io.*;

public class Compile extends Command {
    public String filename;
    public File f, root, ifile;

    Const cmain;
    
        
    public Compile() {
	super(COMPILE);
    }

    public Compile(String file) {
	super(COMPILE);
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
		handleError(ctxt,"Cannot open file "+f+".");
	    }
	    f = new File(tmp.getName());
	}

	ifile = (f.isAbsolute() 
		    ? f
		    : (new File(root.getAbsolutePath() + "/" + f.getPath())));
	
	Expr b = (Expr )ctxt.defsBody.get( cmain );
	
	
	
	if (b.isProof(ctxt))
	    handleError(ctxt,"Compiler: Cannot compile a proof.");
	
	Expr ctp = ctxt.getClassifier(cmain);
	if (ctp == null)
	    handleError(ctxt, 
			"Internal error: the program to compile is missing "
			+"a type");
	String n = ifile.getName();
	
	guru.compiler.Compiler compiler = new guru.compiler.Compiler();

	PrintStream os = null;
	try {
	    os = new PrintStream(new FileOutputStream(ifile));
	} catch (IOException e) {
	    e.printStackTrace();
	    handleError(ctxt,"Problem opening output file for writing:\n"
			+ e.getMessage());
	}

	compiler.compile(root, ctxt, os, cmain);
    }
    
    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	w.println("Compiled " + ifile.getPath() + ".");
    }
}
