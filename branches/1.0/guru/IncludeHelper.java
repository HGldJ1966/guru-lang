package guru;

import java.io.File;
import java.util.Hashtable;


public class IncludeHelper {
    public String filename;
    public File f, root, ifile;
    public static Hashtable includeHash = new Hashtable(); 
    public boolean included;
    
    public IncludeHelper() {
    }

    public IncludeHelper(String filename) {
	this.filename = filename;
    }

    public IncludeHelper(File f, File root) {
	this.f = f;
	this.root = root;
    }

    // return an error message if there is a problem, otherwise null.
    public String process(FlagManager fm) {
	if (f == null) {
	    File tmp = null;
	    try {
		tmp = (new File(filename)).getCanonicalFile();
		root = tmp.getParentFile();
	    }
	    catch (Exception e) {
		return "Cannot find file "+f+".";
	    }
	    f = new File(tmp.getName());
	}

	included = false;
	ifile = (f.isAbsolute() 
		    ? f
		    : (new File(root.getAbsolutePath() + "/" + f.getPath())));
	try {
	    ifile = ifile.getCanonicalFile();
	} 
	catch (Exception e) {
	    return "Error getting information about file:\n"+e.toString();
	}

	if (includeHash.containsKey(ifile)) {
	    included = true;
	    if (((Boolean)includeHash.get(ifile)).booleanValue()) 
		return null;
	    // we have a circular include

	    return "A file is causing itself to be included.\n"+"1. the file :"+ifile.getPath();
	}
	
	if (!ifile.isFile())
	    return ("Cannot include " + ifile.getPath()
		    + ": it is not a file.");
	if (!ifile.canRead())
	    return ("Cannot include " + ifile.getPath() + 
		    ": the file cannot be read.");
	
	if (fm.getFlag("show_includes")) {
	    fm.w.println("Including "+ifile.getPath());
	    fm.w.flush();
	}

    	includeHash.put(ifile, new Boolean(false));
	return null;
    }

    // call this when you are done processing the included file
    public void finished(FlagManager fm) {
	included = true;
	includeHash.put(ifile,new Boolean(true));
	if (fm.getFlag("show_includes")) {
	    fm.w.println("Done including "+ifile.getPath());
	    fm.w.flush();
	}
    }

}
