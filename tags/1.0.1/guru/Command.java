package guru;

public class Command {
    
    public static final int INVALID = 0;
    public static final int DEFINE = 1;
    public static final int INDUCTIVE = 2;
    public static final int SET = 3;
    public static final int UNSET = 4;
    public static final int INCLUDE = 5;
    public static final int ADDTOPATH = 6;
    public static final int COMPILE = 7;
    public static final int INTERPRET = 8;

    // to help with compilation
    public static final int OPAQUE = 9;
    public static final int STUB = 10;
    public static final int UNTRACKED = 11;

    // dependence tracking
    public static final int DUMPDEPENDENCE = 15;
    
    public static final int TOTAL = 16;

    public static final int CLASSIFY_CMD = 17;

    public static final int CHECK_TRUSTED = 18;

    public static final int ECHO = 19;

    // for carraway layer
    public static final int RESOURCE_TYPE = 20;
    public static final int INIT = 21;
    public static final int LOCATE = 22;

    protected int which;
    public Position pos;

    public Command(int which) {
	this.which = which;
    }
    
    public void process(Context ctxt) {
	System.out.println("Processing command unimplemented.");
        System.exit(5);
    }

    public String toString(Context ctxt) {
	java.io.ByteArrayOutputStream s = new java.io.ByteArrayOutputStream();
	java.io.PrintStream w = new java.io.PrintStream(s);
	print(w,ctxt);
	return s.toString();
    }

    public void print(java.io.PrintStream w, Context ctxt) {
	w.print("***");
    }

    public void handleError(Context ctxt, String msg) {
	if (pos != null)
	    pos.print(System.out);
	System.out.println(": command processing error.\n"+msg);
	ctxt.printDefEqErrorIf();
        int retval = (which == DEFINE) ? 3 : 4;
	System.exit(retval);
    }

    public void handleWarning(Context ctxt, String msg) {
	pos.print(System.out);
	System.out.println(": command processing warning.\n"+msg+"\n");
    }
}
