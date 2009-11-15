package guru.carraway;
import guru.Position;

public class Command {
    
    public static final int INVALID = 0;
    public static final int ATTRIBUTE = 1;
    public static final int PRIMITIVE = 2;
    public static final int DATATYPE = 3;
    public static final int FUNCTION = 4;
    public static final int GLOBAL = 5;

    public static final int SET = 6;
    public static final int UNSET = 7;
    public static final int INCLUDE = 8;
    public static final int INIT = 9;
    public static final int TYPEDEF = 10;

    protected int which;
    public Position pos;

    public Command(int which) {
	this.which = which;
    }
    
    public void process(Context ctxt) {
	System.out.println("Processing command unimplemented.");
        System.exit(5);
    }

    public void process_new_typedefs(Context ctxt) {
	// print any typedefs that were queued up
	java.util.Iterator it = ctxt.new_typedefs.iterator();
	while(it.hasNext()) {
	    Command c = (Command)it.next();
	    c.process(ctxt);
	}
	ctxt.new_typedefs.clear();
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
	System.exit(1);
    }
}
