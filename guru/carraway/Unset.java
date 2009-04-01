package guru.carraway;

public class Unset extends Command {
    public String flag;

    public Unset() {
	super(UNSET);
    }

    public void process(Context ctxt) {
	if (flag.equals("use_malloc") && ctxt.alloc_committed)
	    handleError(ctxt, "The use_malloc flag cannot be unset after the first Datatype command.");
	ctxt.unsetFlag(flag);
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	w.println("Unset "+flag);
    }
}
