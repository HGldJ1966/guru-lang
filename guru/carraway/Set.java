package guru.carraway;

public class Set extends Command {
    public String flag;

    public Set() {
	super(SET);
    }

    public void process(Context ctxt) {
	if (flag.equals("use_malloc") && ctxt.alloc_committed)
	    handleError(ctxt, "The use_malloc flag must be set before the first Datatype command.");
	ctxt.setFlag(flag);
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	w.println("Set \""+flag+"\".");
    }
}
