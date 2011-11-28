package guru;

public class Set extends Command {
    public String flag;

    public Set() {
	super(SET);
    }

    public void process(Context ctxt) {
	ctxt.setFlag(flag);
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	w.println("Set \""+flag+"\".");
    }
}
