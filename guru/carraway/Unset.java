package guru.carraway;

public class Unset extends Command {
    public String flag;

    public Unset() {
	super(UNSET);
    }

    public void process(Context ctxt) {
	ctxt.unsetFlag(flag);
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	w.println("Unset "+flag);
    }
}
