package guru;

public class Echo extends Command {
    public String s;
    public Echo() {
	super(ECHO);
    }

    public void process(Context ctxt) {
	ctxt.w.println(s);
	ctxt.w.flush();
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {
    }
}
