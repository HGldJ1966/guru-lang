package guru.carraway;

public class Attribute extends Command {
    public Sym s;

    public Attribute() {
	super(ATTRIBUTE);
    }

    public void process(Context ctxt) {
	ctxt.addAttribute(s);
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	w.println("Attribute "+s.toString(ctxt)+".");
    }


}