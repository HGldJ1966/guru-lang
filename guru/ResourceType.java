package guru;

public class ResourceType extends Command {
    public Const s;

    public Define drop;

    public ResourceType() {
	super(RESOURCE_TYPE);
    }

    public void process(Context ctxt) {
	drop.process(ctxt);
	// we already called ctxt.addResourceType() in the parser.
	ctxt.setDropFunc(s,drop);
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	w.println("ResourceType "+s.toString(ctxt)+" with ");
	drop.print(w,ctxt);
    }


}