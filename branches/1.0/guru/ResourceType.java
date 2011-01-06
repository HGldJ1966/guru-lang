package guru;

public class ResourceType extends Command {
    public Const s;

    public Define drop;

    public ResourceType() {
	super(RESOURCE_TYPE);
    }

    public void process(Context ctxt) {
	if (drop != null) {
	    drop.process(ctxt);
	    // we already called ctxt.addResourceType() in the parser.
	    ctxt.setDropFunc(s,drop);
	}
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	w.println("ResourceType "+s.toString(ctxt)+" with ");
	if (drop != null)
	    drop.print(w,ctxt);
	else
	    w.println(" no drop function.");
    }


}