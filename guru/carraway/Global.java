package guru.carraway;

public class Global extends Command {
    Sym c;
    Expr t;

    public Global() {
	super(GLOBAL);
    }

    public void process(Context ctxt) {
	ctxt.addGlobal(c,t.simpleType(ctxt),t);
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("Global ");
	c.print(w,ctxt);
	w.print(" = ");
	t.print(w,ctxt);
	w.println(".");
    }
}
