package guru;

public class Interpret extends Command {
    public Expr t;
    public Interpret() {
	super(INTERPRET);
    }

    public void process(Context ctxt) {
	Expr e = t.eval(ctxt);
	e.print(ctxt.w,ctxt);
	ctxt.w.println("");
	ctxt.w.flush();
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {
    }
}
