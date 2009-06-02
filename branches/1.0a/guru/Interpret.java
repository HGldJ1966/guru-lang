package guru;

public class Interpret extends Command {
    public Expr t;
    public Interpret() {
	super(INTERPRET);
    }

    public void process(Context ctxt) {
	t.classify(ctxt,Expr.NO_APPROX,true);
	Expr e = t.eval(ctxt);
	e.print(ctxt.w,ctxt);
	ctxt.w.println("");
	ctxt.w.flush();
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {
    }
}
