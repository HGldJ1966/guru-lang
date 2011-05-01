package guru;

public class ClassifyCmd extends Command {
    public Expr G;
    public Expr e;
    public ClassifyCmd() {
	super(CLASSIFY_CMD);
    }

    public void process(Context ctxt) {
	e = G.classify(ctxt, Expr.NO_APPROX, true);
	e.dropAnnos(ctxt).print(ctxt.w,ctxt);
	ctxt.w.println("");
	ctxt.w.flush();
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {
    }
}
