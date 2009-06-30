package guru;

public class Init extends Command {
    public Const s;
    public Var v1, v2;
    Ownership T1, T2, T3; // T1 and T2 are guaranteed to have status RESOURCE.
    boolean must_consume_scrut;
    String delim, code;

    public Init() {
	super(INIT);
    }

    public void process(Context ctxt) {
	ctxt.initCmds.add(this);
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("Init ");
	if (must_consume_scrut)
	    w.print("must_consume_scrutinee ");
	w.print(s.toString(ctxt)+"(");
	w.print(T1.toString(ctxt));
	w.print(" ");
	v1.print(ctxt.w,ctxt);
	w.print(") (");
	w.print(T2.toString(ctxt));
	w.print(" ");
	v2.print(ctxt.w,ctxt);
	w.print("). ");
	w.print(T3.toString(ctxt));
	w.print(" <<");
	w.print(delim);
	w.println(code);
	w.println(delim);
    }

}