package guru;

public class Interpret extends Command {
    public Const c;
    public Expr e;
    public Interpret() {
	super(INTERPRET);
    }

    public void process(Context ctxt) {
	
	Expr e1 = c.dropAnnos(ctxt).eval(ctxt);
	/*
	Expr e2 = null;
	while (e1 != e2){
		e2 = e1;
		e1 = e1.eval(ctxt);
	}*/
	e = e1;
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	e.do_print(w,ctxt);
    }
}
