package guru.carraway;

public class Function extends Command {
    public FunTerm t;

    public Function(){
	super(FUNCTION);
    }

    public void process(Context ctxt) {
	t.comment_expr(0,ctxt);

	ctxt.defineFunction(t.f,t.simpleType(ctxt),t);

	t.comment_expr(1,ctxt);

	t.simulate(ctxt, pos);
    }

    public void print(java.io.PrintStream w, Context ctxt) {
	w.print("Function ");
	t.print(w,ctxt);
	w.println(".");
    }    

}