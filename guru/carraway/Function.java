package guru.carraway;

public class Function extends Command {
    public FunTerm t;

    public Function(){
	super(FUNCTION);
    }

    public void process(Context ctxt) {

	// stage 0

	ctxt.stage = 0;
	ctxt.commentBox(t.f.toString(ctxt));
	t.comment_expr(null,ctxt);

	// stage 1

	ctxt.stage = 1;
	ctxt.defineFunction(t.f,t.simpleType(ctxt),t);
	t.comment_expr(null,ctxt);
	t.simulate(ctxt, pos);

	// stage 2

	ctxt.stage = 2;
	FunTerm lin = (FunTerm)t.linearize(ctxt,null,null); // last two vals ignored
	lin.comment_expr(null,ctxt);
    }

    public void print(java.io.PrintStream w, Context ctxt) {
	w.print("Function ");
	t.print(w,ctxt);
	w.println(".");
    }    

}