package guru.carraway;

public class Function extends Command {
    public FunTerm t;

    public Function(){
	super(FUNCTION);
    }

    public void process(Context ctxt) {
	ctxt.defineFunction(t.f,t.simpleType(ctxt),t);
    }

    public void print(java.io.PrintStream w, Context ctxt) {
	w.print("Function ");
	t.print(w,ctxt);
	w.println(".");
    }    

}