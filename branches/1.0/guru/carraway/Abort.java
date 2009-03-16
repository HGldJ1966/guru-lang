package guru.carraway;

public class Abort extends Expr {

    public Abort(){
	super(ABORT);
    }

    public void print(java.io.PrintStream w, Context ctxt) {
	w.print("abort");
    }    

    public Expr simpleType(Context ctxt) {
	return new Abort();
    }

    public boolean eqType(Context ctxt, Expr T) {
	return true;
    }

    public Sym simulate(Context ctxt) {
	return null;
    }
}