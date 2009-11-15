package guru.carraway;
import java.util.Collection;

public class Abort extends Expr {

    public Abort(){
	super(ABORT);
    }

    public void do_print(java.io.PrintStream w, Context ctxt) {
	if (ctxt.stage > 2)
	    w.println("fprintf(stderr,\"abort at "+pos.toString(false/*not quoted */)
		      +"\\n\"); exit(EXIT_FAILURE)");
	else
	    w.print("abort");
    }    

    public Expr simpleType(Context ctxt) {
	return new Abort();
    }

    public boolean eqType(Context ctxt, Expr T) {
	return true;
    }

    public Sym simulate_h(Context ctxt, guru.Position p) {
	return null;
    }

    public Expr linearize(Context ctxt, guru.Position p, Sym dest, Collection decls, Collection defs) {
	defs.add(this);
	return linearize_return(ctxt,ctxt.zerof,p,dest);
    }
}