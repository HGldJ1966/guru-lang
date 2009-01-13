package guru;

public class Truei extends Expr {
    
    public Truei() {
	super(TRUEI);
    }
    
    public void do_print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("truei");
    }

    public Expr classify(Context ctxt) {
	return new True();
    }
    
    public Expr subst(Expr e, Expr x) {
	return this;
    }

    public int numOcc(Expr e) {
	return (this == e) ? 1 : 0;
    }
    
    public Expr dropAnnos(Context ctxt) {
	return this;
    }

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] v) {

    }
}
