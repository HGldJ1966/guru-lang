package guru;

public class Kind extends Expr{
    public Kind(int construct) { 
	super(construct);
    }
    public void do_print(java.io.PrintStream w, Context ctxt) {
	if (construct == FKIND)
	    w.print("fkind");
	else
	    w.print("tkind");
    }

    public Expr dropAnnos(Context ctxt) {
	return this;
    }

    public int numOcc(Expr e) {
	return (this == e) ? 1 : 0;
    }

    public Expr subst(Expr e, Expr x) {
	return this;
    }
}
