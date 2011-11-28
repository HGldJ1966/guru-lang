package guru;

public class Compress extends Expr{
    
    public Expr t;
    
    public Compress() {
	super(COMPRESS);
    }
    
    public Compress(Expr t) {
	super(COMPRESS);
	this.t = t;
    }

    public void do_print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("@ ");
	t.print(w,ctxt);
    }

    public int numOcc(Expr e) {
	return t.numOcc(e);
    }

    public Expr subst(Expr e, Expr x) {
	Expr nt = t.subst(e,x);
	if (nt != t)
	    return new Compress(nt);
	return this;
    }

    public Expr classify(Context ctxt, int approx, boolean spec) {
	return t.classify(ctxt, approx, spec);
    }
    
    public Expr dropAnnos(Context ctxt) {
	return t.dropAnnos(ctxt);
    }
    public void checkTermination(Context ctxt) {
        t.checkTermination(ctxt);
    }

    public java.util.Set getDependences() {
        return t.getDependences();
    }

    public void checkSpec(Context ctxt, boolean in_type, Position p){
	t.checkSpec(ctxt, in_type, pos);
    }

    public void getFreeVarsComputational(Context ctxt, 
					 java.util.Collection vars) {
	t.getFreeVarsComputational(ctxt,vars);
    }

    public guru.carraway.Expr toCarraway(Context ctxt) {
	return new guru.carraway.Compress(t.toCarraway(ctxt),pos);
    }
}
