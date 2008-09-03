package guru;

public class Clash extends Expr{
    
    public Expr t1;
    public Expr t2;
    
    public Clash() { 
	super(CLASH);
    }

    public Clash(Expr t1, Expr t2) {
	super(CLASH);
	this.t1 = t1;
	this.t2 = t2;
    }

    public void do_print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("clash ");
	t1.print(w,ctxt);
	w.print(" ");
	t2.print(w,ctxt);
    }
    
    public int numOcc(Expr e) {
	return t1.numOcc(e) + t2.numOcc(e);
    }

    public Expr subst(Expr e, Expr x) {
	Expr nt1 = t1.subst(e,x), nt2 = t2.subst(e,x);
	if (nt1 != t1 || nt2 != t2)
	    return new Clash(nt1, nt2);
	return this;
    }
   
    public Expr dropAnnos(Context ctxt) {
	return new Bang();
    }

    protected void check_not_var(Context ctxt, Expr e) {
	if (e.construct == VAR) 
	    handleError(ctxt,
			"One of the terms given to a clash-proof is a variable"
			+" (which is not allowed).\n"
			+"1. the term: "+e.toString(ctxt));
    }

    public Expr classify(Context ctxt) {
        t1.checkTermination(ctxt);
        t2.checkTermination(ctxt);

	Expr t1a = t1.dropAnnos(ctxt).defExpandTop(ctxt);
	Expr t2a = t2.dropAnnos(ctxt).defExpandTop(ctxt);

	check_not_var(ctxt,t1a);
	check_not_var(ctxt,t2a);

	if (t1a.construct == t2a.construct && t1a.construct != Expr.BANG
            && t1a != t2a) {
	    // this might still work out, if we have applications
	    // of different constructors.
	    if (t1a.construct != CONST) {
		if (t1a.construct != TERM_APP && t1a.construct != TYPE_APP) 
		    handleError(ctxt,
				"Terms given to clash have same top-level"
				+" construct (and are not applications).\n"
				+"1. the first term (annotations dropped): "+
				t1a.toString(ctxt)+"\n"
				+"2. the second term (annotations dropped): "+
				t2a.toString(ctxt));
		
		App a1 = (App)t1a;
		App a2 = (App)t2a;
		if (a1.getHead(ctxt,true) == a2.getHead(ctxt,true))
		    handleError(ctxt,
				"Terms given to clash are applications of the"
				+" same term\n"
				+"1. the first term (annotations dropped): "+
				t1a.toString(ctxt)+"\n"
				+"2. the second term (annotations dropped): "+
				t2a.toString(ctxt));
		
		if (a1.getHead(ctxt,true).construct != CONST)
		    handleError(ctxt,
				"Terms given to clash are applications with"
				+" non-constant heads\n"
				+"1. the first term (annotations dropped): "+
				t1a.toString(ctxt)+"\n"
				+"2. the second term (annotations dropped): "+
				t2a.toString(ctxt));
	    }
	}

	return new Atom(false, t1a, t2a);
    }

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars)
    { }

    public java.util.Set getDependences() {
        java.util.Set s = t1.getDependences();
        s.addAll(t2.getDependences());
        return s;
    }
}
