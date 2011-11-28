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

    // we assume t1 is def-expanded.
    protected void check_ctor_head(Context ctxt, Expr t1) {
	if (t1.construct == CONST)
	    return;
	
	boolean problem = false;

	if (t1.construct == TERM_APP || t2.construct == TYPE_APP) {
	    Expr e = ((App)t1).getHead(ctxt,true);
	    if (e.construct != CONST)
		problem = true;
	    else
		problem = !ctxt.isCtor((Const)e);
	}
	else
	    problem = true;

	if (problem)
	    handleError(ctxt,
			"One of the terms given to clash does not have a constructor at its head.\n"
			+"1. The term: "+t1.toString(ctxt));
	
    }

    public Expr classify(Context ctxt) {
        t1.checkTermination(ctxt);
        t2.checkTermination(ctxt);

	Expr t1a = t1.dropAnnos(ctxt).defExpandTop(ctxt);
	Expr t2a = t2.dropAnnos(ctxt).defExpandTop(ctxt);

	check_ctor_head(ctxt,t1a);
	check_ctor_head(ctxt,t2a);

	if (t1a.construct == t2a.construct) {
	    if (t1a.construct == CONST) {
		if (t1a.defEq(ctxt,t2a,true))
		    handleError(ctxt,"The terms given to clash are definitionally equal, but\n"
				+"they should be different in order to clash.\n"
				+"1. the first term: "+t1a.toString(ctxt)
				+"\n2. the second term: "+t2a.toString(ctxt));
		ctxt.resetNotDefEq();
		return new Atom(false,t1a,t2a);
	    }

	    App a1 = (App)t1a;
	    App a2 = (App)t2a;

	    if (a1.getHead(ctxt,true).defEq(ctxt,a2.getHead(ctxt,true),true))
		handleError(ctxt,
			    "Terms given to clash are applications of the"
			    +" same constructor.\n"
			    +"1. the first term: "+
			    t1a.toString(ctxt)+"\n"
			    +"2. the second term: "+
			    t2a.toString(ctxt));
	    ctxt.resetNotDefEq();
	}

	/* these have ctor heads but different constructs.  The only
	   possibilities are (CONST,TERM_APP) and (CONST,TYPE_APP),
	   or the reverse (also (TERM_APP,TYPE_APP) is possible). */

	return new Atom(false,t1a,t2a);
    }

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars)
    { }

    public java.util.Set getDependences() {
        java.util.Set s = t1.getDependences();
        s.addAll(t2.getDependences());
        return s;
    }
}
