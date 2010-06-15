package guru;

import java.util.*;
import java.io.*;

public class TerminatesCase extends Expr{

    public Expr t;
    public Expr p1;
    public Expr p2;
    public Var x;
    public Var u;	

    public TerminatesCase() {
	super(TERM_CASE);
    }

    public TerminatesCase(Expr t, Expr p1, Expr p2, Var x, Var u) {
	super(TERM_CASE);
	this.t = t;
	this.p1 = p1;
  	this.p2 = p2;
	this.x = x;
	this.u = u;
    }

    public Expr subst(Expr e, Expr y) {
	Expr n = t.subst(e,y), n1 = p1.subst(e,y), n2 = p2.subst(e,y);
	if (n != t || n1 != p1 || n2 != p2)
	    return new TerminatesCase(n,n1,n2,x,u);
	return this;
    }

    public int numOcc(Expr e) {
        return t.numOcc(e) + p1.numOcc(e) + p2.numOcc(e) + x.numOcc(e) + u.numOcc(e);
    }

    public void do_print(java.io.PrintStream w, 
			 Context ctxt) {
	w.print("terminates-case ");
        t.print(w,ctxt);
        w.print(" by ");
	u.print(w,ctxt);
        w.print(" with ");
	x.print(w,ctxt);
	w.print(" => ");
	p1.print(w,ctxt);
	w.print(" | abort => ");
	p2.print(w,ctxt);
	w.print(" end ");

    }
 
    public Expr dropAnnos(Context ctxt) {
	return new Bang();
    }

    public Expr classify(Context ctxt, int approx, boolean spec) {
	ctxt.setClassifier(u, new Atom(true, t, x));
	Expr cP1 = p1.classify(ctxt,approx,spec);

	ctxt.setClassifier(u, new Atom(true, t, new Abort(new Bang())));
	Expr cP2 = p2.classify(ctxt,approx,spec);

	if (!cP1.defEq(ctxt,cP2,approx,spec)) {
	  handleError(ctxt,
		     "terminates-case branches prove different formulas:\n\n"
	             +"1. first branch: "+cP1.toString(ctxt)
                     +"\n2. second branch: "+cP2.toString(ctxt));
	}

	return cP1;
    }
  

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars) {
	p1.checkTermination(ctxt,IH,arg,vars);
        p2.checkTermination(ctxt,IH,arg,vars);
    }

}
