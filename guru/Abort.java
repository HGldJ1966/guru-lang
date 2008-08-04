package guru;


import java.util.*;
import java.io.*;

public class Abort extends Expr{
    
    public Expr T;
    
    public Abort() {
        super(ABORT);
    }

    public Abort(Expr T) {
	super(ABORT);
	this.T = T;
    }

    public Expr do_rewrite(Context ctxt, Expr e, Expr x, Stack boundVars)
    {
	return this;
    }

    public void do_print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("abort ");
	if (T.construct != BANG)
	    T.print(w,ctxt);
    }
    
    public int numOcc(Expr e) {
	return T.numOcc(e);
    }

    public Expr subst(Expr e, Expr x) {
	Expr nT = T.subst(e,x);
	if (nT != T)
	    return new Abort(nT);
	return this;
    }

    public Expr dropAnnos(Context ctxt) {
	if (T.construct != BANG)
	    return new Abort(new Bang());
	return this;
    }

    public isInstC isInstance(Context ctxt, Expr ee) {
	ee = ee.defExpandTop(ctxt);
	if (ee.construct != ABORT)
	    return new isInstC(); // not an instance

	Abort e = (Abort)ee;
	return T.isInstance(ctxt, e.T);
    }
    
    public boolean defEqNoAnno(Context ctxt, Expr ee, boolean spec) {
	ee = ee.defExpandTop(ctxt, true, spec);
	if (construct != ee.construct) {
	    ctxt.notDefEq(this,ee);
	    return false;
	}
	Abort e = (Abort)ee;

	return T.defEqNoAnno(ctxt,e.T,spec);
    }

    public Expr classify(Context ctxt, int approx, boolean spec) {
	Expr cT = T.classify(ctxt,approx,spec);
	if (cT.construct != TYPE)
	    handleError(ctxt,
			"Abort is used with an expression which is not a "
			+"type.\n"
			+"1. The expression: "+T.toString(ctxt)+"\n"
			+"2. Its classifier: "+cT.toString(ctxt));
	return T;
    }
    
    public void getFreeVarsComputational(Context ctxt,
					 java.util.Collection vars) { }
    

    public boolean termTerminates(Context ctxt) {
        return false;
    }

    public java.util.Set getDependences() {
        return T.getDependences();
    }

    public void checkSpec(Context ctxt, boolean in_type){

    }
}

