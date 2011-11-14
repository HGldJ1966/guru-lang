package guru;

import java.util.*;
import java.io.*;

public class Const extends Expr implements Comparable {
    
    public String name;
    
    public Const(String name) {
	super(CONST);
	this.name = name;
    }
    
    public void do_print(java.io.PrintStream w, Context ctxt) {
	w.print(name);
	if (ctxt.getFlag("comment_consts")) 
	    print_pos_comment_long(w);
    }    

    public int numOcc(Expr e) {
	return (this == e) ? 1 : 0;
    }

    public int hashCode_h(Context ctxt) {
	return name.hashCode();
    }

    public Expr subst(Expr e, Expr x) {
	return this;
    }
    
    public Expr do_rewrite(Context ctxt, Expr e, Expr x, Stack boundVars) {
    	return this;
    }

    public Expr evalStep(Context ctxt) {
	return this.defExpandTop(ctxt,true,true);
    }
    
    public Expr classify(Context ctxt, int approx, boolean spec) {
	Expr T = ctxt.getClassifier(this);
	if (T == null)
	    handleError(ctxt, "Missing a classifier for a constant.\n"
			+"1. The constant: "+toString(ctxt));
	return T;
    }

    public boolean defEqNoAnno(Context ctxt, Expr e, boolean spec) {
	if (this == e)
	    return true;
	if (ctxt.isDefined(this) && (spec || !ctxt.isOpaque(this))) {
	    Expr n = defExpandTop(ctxt,true,spec);
	    if (ctxt.getFlag("debug_def_eq")) {
		ctxt.w.println("Expanding "+toString(ctxt)+" to "
			       +n.toString(ctxt));
		ctxt.w.flush();
	    }

	    return n.defEqNoAnno(ctxt, e, spec);
	}
	if (e.construct == TYPE_APP) {
	    // might beta reduce to this.
	    
	    Expr ep = ((App)e).spineForm(ctxt,false,spec,true);
	    if (ep.construct == CONST)
		return defEqNoAnno(ctxt,ep,spec);
	}

	Expr tmp = e.defExpandTop(ctxt,true,spec);
	boolean ret = (this == tmp);
	if (!ret)
	    ctxt.notDefEq(this,tmp);
	return ret;
    }

    protected boolean defEqNoAnnoApprox(Context ctxt, Expr e,
					boolean spec) {
	if (this == e)
	    return true;
	if (ctxt.isDefined(this) && (spec || !ctxt.isOpaque(this)))
	    return defExpandTop(ctxt,true,true).defEqNoAnnoApprox(ctxt, e,
								  spec);
	Expr tmp = e.defExpandTop(ctxt,true,spec);
	boolean ret = (this == tmp);
	if (!ret)
	    ctxt.notDefEq(this,tmp);
	return ret;
    }

    public Expr dropAnnos(Context ctxt) {
	return this;
    }

    public isInstC isInstance(Context ctxt, Expr e) {
	return new isInstC(defEq(ctxt, e));
    }

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars)
    { }
    
    public void getFreeVarsComputational(Context ctxt, Collection vars) { }

    public void checkTermination(Context ctxt) { }

    public java.util.Set getDependences() {
        // We model constants as depending on themselves; this way
        // e.g. a ProofApp that uses a constant will depend on the
        // constant.
        java.util.Set s = new TreeSet();
        s.add(this);
        return s;
    }

    public int compareTo(Object o) {
        return name.compareTo(((Const)o).name);
    }

    public void checkSpec(Context ctxt, boolean in_type, Position p) {
	if (ctxt.isSpec(this) && !in_type) {
	    handleError(ctxt, p, "Specificational constant used in" 
			+ " non-specificational location.\n"
                        + "\n1. the constant: " + toString(ctxt));
	}
    }
    
    public UnjoinDeduction Unjoin(
			Expr target, 
			UnjoinContext uctxt,
			Context baseCtxt,
			boolean eq
	)
    {
    	if (target.construct != CONST)
    		return eq ? UnjoinDeduction.contradiction : UnjoinDeduction.empty;
    	
    	Const c = (Const)target;
    	
    	if (this.name == c.name)
    		return eq ? UnjoinDeduction.empty : UnjoinDeduction.contradiction;
    	else
    		return eq ? UnjoinDeduction.contradiction : UnjoinDeduction.empty;
    }

    public guru.carraway.Expr toCarrawayType(Context ctxt, boolean rttype) {
	if (rttype) {
	    guru.carraway.Sym s = ctxt.carraway_ctxt.lookup(name);
	    if (s == null)
		handleError(ctxt, "Internal error: Carraway declaration missing for \""+toString(ctxt)+"\".");
	    return s;
	}
	// we are getting the resource type here

	if (isTrackedType(ctxt)) {
	    guru.carraway.Sym s = ctxt.carraway_ctxt.lookup("unowned");
	    if (s == null)
		handleError(ctxt, "Internal error: Carraway declaration missing for \"unowned\".\n\n");
	    return s;
	}
	else 
	    return new guru.carraway.Untracked();
    }

    public guru.carraway.Expr toCarraway(Context ctxt) {
	guru.carraway.Sym s = ctxt.carraway_ctxt.lookup(name);
	if (s == null)
	    handleError(ctxt, "Internal error: Carraway declaration missing for \""+toString(ctxt)+"\".");
	return s;
    }
}
