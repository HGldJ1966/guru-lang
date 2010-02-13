package guru;

import java.util.*;
import java.io.*;


public class Var extends Expr{
    
    public String name;

    public Var(String name){
	super(VAR);
        this.name = name;
    }

    public void print_pos_comment(java.io.PrintStream w, Context ctxt) {
	if (ctxt.getFlag("comment_vars")) 
	    print_pos_comment_short(w);
	else if (ctxt.getFlag("comment_vars_long")) 
	    print_pos_comment_long(w);
    }

    public int hashCode_h(Context ctxt) {
	return ctxt.varHashCode(this);
    }

    public void do_print(java.io.PrintStream w, Context ctxt) {
	if (!ctxt.getFlag("no_expand_vars") && ctxt.isMacroDefined(this))
	    ctxt.getDefBody(this).print(w,ctxt);
	else
	    w.print(name);
	if (ctxt.getFlag("print_var_context")) {
	    w.print(" [ctxt is ");
	    w.print(ctxt);
	    w.print("]");
	}
	print_pos_comment(w,ctxt);
    }    

    /* special method for the benefit of Abbrev, because the binding occurrence
       in an abbrev is a very special case. */
    public void abbrev_print(java.io.PrintStream w, Context ctxt) {
	w.print(name);
	print_pos_comment(w,ctxt);
    }

    public int numOcc(Expr e) {
	return (this == e) ? 1 : 0;
    }
    
    public Expr subst(Expr e, Expr x) {
	return (this == x) ? e : this;
    }
    public Expr do_rewrite(Context ctxt, Expr e, Expr x, Stack boundVars) {
    	return this;
    }

    public Expr classify(Context ctxt, int approx, boolean spec) {
	Expr T = ctxt.getClassifier(this);
	if (T == null) {
	    if (ctxt.isMacroDefined(this)) 
		/* setting this's classifier after the computation
		   just below does not seem to save us much checking
		   time, so we don't do it. */
		return ctxt.getDefBody(this).classify(ctxt,approx,spec);
	    handleError(ctxt, "Missing a classifier for a variable.\n"
			+"1. The variable: "+toString(ctxt));
	}
	return T;
    }

    public boolean defEqNoAnno(Context ctxt, Expr e, boolean spec) {
	e = e.defExpandTop(ctxt, true, spec);
	Expr tmp = defExpandTop(ctxt, true, spec);
	if (tmp == this) {
	    if (this == e)
	       return true;
	    ctxt.notDefEq(this,e);
	    return false;	
	}
	return tmp.defEqNoAnno(ctxt,e,spec);
    }

    public boolean defEqNoAnnoApprox(Context ctxt, Expr e,
				     boolean spec) {
	e = e.defExpandTop(ctxt, true, spec);
	Expr tmp = defExpandTop(ctxt, true, spec);
	if (tmp == this) {
	    if (this == e)
	       return true;
	    ctxt.notDefEq(this,e);
	    return false;	
	}
	return tmp.defEqNoAnnoApprox(ctxt,e,spec);
    }

    public isInstC isInstance(Context ctxt, Expr ee) {
	Expr tmp = defExpandTop(ctxt);
	if (tmp == this)
	    return new isInstC(defEq(ctxt, ee));
	return tmp.isInstance(ctxt,ee);
    }

    public Expr dropAnnos(Context ctxt) {

	// we do not set classifiers for macro-defined variables.
	// Since we are dropping annotations, we must already have
	// dropped them from the expression this variable is
	// macro-defined to equal.
	if (ctxt.isMacroDefined((Var)this)) 
	    return ctxt.getDefBody(this).dropAnnos(ctxt);

	if (ctxt.getClassifier(this) == null)
	    // this can only happen in an unannotated term we parsed in
	    return this;

	if (ctxt.isAssumption(this))
	    return new Bang();

	return this;
    }

    public Expr evalStep(Context ctxt) {
	return defExpandTop(ctxt).dropAnnos(ctxt);
    }

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars) { 
	Expr tmp = defExpandTop(ctxt);
	if (tmp == this) {
	    if (this == IH)
		handleError(ctxt,
			    "The induction hypothesis is being used without"
			    +" arguments.\n"
			    +"1. The IH: "+toString(ctxt));
	}
	else
	    tmp.checkTermination(ctxt,IH,arg,vars);
    }
    
    public void getFreeVarsComputational(Context ctxt, Collection vars) {
	vars.add(this);
    }

    public void checkTermination(Context ctxt) {
	if (ctxt.isMacroDefined(this))
	    ctxt.getDefBody(this).checkTermination(ctxt);
    }

    public void checkSpec(Context ctxt, boolean in_type, Position p){
	if (ctxt.isSpec(this) && !in_type) {
	    /*	    Expr n = null;
	      n.print(ctxt.w,ctxt); */
	    handleError(ctxt, "Specificational variable used in" 
			+ " non-specificational location.\n"
                        + "1. the variable: " + toString(ctxt));
	}
    }

    public guru.carraway.Expr toCarrawayType(Context ctxt, boolean rttype) {
	guru.carraway.Sym s = ctxt.carraway_ctxt.lookup(name);
	if (s == null)
	    handleError(ctxt, "Internal error: Carraway declaration missing for \""+toString(ctxt)+"\".");
	return s;
    }	
}
