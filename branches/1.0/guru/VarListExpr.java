package guru;

import java.util.*;

public class VarListExpr extends Expr{
    
    public Var [] vars;
    public Expr [] types;
    
    public VarListExpr(int construct) {
	super(construct);
    }

    public VarListExpr(int construct, Var[] vars, Expr[] types) {
	super(construct);
	this.vars = vars;
	this.types = types;
    }
    
    public void do_print(java.io.PrintStream w, Context ctxt) {
	print_varlist(w,ctxt);
    }

    public void print_varlist(java.io.PrintStream w, Context ctxt) {
	int iend = vars.length;
	for (int i = 0; i < iend; i++) {
	    w.print("(");
	    vars[i].print(w, ctxt);
	    if (types[i].construct != Expr.BANG){
		w.print(" : ");
		types[i].print(w, ctxt);
	    }
	    w.print(")");
	}
    }

    public int numOcc(Expr e) {
	int n = 0;
	boolean bound = false;
	for (int i = 0, iend = vars.length; i < iend; i++) {
	    n += (bound ? 0 : vars[i].numOcc(e)) + types[i].numOcc(e);
	    bound = (bound || e == vars[i]);
	}
	return n;
    }

    public boolean isBound(Expr x) {
	for (int i = 0, iend = vars.length; i < iend; i++)
	    if (x == vars[i])
		return true;
	return false;
    }

    public Expr subst(Expr e, Expr x) {
	int iend = vars.length;
	Expr [] stypes = new Expr[iend];
	boolean bound = false;
	boolean changed = false;
	for (int i = 0; i < iend; i++) {
	    if (bound)
		stypes[i] = types[i];
	    else {
		stypes[i] = types[i].subst(e,x);
		//System.out.println("subbing " + e.toString() + " for " + e.toString());
		
		bound = (vars[i] == x);
	    }
	    if (stypes[i] != types[i])
		changed = true;
	}
	if (changed)
	    return new VarListExpr(construct,vars,stypes);
	return this;
    }
    
    // check that the classifiers declared for the inputs are classifiable.
    //
    // This method sets the vars' classifiers if currently unset (but
    // vars with different scopes are distinct, so it is not necessary
    // to unset this later).
    //
    // We return true if we set any vars' classifiers.
    public boolean checkClassifiers(Context ctxt, int approx,
				    boolean spec) {
	boolean ret = false;
	for (int i = 0, iend = vars.length; i < iend; i++) {
	    Expr x = types[i].classify(ctxt, approx, spec);
	    if (types[i].construct != TYPE && 
		x.construct != TYPE && x.construct != FORMULA) 
		handleError(ctxt,
			    "A variable's declared classifier is not \"type\","
			    +" a type, or a formula.\n"
			    +"1. the variable's classifier: "
			    +types[i].toString(ctxt)+"\n"
			    +"2. its classifier: "+x.toString(ctxt));
	    if (ctxt.getClassifier(vars[i]) == null) {
		ret = true;
		ctxt.setClassifier(vars[i], types[i]);
	    }
	}
	return ret;
    }

    // just add declarations for all the variables to the given context
    public void setClassifiers(Context ctxt) {
	for (int i = 0, iend = vars.length; i < iend; i++) 
	    ctxt.setClassifier(vars[i], types[i]);
    }

    public Expr dropAnnos(Context ctxt) {
	int iend = types.length;
	Expr[] types2 = new Expr[iend];
	boolean changed = false;

	for (int i = 0; i < iend; i++) {
	    types2[i] = types[i].dropAnnos(ctxt);
	    if (types2[i] != types[i])
		changed = true;

	    /* the following needs to be done so that we can tell
	       which variables are assumption variables when dropping
	       proofs.  We will check the classifier types[i] during
	       classification. */
	    if (ctxt.getClassifier(vars[i]) == null)
		ctxt.setClassifier(vars[i],types[i]); 

	}

	if (changed)
	    return new VarListExpr(construct, vars, types2);
	return this;
    }

    public java.util.Set getDependences() {
        java.util.Set s = new TreeSet();
        for(int i = 0, n = types.length; i < n; ++i)
            s.addAll(types[i].getDependences());
        return s;
    }
}
