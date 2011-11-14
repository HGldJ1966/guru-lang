package guru;

import java.util.*;
import java.io.*;

public class Let extends Expr{
    
    public Var x1;
    public Expr t1;
    public Var x2;
    public Expr t2;

    public Ownership x1_stat; // ownership info for x1, see FunAbstraction

    public Let() {
	super(LET);
    }

    public Let(Var x1, Ownership x1_stat, Expr t1, Var x2, Expr t2) {
	super(LET);
	this.x1 = x1;
	this.x1_stat = x1_stat;
	this.t1 = t1;
	this.x2 = x2;
	this.t2 = t2;
    }
    
    public int hashCode_h(Context ctxt) {
	return t1.hashCode_h(ctxt) + t2.hashCode_h(ctxt);
    }

    public void do_print(java.io.PrintStream w, Context ctxt) 
    {
	w.print("let ");
	if (x1_stat.status != Ownership.DEFAULT) {
	    w.print(x1_stat.toString(ctxt));
	    w.print(" ");
	}
	x1.print(w,ctxt);
	w.print(" = ");
	t1.print(w,ctxt);
	if (x2 != null) {
	    w.print(" by ");
	    x2.print(w,ctxt);
	}
	w.print(" in ");
	t2.print(w,ctxt);
    }

    public int numOcc(Expr e) 
    {
	return (x1.numOcc(e) + t1.numOcc(e) + (x2 != null ? x2.numOcc(e) : 0)
		+ t2.numOcc(e));
    }

    public Expr subst(Expr e, Expr x) {
	Expr n1 = t1.subst(e,x);
	Expr n2 = (x == x1 ? t2 : t2.subst(e,x));
	if (n1 != t1 || n2 != t2)
	    return new Let(x1, x1_stat, n1, x2, n2);
	return this;
    }

    public Expr do_rewrite(Context ctxt, Expr e, Expr x, Stack boundVars) {
	Expr n1 = t1.rewrite(ctxt,e,x,boundVars);
	boundVars.push(x1);
	Expr n2 = (x == x1 ? t2 : t2.rewrite(ctxt,e,x,boundVars));
	boundVars.pop();
	if (n1 != t1 || n2 != t2)
	    return new Let(x1, x1_stat, n1, x2, n2);
	return this;
    }

    public Expr dropAnnos(Context ctxt) {
	if (ctxt.getClassifier(x1) == null)
	    ctxt.setClassifier(x1,new Bang());
	Expr t1a = t1.dropAnnos(ctxt);
	Expr t2a = t2.subst(new Bang(),x2).dropAnnos(ctxt);
	if (t1a != t1 || t2a != t2)
	    return new Let(x1, x1_stat, t1a, x2, t2a);
	return this;
    }

    public void setClassifier2(Context ctxt) {
	if (x2 != null) {
	    ctxt.setClassifier(x2,new Atom(true, x1, t1.dropAnnos(ctxt)));
	}
    }

    public void setClassifiers(Context ctxt, int approx, boolean spec) {
	ctxt.setClassifier(x1,t1.classify(ctxt, approx, spec));
	setClassifier2(ctxt);
    }

    public Expr classify(Context ctxt, int approx, boolean spec) {
	if (ctxt.getFlag("debug_classify_lets")) {
	    ctxt.w.print("(Classifying ");
	    print(ctxt.w,ctxt);
	    ctxt.w.println("");
	    ctxt.w.flush();
	}
	if (ctxt.getClassifier(x1) == null) {
	    /* we do not change the classifier, because the Compiler
	       may set it carefully the way it wants it */
	    Expr T = t1.classify(ctxt, approx, spec);
	    ctxt.setClassifier(x1,T);
	}
	setClassifier2(ctxt);
	Expr ret = t2.classify(ctxt,approx,spec);
	if (ret.numOcc(x1) > 0)
	    handleError(ctxt,"The classifier for the body of a let-term uses"
			+" the let-bound variable.\n"
			+"1. the let-bound variable: "+x1.toString(ctxt)
			+"\n2. the classifier: "+ret.toString(ctxt));
	if (ctxt.getFlag("debug_classify_lets")) {
	    ctxt.w.print(") Classifier is ");
	    ret.print(ctxt.w,ctxt);
	    ctxt.w.println("");
	    ctxt.w.flush();
	}
	return ret;
    }

    public boolean defEqNoAnno(Context ctxt, Expr ee, boolean spec) {
	ee = ee.defExpandTop(ctxt,true,spec);
	if (ee.construct != construct) {
	    ctxt.notDefEq(this,ee);
	    return false;
	}
	Let e = (Let)ee;

	return (t1.defEqNoAnno(ctxt,e.t1,spec) && 
		t2.defEqNoAnno(ctxt, e.t2.subst(x1,e.x1), spec));
    }
  
    
    public Expr evalStep(Context ctxt) {
	Expr et1 = t1.evalStep(ctxt);
	if (et1 != t1)
	    return new Let(x1, x1_stat, et1,x2,t2);
	if (t1.construct == ABORT)
	    //return ctxt.abort;
		return t1;
	return t2.subst(t1, x1);
    }
    
    public void getFreeVarsComputational(Context ctxt, Collection vars){
	t1.getFreeVarsComputational(ctxt, vars);
	t2.getFreeVarsComputational(ctxt, vars);
	vars.remove(x1);
    }

    public void checkTermination(Context ctxt) {
        t1.checkTermination(ctxt);
	t2.checkTermination(ctxt);
    }

    public java.util.Set getDependences() {
        java.util.Set s = t1.getDependences();
        s.addAll(t2.getDependences());
        return s;
    }

    public void checkSpec(Context ctxt, boolean in_type, Position p){
	t1.checkSpec(ctxt, in_type, pos);
	t2.checkSpec(ctxt, in_type, pos);
    }

    // Overloaded from Expr
    public UnjoinDeduction Unjoin(
			Expr target, 
			UnjoinContext uctxt,
			Context ctxt,
			boolean eq
	)
    {
    	return t2.subst(t1, x1).Unjoin(
    		target,
    		uctxt,
    		ctxt,
    		eq
    	);
    }
    
    public guru.carraway.Expr toCarraway(Context ctxt) {
	guru.carraway.Let l = new guru.carraway.Let();
	l.pos = pos;
	guru.carraway.Context cctxt = ctxt.carraway_ctxt;
	l.x = cctxt.newSym(x1.name,x1.pos, false);
	l.t1 = t1.toCarraway(ctxt);
	cctxt.pushVar(l.x);
	l.t2 = t2.toCarraway(ctxt);
	cctxt.popVar(l.x);
	return l;
    }
	
}
