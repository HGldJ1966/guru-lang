package guru;

import java.util.*;
import java.io.*;

/* StringExprs are for string literals.  They are definitionally equal
   to applications of string constructors. */
public class StringExpr extends Expr {
    
    public String val;
    
    public StringExpr(String val) {
	super(STRING_EXPR);
	this.val = val;
    }
    
    public void do_print(java.io.PrintStream w, Context ctxt) {
	w.print("\"");
	w.print(val);
	w.print("\"");
    }    

    public int numOcc(Expr e) {
	return (this == e) ? 1 : 0;
    }

    public Expr subst(Expr e, Expr x) {
	return this;
    }
    
    public Expr do_rewrite(Context ctxt, Expr e, Expr x, Stack boundVars) {
    	return this;
    }

    protected Expr toBitExpr(Context ctxt, int a) {
	return (a == 0 ? _const(ctxt, "ff") : _const(ctxt, "tt"));
    }

    protected Expr toCharExpr(Context ctxt, char c) {
	Expr[] args = new Expr[7];
	int mask = 1;
	for (int j = 0; j < 7; j++) {
	    args[j] = toBitExpr(ctxt, c & mask);
	    mask = mask * 2;
	}
	return new TermApp(_const(ctxt,"mkchar"),args);
    }


    public Expr classify(Context ctxt, int approx, boolean spec) {
	return _const(ctxt,"string");
    }

    public Collection getConstsUsed(Context ctxt) {
	LinkedList l = new LinkedList();
	l.add(_const(ctxt,"string"));
	l.add(_const(ctxt,"stringc"));
	l.add(_const(ctxt,"stringn"));
	l.add(_const(ctxt,"mkchar"));
	l.add(_const(ctxt,"tt"));
	l.add(_const(ctxt,"ff"));
	return l;
    }

    public Expr dropAnnos(Context ctxt) {
	return expand(ctxt).dropAnnos(ctxt);
    }

    public Expr expand(Context ctxt) {
	char[] a = val.toCharArray();
	Expr ret = new TermApp(_const(ctxt,"inc"), _const(ctxt,"string"), 
			       _const(ctxt,"stringn"));
	for (int i = a.length - 1, iend = 0; i >= iend; i--) 
	    ret = new TermApp(_const(ctxt,"stringc"), 
			      toCharExpr(ctxt,a[i]), ret);
	return ret;
    }

    public isInstC isInstance(Context ctxt, Expr e) {
	return new isInstC(defEq(ctxt, e));
    }

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars)
    { }
    
    public void getFreeVarsComputational(Context ctxt, Collection vars) { }

    public void checkTermination(Context ctxt) {
    }

    public void checkSpec(Context ctxt, boolean in_type){
    }

}
