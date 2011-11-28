package guru;

import java.util.*;
import java.io.*;

/* CharExprs are for character literals.  They are definitionally equal
   to applications of character constructors. */
public class CharExpr extends Expr {
    
    public String val;
    
    public CharExpr(String val) {
	super(CHAR_EXPR);
	this.val = val;
    }
    
    public void do_print(java.io.PrintStream w, Context ctxt) {
	w.print("\'");
	w.print(val);
	w.print("\'");
    }    

    public int numOcc(Expr e) {
	return (this == e) ? 1 : 0;
    }

    public Expr subst(Expr e, Expr x) {
	return this;
    }
    
    public Collection getConstsUsed(Context ctxt) {
	LinkedList l = new LinkedList();
	l.add(_const(ctxt,"mkchar"));
	l.add(_const(ctxt,"tt"));
	l.add(_const(ctxt,"ff"));
	return l;
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
	Expr ret = new TermApp(_const(ctxt,"mkchar"),args);
	ret.pos = pos;
	return ret;
    }


    public Expr classify(Context ctxt, int approx, boolean spec) {
	return _const(ctxt,"char");
    }

    public Expr dropAnnos(Context ctxt) {
	return expand(ctxt).dropAnnos(ctxt);
    }

    public Expr expand(Context ctxt) {
	char[] a = val.toCharArray();
	//Expr ret = new TermApp(_const(ctxt,"inc"), // _const(ctxt,"string"), 
	//		       _const(ctxt,"stringn"));
	Expr ret;
	String s = "";
	for (int i = 0; i < a.length; i++) {
	    if (a[i] == '\\') {
		if (a[++i] == -1)
			break;
		switch(a[i]) {
		    case '\\': s += '\\'; break;
		    case '\'': s += '\''; break;
		    case '\"': s += '\"'; break;
		    case '0' : s += '\0'; break;
		    case 'b' : s += '\b'; break;
		    case 't' : s += '\t'; break;
		    case 'n' : s += '\n'; break;
		    case 'f' : s += '\f'; break;
		    case 'r' : s += '\r'; break;
		    default  : s += a[i]; break;
		}
	    } else
		s += a[i];
	}

	//handleError("test");

	a = s.toCharArray();
	ret =  toCharExpr(ctxt,a[0]);
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

    public void checkSpec(Context ctxt, boolean in_type, Position p){
    }

    public guru.carraway.Expr toCarraway(Context ctxt) {
	return expand(ctxt).toCarraway(ctxt);
    }
}
