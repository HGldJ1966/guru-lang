package guru;

import java.util.*;
import java.io.*;
import java.lang.Math.*;

/* WordExprs are for hex-to-word conversions. */
public class WordExpr extends Expr {

	public String val;

	public WordExpr(String val) {
		super(WORD_EXPR);
		this.val = val;
	}

	public Collection getConstsUsed(Context ctxt) {
		LinkedList l = new LinkedList();
		l.add(_const(ctxt, "mkword"));
		l.add(_const(ctxt, "tt"));
		l.add(_const(ctxt, "ff"));
		return l;
	}

	public Expr classify(Context ctxt, int approx, boolean spec) {
		return _const(ctxt, "word");
	}


	public Expr subst(Expr e, Expr x) {
		return this;
	}

	public int numOcc(Expr e) {
		return (this == e) ? 1 : 0;
	}

	public void do_print(java.io.PrintStream w, Context ctxt) {
		w.print("0x");
		w.print(val);
	}

	public Expr do_rewrite(Context ctxt, Expr e, Expr x, Stack boundVars) {
		return this;
	}

	public Expr buildExpr(Context ctxt, long hexnum) {
		Expr[] args = new Expr[32];
		for (int i = 0; i < 32; i++) {
			if (((hexnum >> (31-i)) & 1) == 1)
				args[i] = _const(ctxt, "tt");
			else
				args[i] = _const(ctxt, "ff");
		}
		Expr ret = new TermApp(_const(ctxt, "mkword"), args);
		ret.pos = pos;
		return ret;
	}



	public Expr expand(Context ctxt) {
		char[] a = val.toCharArray();
		long hexnum = 0;
		double cur_pow;
		Expr ret;
		for(int i = 0; i < a.length; i++) {
			cur_pow = Math.pow(16, (a.length - i - 1));
			switch(a[i]) {
				case '0' : break;
				case '1' : hexnum += 1 * cur_pow; break;
				case '2' : hexnum += 2 * cur_pow; break;
				case '3' : hexnum += 3 * cur_pow; break;
				case '4' : hexnum += 4 * cur_pow; break;
				case '5' : hexnum += 5 * cur_pow; break;
				case '6' : hexnum += 6 * cur_pow; break;
				case '7' : hexnum += 7 * cur_pow; break;
				case '8' : hexnum += 8 * cur_pow; break;
				case '9' : hexnum += 9 * cur_pow; break;
				case 'a' :
				case 'A' :
					hexnum += 10 * cur_pow; break;
				case 'b' :
				case 'B' :
					hexnum += 11 * cur_pow; break;
				case 'c' :
				case 'C' :
					hexnum += 12 * cur_pow; break;
				case 'd' :
				case 'D' :
					hexnum += 13 * cur_pow; break;
				case 'e' :
				case 'E' :
					hexnum += 14 * cur_pow; break;
				case 'f' :
				case 'F' :
					hexnum += 15 * cur_pow; break;
				default :
					//This is bad. Treating as 0 for now.
					break;
			}
		}
		ret = buildExpr(ctxt, hexnum);
		ret.pos = pos;
		return ret;
		
	}

	public Expr dropAnnos(Context ctxt) {
		return expand(ctxt).dropAnnos(ctxt);
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

