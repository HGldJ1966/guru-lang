package guru.carraway;
import guru.Position;

public abstract class Expr {

    public static final int INVALID = 0;
    public static final int SYM = 1;

    // term constructs
    public static final int CAST = 2;
    public static final int APP = 3;
    public static final int ABORT = 4;
    public static final int LET = 5;
    public static final int MATCH = 6;
    public static final int CASE = 7; // used in MATCH-terms
    public static final int FUN_TERM = 8; // top-level only
    public static final int INIT_TERM = 9; // created only internally (not parsed)
    public static final int DO = 10;
    public static final int DROP_TERM = 11;

    // type constructs
    public static final int PIN = 20;
    public static final int UNTRACKED = 21;
    public static final int VOID = 22;
    public static final int FUN_TYPE = 24;

    // our sole kind construct
    public static final int TYPE = 23;

    public static final int LAST = 100;

    public int construct;
    public Position pos;
    
    public Expr(int construct) {
	this.construct = construct;
	this.pos = null;
    }

    public void classifyError(Context ctxt, String msg) {
	if (pos != null) {
	    pos.print(System.out);
	    System.out.print(": ");
	}
	System.out.println("classification error.\n\n"+msg);
	System.exit(2);
    }

    public void simulateError(Context ctxt, String msg) {
	if (pos != null) {
	    pos.print(System.out);
	    System.out.print(": ");
	}
	System.out.println("simulation error.\n\n"+msg);
	System.exit(2);
    }

    public void compileError(int i, Context ctxt, String msg) {
	if (pos != null) {
	    pos.print(System.out);
	    System.out.print(": ");
	}
	System.out.println("compilation error, stage "+(new Integer(i)).toString()+".\n\n"+msg);
	System.exit(2);
    }

    abstract public void print(java.io.PrintStream w, Context ctxt);
   
    public String posToString() {
	java.io.ByteArrayOutputStream s = new java.io.ByteArrayOutputStream();
	java.io.PrintStream w = new java.io.PrintStream(s);
	if (pos == null)
	    w.print("unknown position");
	else
	    pos.print(w);
	return s.toString();
    }

    public String toString(Context ctxt) {
	java.io.ByteArrayOutputStream s = new java.io.ByteArrayOutputStream();
	java.io.PrintStream w = new java.io.PrintStream(s);
	print(w,ctxt);
	return s.toString();
    }

    public void comment_expr(int i, Context ctxt) {
	String stage_num = (new Integer(i)).toString();
	if (ctxt.getFlag("debug_stage"+stage_num)) {
	    ctxt.cw.println("/*");
	    ctxt.cw.println(" * stage "+stage_num);
	    ctxt.cw.println(" *");
	    ctxt.cw.println("\n");
	    print(ctxt.cw,ctxt);
	    ctxt.cw.println("\n*/");
	    ctxt.cw.println("");
	    ctxt.cw.flush();
	}
    }

    public boolean consumable() {
	if (construct == UNTRACKED ||
	    construct == TYPE ||
	    construct == FUN_TYPE)
	    return false;
	
	return true;
    }
	
    abstract public Expr simpleType(Context ctxt);

    // must define for types only
    public boolean eqType(Context ctxt, Expr T) {
	classifyError(ctxt,"Internal error: type equality checking not implemented.\n\n"
		      +"1. the expression: "+toString(ctxt));
	return false;
    }

    // must define for types only
    public Expr applySubst(Context ctxt) {
	classifyError(ctxt,"Internal error: applying a substitution is not implemented.\n\n"
		      +"1. the expression: "+toString(ctxt));
	return null;
    }

    // must define for types and terms which are not fun-terms, only
    public final boolean nonBindingOccurrence(Context ctxt, Sym s) {
	if (ctxt.getFlag("debug_nonBindingOccurrence")) {
	    ctxt.w.print("checking for nonBindingOccurrence of "+s.toString(ctxt)
			 +" in "+toString(ctxt));
	    ctxt.w.println(" (");
	    ctxt.w.flush();
	}   
	boolean ret = nonBindingOccurrence_h(ctxt,s);
	if (ctxt.getFlag("debug_nonBindingOccurrence")) {
	    if (ret)
		ctxt.w.println(") = true");
	    else
		ctxt.w.println(") = true");
	    ctxt.w.flush();
	}
	return ret;
    }

    public boolean nonBindingOccurrence_h(Context ctxt, Sym s) {
	classifyError(ctxt,"Internal error: checking for a non-binding variable occurrence is not implemented.\n\n"
		    +"1. the expression: "+toString(ctxt));
	return false;
    }

    final public Expr stage1(Context ctxt) {
	compileError(1,ctxt,"Internal error: stage 1 compilation is not implemented.\n\n"
		     +"1. the expression: "+toString(ctxt));
	return null;
    }

    // must define for well-typed terms only.  This returns null if an abort is evaluated.
    public Sym simulate_h(Context ctxt, Position p) {
	simulateError(ctxt,"Internal error: simulation is not implemented.\n\n"
		    +"1. the expression: "+toString(ctxt));
	return null;
    }

    final public Sym simulate(Context ctxt, Position p) {
	if (ctxt.getFlag("debug_simulate")) {
	    ctxt.w.print("simulating "+toString(ctxt));
	    ctxt.w.println(" (");
	    ctxt.w.flush();
	}
	Sym ret = simulate_h(ctxt,p);
	if (ctxt.getFlag("debug_simulate")) {
	    ctxt.w.println(") simulated "+toString(ctxt));
	    if (ret == null)
		ctxt.w.println("  aborting");
	    else
		ctxt.w.println("  returning "+ret.toString(ctxt) + " (created at "+ret.posToString()+")");
	    ctxt.w.flush();
	}
	return ret;
    }


}