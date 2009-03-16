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

    // must define for types only
    public boolean nonBindingOccurrence(Context ctxt, Sym s) {
	classifyError(ctxt,"Internal error: checking for a non-binding variable occurrence is not implemented.\n\n"
		    +"1. the expression: "+toString(ctxt));
	return false;
    }

    // must define for well-typed terms only.  This returns null if an abort is evaluated.
    public Sym simulate(Context ctxt) {
	simulateError(ctxt,"Internal error: simulation is not implemented.\n\n"
		    +"1. the expression: "+toString(ctxt));
	return null;
    }
}