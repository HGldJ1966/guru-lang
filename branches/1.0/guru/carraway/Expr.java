package guru.carraway;
import guru.Position;
import java.util.Collection;
import java.util.Vector;
import java.util.ListIterator;

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
    public static final int DO = 9;
    public static final int COMPRESS = 10;

    // type constructs
    public static final int PIN = 20;
    public static final int UNTRACKED = 21;
    public static final int VOID = 22;
    public static final int FUN_TYPE = 24;

    // our sole kind construct
    public static final int TYPE = 23;

    // terms created only during compilation
    public static final int INIT_TERM = 30; 
    public static final int DROP_TERM = 31;

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
	System.out.println("Carraway classification error.\n\n"+msg);
	System.exit(2);
    }

    public void simulateError(Context ctxt, String msg) {
	if (pos != null) {
	    pos.print(System.out);
	    System.out.print(": ");
	}
	System.out.println("Carraway simulation error.\n\n"+msg);
	System.exit(2);
    }

    public void compileError(Context ctxt, String msg) {
	if (pos != null) {
	    pos.print(System.out);
	    System.out.print(": ");
	}
	System.out.println("Carraway compilation error, stage "+(new Integer(ctxt.stage)).toString()+".\n\n"+msg);
	System.exit(2);
    }

    final protected void print(java.io.PrintStream w, Context ctxt) {
	/*
	if (pos != null) {
	    int lines = pos.linenum - ctxt.output_pos.linenum;
	    int cols = pos.column - ctxt.output_pos.column;
	    if (lines > 0) {
		for (int i = 0; i < lines; i++)
		    w.println("");
		ctxt.output_pos.linenum = pos.linenum;
		if (cols > 0) {
		    for (int i = 0; i < cols; i++)
			w.print(" ");
		    ctxt.output_pos.column = pos.column;
		}
	    }
	    }*/
	do_print(w,ctxt);
    }

    abstract protected void do_print(java.io.PrintStream w, Context ctxt);
   
    public String toString(Context ctxt) {
	java.io.ByteArrayOutputStream s = new java.io.ByteArrayOutputStream();
	java.io.PrintStream w = new java.io.PrintStream(s);
	print(w,ctxt);
	return s.toString();
    }

    public void comment_expr(Sym s, Context ctxt) {
	comment_expr(s,ctxt,false);
    }

    public void comment_expr(Sym s, Context ctxt, boolean is_typing) {
	String stage_num = (new Integer(ctxt.stage)).toString();
	if (ctxt.getFlag("debug_stage"+stage_num) || ctxt.getFlag("debug_stages")) {
	    if (ctxt.getFlag("output_ocaml"))
		ctxt.cw.print("(");
	    else
		ctxt.cw.print("/");
	    ctxt.cw.println("*\n * stage "+stage_num);
	    ctxt.cw.println(" *");
	    ctxt.cw.println("\n");
	    if (is_typing) {
		if (s != null)
		    ctxt.cw.print(s.toString(ctxt)+" : ");
	    }
	    else {
		if (s != null)
		    ctxt.cw.print("Global "+s.toString(ctxt)+" := ");
		else {
		    if (ctxt.stage <= 2)
			ctxt.cw.print("Function ");
		}
	    }

	    print(ctxt.cw,ctxt);
	    ctxt.cw.print(".\n*");

	    if (ctxt.getFlag("output_ocaml"))
		ctxt.cw.print(")");
	    else
		ctxt.cw.print("/");
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
		ctxt.w.println("  returning "+ret.refString(ctxt));
	    ctxt.w.flush();
	}
	return ret;
    }

    // only call with a returnable t (anything except an Abort, Let, InitTerm, or Match)
    static protected Expr linearize_return(Context ctxt, Expr t, Position p, Sym dest) {
	if (dest == ctxt.returnf)
	    return new App(ctxt.returnf,t,p);
	if (dest != null)
	    return new Let(dest,t,p);
	return t;
    }

    // implement for terms only
    public Expr linearize(Context ctxt, guru.Position p, Sym dest, Collection decls, Collection defs) {
	compileError(ctxt,"Internal error: linearization is not implemented.\n\n"
		    +"1. the expression: "+toString(ctxt));
	return null;
    }

    public Expr linearize(Context ctxt, guru.Position p, Sym dest) {
	Vector decls = new Vector();
	Vector defs = new Vector();

	Expr r = linearize(ctxt,p,dest,decls,defs);
	
	ListIterator it = defs.listIterator(defs.size());
	while(it.hasPrevious()) {
	    Expr e = (Expr)it.previous();
	    r = new Do(e,r,pos);
	}

	it = decls.listIterator(decls.size());
	while(it.hasPrevious()) {
	    Sym s = (Sym)it.previous();
	    r = new Do(new Let(s,pos),r,pos);
	}
	return r;
    }

    // return a flattened form of this Expr, assumed to be a type.
    // this may queue up new Typedefs in ctxt.new_typedefs.
    public Expr flattenType(Context ctxt) {
	return this;
    }
 
    public boolean need_datatype_for_ctor_arg_resource_type() {
	return (construct != Expr.FUN_TYPE && construct != Expr.TYPE && construct != Expr.UNTRACKED);
    }
   
}