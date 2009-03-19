package guru.carraway;

import guru.Position;
import java.util.Collection;

public class Do extends Expr {

    public Expr[] ts;

    public Do(){
	super(DO);
    }

    public Do(Expr t1, Expr t2, Position p){
	super(DO);
	ts = new Expr[2];
	ts[0] = t1;
	ts[1] = t2;
	this.pos = p;
    }

    public Expr simpleType(Context ctxt) {
	int iend = ts.length - 1;
	for (int i = 0; i < iend; i++) {
	    Expr T = ts[i].simpleType(ctxt);
	    if (T.construct != VOID)
		classifyError(ctxt,"A subterm of a do-term does not have type void.\n\n"
			    +"1. The subterm: "+ts[i].toString(ctxt)
			      +"\n\n2. its type: "+T.toString(ctxt));
	}
	return ts[iend].simpleType(ctxt);
    }

    public boolean nonBindingOccurrence_h(Context ctxt, Sym s) {
	for (int i = 0, iend = ts.length; i < iend; i++) 
	    if (ts[i].nonBindingOccurrence(ctxt,s))
		return true;
	return false;
    }

    public void do_print(java.io.PrintStream w, Context ctxt) {
	if (ctxt.stage < 2)
	    w.print("do");
	for (int i = 0, iend = ts.length; i < iend; i++) {
	    if (ctxt.stage < 2)
		w.print(" ");
	    ts[i].print(w,ctxt);
	    if (ctxt.stage >= 2 && ts[i].construct != DO)
		w.println(";");
	}
	if (ctxt.stage < 2)
	    w.print(" end");
    }    

    public Sym simulate_h(Context ctxt, Position p) {
	Sym r = null;
	for (int i = 0, iend = ts.length; i < iend; i++) {
	    r = ts[i].simulate(ctxt,pos);
	    if (r == null)
		return null;
	}

	return r;
    }

    public Expr linearize(Context ctxt, guru.Position p, Sym dest, Collection decls, Collection defs) {
	int iend = ts.length - 1;
	for (int i = 0; i < iend; i++) 
	    // for each but the last term
	    defs.add(ts[i].linearize(ctxt,pos,null,decls,defs));
	return ts[iend].linearize(ctxt,pos,dest,decls,defs);
    }

}