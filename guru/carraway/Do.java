package guru.carraway;

import guru.Position;

public class Do extends Expr {

    public Expr[] ts;

    public Do(){
	super(DO);
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

    public void print(java.io.PrintStream w, Context ctxt) {
	w.print("do ");
	for (int i = 0, iend = ts.length; i < iend; i++) {
	    w.print(" ");
	    ts[i].print(w,ctxt);
	}
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
}