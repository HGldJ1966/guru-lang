package guru.carraway;

public class Match extends Expr {
    public Expr t;
    public Sym s;
    public Case[] C;

    public Match(){
	super(MATCH);
    }

    public void print(java.io.PrintStream w, Context ctxt) {
	w.print("match ");
	t.print(w,ctxt);
	w.print(" with ");
	boolean first = true;
	for(int i = 0, iend = C.length; i < iend; i++) {
	    if (first) 
		first = false;
	    else
		w.print(" | ");
	    C[i].print(w,ctxt);
	}
	w.print(" end");
    }    

    public Expr simpleType(Context ctxt) {
	Expr expected = null;
	Expr T = t.simpleType(ctxt);
	for (int i = 0, iend = C.length; i < iend; i++) {
	    Expr CT = C[i].simpleType(ctxt);
	    if (s == null)
		s = ctxt.getDatatype(C[i].c);
	    if (expected == null)
		expected = CT;
	    else
		if (!CT.eqType(ctxt,expected))
		    classifyError(ctxt,"The type computed for a match-case is different from the one expected from earlier cases.\n\n"
				  +"1. the case: "+C[i].c.toString(ctxt)
				  +"\n\n2. the computed type: "+CT.toString(ctxt)
				  +"\n\n3. the expected type: "+expected.toString(ctxt));
	}
	return expected;
    }

}