package guru.carraway;

public class Case extends Expr {
    public Sym c;
    public Sym[] vars;
    public Expr body;

    public Case(){
	super(CASE);
    }

    public void print(java.io.PrintStream w, Context ctxt) {
	c.print(w,ctxt);
	for(int i = 0, iend = vars.length; i < iend; i++) {
	    w.print(" ");
	    vars[i].print(w,ctxt);
	}
	w.print(" => ");
	body.print(w,ctxt);
    }    

    public Expr simpleType(Context ctxt) {
	Expr cT = ctxt.getType(c);
	if (vars.length == 0) {
	    if (cT.construct != SYM)
		classifyError(ctxt,"A constructor given as the pattern of a match-case has a type which is not a datatype.\n\n"
			      +"1. the constructor: "+c.toString(ctxt)
			      +"\n\n2. its type: "+cT.toString(ctxt));
	    return body.simpleType(ctxt);
	}

	if (cT.construct != FUN_TYPE)
	    classifyError(ctxt,"The constructor heading the pattern of a match-case has an unexpected type.\n\n"
			  +"1. the constructor: "+c.toString(ctxt)
			  +"\n\n2. its type: "+cT.toString(ctxt));
	
	FunType f = (FunType)cT;
	
	if (f.vars.length != vars.length)
	    classifyError(ctxt,
			  "The constructor heading the pattern of a match-case is applied to the wrong number of pattern variables.\n\n"
			  +"1. the constructor: "+c.toString(ctxt)
			  +"\n\n2. its type: "+cT.toString(ctxt));
	for (int i = 0, iend = vars.length; i < iend; i++) {
	    ctxt.setType(vars[i], f.types[i].applySubst(ctxt));
	    ctxt.setSubst(f.vars[i],vars[i]);
	}

	// clear the substitution of f's vars now.
	for (int i = 0, iend = vars.length; i < iend; i++) 
	    ctxt.setSubst(f.vars[i],null);
	
	return body.simpleType(ctxt);
    }
}