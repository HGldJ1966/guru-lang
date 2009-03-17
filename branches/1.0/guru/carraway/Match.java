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

    protected Expr simpleTypeCase(Context ctxt, Case C) {
	Expr cT = ctxt.getType(C.c);
	if (C.vars.length == 0) {
	    if (cT.construct != SYM)
		classifyError(ctxt,"A constructor given as the pattern of a match-case has a type which is not a datatype.\n\n"
			      +"1. the constructor: "+C.c.toString(ctxt)
			      +"\n\n2. its type: "+cT.toString(ctxt));
	    return C.body.simpleType(ctxt);
	}

	if (cT.construct != FUN_TYPE)
	    classifyError(ctxt,"The constructor heading the pattern of a match-case has an unexpected type.\n\n"
			  +"1. the constructor: "+C.c.toString(ctxt)
			  +"\n\n2. its type: "+cT.toString(ctxt));
	
	FunType f = (FunType)cT;
	FunType rf = (FunType)ctxt.getCtorRuntimeType(C.c);
	
	if (f.vars.length != C.vars.length)
	    classifyError(ctxt,
			  "The constructor heading the pattern of a match-case is applied to the wrong number of pattern variables.\n\n"
			  +"1. the constructor: "+C.c.toString(ctxt)
			  +"\n\n2. its type: "+cT.toString(ctxt));
	for (int i = 0, iend = C.vars.length; i < iend; i++) {
	    Expr vT = f.types[i].applySubst(ctxt);
	    ctxt.setType(C.vars[i], vT);
	    ctxt.setSubst(f.vars[i],C.vars[i]);
	    if (rf.types[i].construct != UNTRACKED) {
		// we have a runtime type for this var

		Sym rt = (Sym)rf.types[i];
		
		Sym q = null;
		if (f.types[i].construct == SYM)
		    q = f.types[i];
		else
		    q = ((Pin)f.types[i]).s;

		Context.InitH h = ctxt.getInit(s,q);

		if (h == null)
		    C.classifyError(ctxt, "Missing an initialization function in a match-case.\n\n"
				    +"1. the pattern variable: "+C.vars[i].toString(ctxt)
				    +"\n\n2. its type: "+vT.toString(ctxt)
				    +"\n\n3. the scrutinee's type: "+s.toString(ctxt));

		Expr i = new InitTerm(h,rt,(ctxt.isVar(t) ? (Sym)t : null),C.vars[i]);
		i.pos = C.pos;
		body = new Let(C.vars[i],i,body);
		body.pos = C.pos;
	    }
	}

	// clear the substitution of f's vars now.
	for (int i = 0, iend = vars.length; i < iend; i++) 
	    ctxt.setSubst(f.vars[i],null);
	
	return C.body.simpleType(ctxt);
    }

    public Expr simpleType(Context ctxt) {
	Expr expected = null;
	Expr T = t.simpleType(ctxt);
	if (s == null)
	    s = ctxt.getDatatype(C[0].c);
	for (int i = 0, iend = C.length; i < iend; i++) {
	    Expr CT = simpleTypeCase(ctxt,C[i]);
	    if (expected == null)
		expected = CT;
	    else
		if (!CT.eqType(ctxt,expected))
		    classifyError(ctxt,"The type computed for a match-case is different from the one expected from the earlier cases.\n\n"
				  +"1. the case: "+C[i].c.toString(ctxt)
				  +"\n\n2. the computed type: "+CT.toString(ctxt)
				  +"\n\n3. the expected type: "+expected.toString(ctxt));
	}
	return expected;
    }

}