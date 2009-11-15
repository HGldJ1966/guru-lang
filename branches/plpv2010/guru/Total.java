package guru;

public class Total extends Command {
    public Const c;
    public Expr P;

    public Total() {
	super(TOTAL);
    }

    public void process(Context ctxt) {
	Expr tp = ctxt.getClassifier(c);
	if (tp == null)
	    handleError(ctxt,"The constant given to a Total command is missing a type.\n"
			+"1. the constant: "+c.toString(ctxt));
	tp = tp.defExpandTop(ctxt);
	if (tp.construct != Expr.FUN_TYPE)
	    handleError(ctxt,"The constant given to a Total command is not a function.\n"
			+"1. the constant: "+c.toString(ctxt)
			+"\n2. its type: "+tp.toString(ctxt));
	FunType f = (FunType)((FunType)tp).coalesce(ctxt,true);
	
	Expr cP = P.classify(ctxt).defExpandTop(ctxt);
	
	if (cP.construct != Expr.FORALL)
	    handleError(ctxt,"The proof given to a Total command does not prove a universal.\n"
			+"1. the proof: "+P.toString(ctxt)
			+"\n2. the formula it proves: "+cP.toString(ctxt));
	Expr tmp = cP;

	for (int i = 0, iend = f.vars.length; i < iend; i++) {
	    tmp = tmp.defExpandTop(ctxt);
	    if (tmp.construct != Expr.FORALL)
		handleError(ctxt,"A Total command is being given a constant and a proof whose "
			    +"classifiers\ndon't match up properly.  The numbers of variables"
			    +" bound in their classifiers are different.\n"
			    +"1. the constant's type: "+f.toString(ctxt)
			    +"\n2. the proof's formula: "+cP.toString(ctxt));
	    
	    Forall F = (Forall)tmp;
	    
	    if (!f.types[i].defEq(ctxt,F.types[0]))
		handleError(ctxt,"A Total command is being given a constant and a proof whose "
			    +"classifiers\ndon't match up properly.  The types for the "
			    +(new Integer(i)).toString()+"'th bound variable\n"
			    +"in their classifiers are different.\n"
			    +"1. the constant's type: "+f.toString(ctxt)
			    +"\n2. the proof's formula: "+cP.toString(ctxt));
	    
	    tmp = F.instantiate(f.vars[i]);
	}
	    
	Forall F = (Forall)((Forall)cP).coalesce(ctxt,true);
	Expr b = F.body = F.body.defExpandTop(ctxt);

	if (b.construct != Expr.EXISTS)
	    handleError(ctxt,"The proof given to a Total command does not prove a Forall-Exists"
			+" formula.\n"
			+"1. the formula proved: "+cP.toString(ctxt));
	
	Exists E = (Exists)b;
	
	if (E.vars.length != 1)
	    handleError(ctxt,"The proof given to a Total command proves a Forall-Exists"
			+" formula with\nmore than one existential variable.\n"
			+"1. the formula proved: "+cP.toString(ctxt));

	b = E.body = E.body.defExpandTop(ctxt);
	
	if (b.construct != Expr.ATOM)
	    handleError(ctxt,"The proof given to a Total command proves a Forall-Exists"
			+" formula\nwhose body is not an equation.\n"
			+"1. the formula proved: "+cP.toString(ctxt)
			+"\n2. the body: "+b.toString(ctxt));

	Atom A = (Atom)b;

	Expr lhs = A.Y1.defExpandTop(ctxt);
	Expr rhs = A.Y2.defExpandTop(ctxt);

	if (!rhs.defEq(ctxt,E.vars[0]))
	    handleError(ctxt,"The rhs of the Forall-Exists equation proved for a Total "
			+"command\nis not the existential variable.\n"
			+"1. the formula proved: "+cP.toString(ctxt)
			+"\n2. the rhs: "+rhs.toString(ctxt));

	if (lhs.construct != Expr.TERM_APP)
	    handleError(ctxt,"The lhs of the Forall-Exists equation proved for a Total "
			+"command\nis not an application.\n"
			+"1. the formula proved: "+cP.toString(ctxt)
			+"\n2. the lhs: "+lhs.toString(ctxt));

	TermApp a = (TermApp)(lhs = ((TermApp)lhs).spineForm(ctxt,true,true,true));
	
	if (a.head.construct != Expr.CONST)
	    handleError(ctxt,"The lhs of the Forall-Exists equation proved for a Total "
			+"command\nis not an application of a constant.\n"
			+"1. the formula proved: "+cP.toString(ctxt)
			+"\n2. the lhs: "+lhs.toString(ctxt));
	boolean head_mismatch = false;
	Const reg_c = c;
	if (a.head != c) {
	    // just check to see if c might defexpand to a prefix of a. In that case,
	    // reset the Const with which we register this theorem.

	    Expr tmp2 = c.defExpandTop(ctxt);

	    if (tmp2.construct != Expr.TERM_APP)
		head_mismatch = true;
	    else {
		TermApp a2 = (TermApp)((TermApp)tmp2).spineForm(ctxt,true,true,true);
		reg_c = (Const)a.head; // we check above that this is a Const
		head_mismatch = (a2.head != a.head);
	    }
	}
	if (head_mismatch)
	    handleError(ctxt,"The lhs of the Forall-Exists equation proved for a Total "
			+"command\nis not an application of the constant given to Total.\n"
			+"1. the formula proved: "+cP.toString(ctxt)
			+"\n2. the given constant: "+c.toString(ctxt)
			+"\n3. the lhs: "+lhs.toString(ctxt));

	int num_args = a.X.length;
	int num_vars = F.vars.length;
	if (ctxt.getFlag("debug_Total")) {
	    ctxt.w.println("Total: checking that arguments are distinct universal variables."
			   +"\n1. the application: "+a.toString(ctxt)
			   +"\n2. the formula: "+F.toString(ctxt));
	    ctxt.w.flush();
	}
	int j = 0;
	for(int i = 0; i < num_args; i++) {
	    if (j >= num_vars)
		handleError(ctxt,"The lhs of the Forall-Exists equation proved for a Total "
			    +"command\nhas an argument not found (in order) in the list"
			    +" of universal variables.\n"
			    +"1. the formula proved: "+F.toString(ctxt)
			    +"\n2. the argument: "+a.X[i].toString(ctxt)
			    +"\n3. the lhs: "+lhs.toString(ctxt));
	    Expr tmp2 = a.X[i] = a.X[i].defExpandTop(ctxt);
	    if (tmp2.construct != Expr.VAR)
		// skip non-variables
		continue;
	    /* advance which variable we are looking at until we find the 
	       current arg or run out of variables. */
	    while(j < num_vars && !F.vars[j].defEq(ctxt,tmp2))
		j++;
	    ctxt.resetNotDefEq();
	}

	ctxt.registerTotal(reg_c, F);
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	w.println("Total "+c.toString(ctxt)+" by "+P.toString(ctxt));
    }
}
