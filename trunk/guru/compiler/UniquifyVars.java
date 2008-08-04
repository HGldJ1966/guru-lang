package guru.compiler;

import guru.*;
import java.util.*;
import java.io.*;

public class UniquifyVars {
    Context ctxt;
    
    HashMap varnums;
    HashSet varnames;

    public UniquifyVars() {
	varnums = new HashMap();
	varnames = new HashSet();
    }

    // we will modify the bodies of defined terms in the given Context.
    public void process(Context ctxt) {
	this.ctxt = ctxt;
	Iterator it = ctxt.getDefinedConsts().iterator();
	while(it.hasNext()) {
	    Const c = (Const)it.next();

	    Expr T = ctxt.getClassifier(c);

	    Expr e = ctxt.getDefBody(c);

	    if (ctxt.isOpaque(c)) 
		continue;

	    process(e);  // including types and terms

	    resetRenaming();
	}

	// we will also uniquify variables in types
	it = ctxt.getTypeCtors().iterator();
	while(it.hasNext()) {
	    Const d = (Const)it.next();

	    Iterator it2 = ctxt.getTermCtors(d).iterator();
	    while (it2.hasNext()) {
		Const c = (Const)it2.next();

		Expr T = ctxt.getClassifier(c);

		process(T);
		
		resetRenaming();
	    }
	}
    }

    public void process(Expr[] X) {
	for (int i = 0, iend = X.length; i < iend; i++)
	    process(X[i]);
    }

    public void process(Expr e) {
	switch (e.construct) {
	case Expr.FUN_TYPE: 
	case Expr.FUN_TERM: {
	    FunAbstraction f = (FunAbstraction)e;
	    String[] names = new String[f.vars.length];
	    Object[] prev = push(f.vars, names);
	    process(f.body);
	    pop(names,f.vars,prev);
	    break;
	}
	case Expr.CONST: 
	case Expr.VAR:
	case Expr.ABORT:
	case Expr.STRING_EXPR:
	    break;
	case Expr.LET: {
	    Let l = (Let)e;
	    String name = l.x1.name;
	    Object prev = push(l.x1);
	    process(l.t1);
	    process(l.t2);
	    pop(name,l.x1,prev);
	    break;
	}
	case Expr.CAST: {
	    Cast c = (Cast)e;
	    process(c.t);
	    break;
	}
	case Expr.INC: {
	    Inc i = (Inc)e;
	    process(i.t);
	    break;
	}
	case Expr.DEC: {
	    Dec d = (Dec)e;
	    process(d.I);
	    process(d.t);
	    break;
	}
	case Expr.CASE: {
	    Case c = (Case)e;
	    String[] names = new String[c.x.length];
	    Object[] prev = push(c.x, names);
	    process(c.body);
	    pop(names,c.x,prev);
	    break;
	}
	case Expr.MATCH: {
	    Match m = (Match)e;
	    process(m.t);
	    for (int i = 0, iend = m.C.length; i < iend; i++) 
		process(m.C[i]);
	    break;
	}
	case Expr.TERM_APP: {
	    TermApp a = (TermApp)e;
	    process(a.head);
	    process(a.X);
	    break;
	}
	default: 
	    // this must be an annotation
	    break;
	}
    }

    protected Object[] push(Var[] x, String[] names) {
	int iend = x.length;
	Object[] prev = new Object[iend];
	for (int i = 0; i < iend; i++) {
	    names[i] = x[i].name;
	    prev[i] = push(x[i]);
	}
	return prev;
    }

    protected Object push(Var x) {
	String varname = x.name;
	String root = varname;
	Integer prev = (Integer)varnums.get(root);
	while(true) {
	    if (!varnames.contains(varname)) {
		varnames.add(varname);
		break;
	    }
	    Integer i = (Integer)varnums.get(root);
	    if (i == null)
		i = new Integer(0);
	    varnums.put(root,new Integer(i.intValue()+1));
	    varname = root+i.toString();
	}
	if (ctxt.getFlag("debug_uniquify_vars")) {
	    ctxt.w.println("Uniquifying "+x.toString(ctxt)+" to "+varname+"(");
	    ctxt.w.flush();
	}
	x.name = varname;
	return prev;
    }

    protected void pop(String[] names, Var[] vars, Object[] prev) {
	for (int i = names.length-1, iend = 0; i >= iend; i--) 
	    pop(names[i],vars[i],prev[i]);
    }

    protected void pop(String varname, Var x, Object prev) {
	if (prev == null) 
	    varnums.remove(varname);
	else
	    varnums.put(varname,prev);
	varnames.remove(x.name);
	if (ctxt.getFlag("debug_uniquify_vars")) {
	    ctxt.w.println(") Restoring "+varname);
	    ctxt.w.flush();
	}
    }

    protected void resetRenaming() {
	if (ctxt.getFlag("debug_uniquify_vars")) {
	    ctxt.w.println("Resetting the renaming.");
	    ctxt.w.flush();
	}   
	varnums = new HashMap();
	varnames = new HashSet();
    }

}