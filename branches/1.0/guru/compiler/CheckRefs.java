package guru.compiler;

import guru.*;
import java.util.*;
import java.io.*;

// use this after the SplitByArity phase

public class CheckRefs {
    Context ctxt;
    
    int nextvar;

    // remember that these are from the function's perspective,
    // telling whether the reference is owned by the caller.  
    // So OWNED means that the caller owns the reference.
    public static final int OWNEDBY = Ownership.OWNEDBY;
    public static final int UNOWNED = Ownership.UNOWNED;
    public static final int UNIQUE_UNOWNED = Ownership.UNIQUE;
    public static final int NOT_TRACKED = Ownership.NOT_TRACKED;
    public static final int UNIQUE_OWNEDBY = Ownership.UNIQUE_OWNEDBY;
    public static final int NEW = Ownership.NEW;
    public static final int KILLED = Ownership.KILLED;

    protected boolean dbg, dbg_check_refs;

    public CheckRefs() { nextvar = 0; }

    public void handleError(Position pos, NamedHashMap st,
			    String msg) {
	if (pos != null) {
	    pos.print(System.out);
	    System.out.print(": ");
	}
	System.out.println("reference counting error.\n"
			   +"State: "+st.toString()+"\n"+msg);
	System.exit(6);
    }

    static class Status {
	Ownership o;
	Expr e;
	Status(Ownership o, Expr e) {
	    this.o = o;
	    this.e = e;
	}
    }

    /* We need to add typing information for new references to the
       context, because we are going to call the type checker on terms
       during simulation.  This must be done so that we can compute
       types for functional references, introduced as the results of
       applications. */
    protected Var nextTmp(HashMap st, Ownership status, Expr source, Expr T) {
	Var tmp = new Var("ref"+(new Integer(nextvar++)).toString());
	if (dbg) {
	    ctxt.w.println("Creating new reference "+tmp.toString(ctxt)
			   +" from: "+source.toString(ctxt));
	    ctxt.w.flush();
	} 
	setStatus(st,tmp,source,status);
	ctxt.setClassifier(tmp,T);
	return tmp;
    }

    public static class NamedHashMap extends HashMap {
	protected String name;
	public NamedHashMap(String name) {
	    super();
	    this.name = name;
	}
	public NamedHashMap(String ext, NamedHashMap m) {
	    super(m);
	    this.name = m.name + ":" + ext;
	}
	public String toString() {
	    return name;
	}
    }

    protected void checkConsumed(NamedHashMap st, Expr r, Const c, Position pos) {
	Iterator it2 = st.keySet().iterator();
	while(it2.hasNext()) {
	    Expr x = (Expr)it2.next();
	    if (x == r)
		// this is the returned reference.
		continue;
	    
	    Status s = (Status)st.get(x);
	    if (s.o.status == UNOWNED || s.o.status == UNIQUE_UNOWNED) 
		handleError(pos, st,
			    "The term \""+c.name+"\" is not consuming"
			    +" the reference "+x.toString(ctxt)
			    +",\nassociated with this source term:"
			    +"\n1. the source term: "+s.e.toString(ctxt));
	}
    }


    // We assume the terms defined in ctxt are eta-expanded already.
    // We will not bother with checking reference counts for non-functional
    // definitions, but insist they are incremented when used.
    // 
    // The given ctxt will not be modified, although the terms used 
    // in definitions might be, specifically to set the scrut_stat
    // field of match-terms.
    public void checkRefs(Context ctxt) {
	NamedHashMap st = new NamedHashMap("global");

	/*
	 * first collect non-functional consts.  We add declarations
	 * of NOT_TRACKED for things that are not tracked.
	 */

	/* we clone the given context, because we will have to add
	   type declarations for functional references to it that we
	   introduce, and we do not wish to pollute the original. */
	this.ctxt = new Context(ctxt);

	dbg_check_refs = ctxt.getFlag("debug_check_refs");
	dbg = dbg_check_refs;

	Iterator it = ctxt.getDefinedConsts().iterator();
	while(it.hasNext()) {
	    Const c = (Const)it.next();

	    Expr T = ctxt.getClassifier(c);
	    Expr t = ctxt.getDefBody(c);

	    if (!T.isTrackedType(ctxt)) {
		setStatus(st, c, c, new Ownership(NOT_TRACKED));
		continue;
	    }

	    if (dbg) {
		ctxt.w.println("Reference checking non-functional term \""
			       +c.name+"\"");
		ctxt.w.flush();
	    }

	    Expr r;
	    try {
		r = simulate(t, st);
	    }
	    catch(AbortException e) { 
		continue; // with other functions
	    }

	    Status ret_stat = (Status)st.get(r);
	    Ownership o = ret_stat.o;
	    if (o.status == KILLED)
		handleError(t.pos, st,
			    "The term \""+c.name+"\" computes to "
			    +" a killed reference.\n"
			    +"1. the reference: "+r.toString(ctxt)
			    +"\n2. the associated source term: "
			    +ret_stat.e.toString(ctxt));
	    
	    if (o.status == Ownership.UNIQUE)
		o = new Ownership(Ownership.UNIQUE_OWNEDBY);
	    else if (o.status == Ownership.UNOWNED 
		     || o.status == Ownership.NEW)
		o = new Ownership(Ownership.OWNEDBY);

	    checkConsumed(st,r,c,t.pos);

	    st.remove(r);
	    setStatus(st, c, t, o);
	}

	/* 
	 * now simulate each function
	 */

	NamedHashMap global_st = st;

	it = ctxt.getDefinedConsts().iterator();
	while(it.hasNext()) {
	    Const c = (Const)it.next();

	    Expr T = ctxt.getClassifier(c);
	    Expr t = ctxt.getDefBody(c);

	    if (t.isTypeOrKind(ctxt) || ctxt.isOpaque(c)
		|| t.construct != Expr.FUN_TERM) 
		// we already handled these in the first loop above
		continue;

	    if (dbg_check_refs) {
		ctxt.w.println("%-----------------------------------------");
		Define D = new Define(false,false,false,false,
				      c,T,t,ctxt.getDefBodyNoAnnos(c));

		ctxt.w.println("Reference checking "+c.name+":");
		D.print(ctxt.w,ctxt);

		ctxt.w.println("");
		ctxt.w.println("");
		ctxt.w.flush();
	    }
	    else if (dbg) {
		ctxt.w.println("%-----------------------------------------");
		ctxt.w.println("Reference checking \""+c.name+"\"");
		ctxt.w.flush();
	    }

	    FunTerm f = (FunTerm)t;

	    /* per-call state initialized from global state, so that
	       globals are available. */
	    st = new NamedHashMap(c.name, global_st);

	    // add vars
	    for (int i = 0, iend = f.vars.length; i < iend; i++) {
		Expr Ti = f.types[i].defExpandTop(ctxt);
		setStatus(st, f.vars[i], f, f.owned[i]);
	    }

	    if (f.r != null)
		setStatus(st, f.r, f.r, new Ownership(NOT_TRACKED));

	    Expr r;
	    try {
		r = simulate(f.body, st);
	    }
	    catch(AbortException e) { 
		continue; // with other functions
	    }
	    finally {
		if (f.r != null)
		    st.remove(f.r);
	    }

	    Status ret_stat = (Status)st.get(r);
	    boolean isowned = (ret_stat.o.status == OWNEDBY || 
			       ret_stat.o.status == UNIQUE_OWNEDBY);
	    if (ret_stat.o.status == KILLED || 
		(isowned && ret_stat.o.e == null))
		handleError(t.pos, st,
			    "The function \""+c.name+"\" is returning"
			    +" a globally owned or killed reference.\n"
			    +"1. the reference: "+r.toString(ctxt)
			    +"\n2. the associated source term: "
			    +ret_stat.e.toString(ctxt));
	    
	    if (isowned) {
		Expr e = ret_stat.o.e;
		boolean is_input_var = false;
		for (int i = 0, iend = f.vars.length; i < iend; i++)
		    if (e == f.vars[i]) {
			is_input_var = true;
			break;
		    }
		if (!is_input_var)
		    handleError(t.pos, st,
				"The function \""+c.name+"\" is returning"
				+" a reference not owned by an input"
				+" variable.\n"
				+"1. the reference: "+r.toString(ctxt)
				+"\n2. the associated source term: "
				+ret_stat.e.toString(ctxt)
				+"\n3. the reference is owned by: "+
				e.toString(ctxt));
	    }

	    FunType F = (FunType)T;
	    if (!ret_stat.o.subStatus(F.ret_stat))
		handleError(t.pos, st,
			    "The function \""+c.name+"\" has different "
			    +"computed and declared\nownership statuses for"
			    +" its return value.\n"
			    +"1. declared status: "
			    +F.ret_stat.toString(ctxt)
			    +"\n2. computed status: "
			    +ret_stat.o.toString(ctxt));

	    // check that all references are consumed

	    checkConsumed(st,r,c,t.pos);

	    if (dbg_check_refs) {
		Define D = new Define(false,false,false,false,
				      c,T,t,ctxt.getDefBodyNoAnnos(c));

		ctxt.w.println("Finished reference checking "+c.name+":");
		D.print(ctxt.w,ctxt);

		ctxt.w.println("");
		ctxt.w.println("");
		ctxt.w.flush();
	    }

	}
    }

    protected void checkOtherRefs(Context ctxt,
				  HashMap parent, NamedHashMap child,
				  Expr ret, Position p) {
	Iterator it = child.keySet().iterator();
	while (it.hasNext()) {
	    Expr r = (Expr)it.next();
	    if (parent.containsKey(r))
		continue;
	    if (r == ret)
		continue;
	    Status s = (Status)child.get(r);
	    if (s.o.status != OWNEDBY && 
		s.o.status != UNIQUE_OWNEDBY && 
		s.o.status != KILLED && 
		s.o.status != NOT_TRACKED)
		handleError(p, child,
			    "A reference created in a case of a match-term"
			    +" is not\nbeing consumed in that case.\n"
			    +"1. the state for the case: "+child.toString()
			    +"\n2. the reference: "+r.toString(ctxt)
			    +"\n3. the associated source term: "
			    +s.e.toString(ctxt));
	}
    }

    /* update the status of all references in parent to have the
       status they have in child. */
    protected void updateParent(Context ctxt, HashMap parent, HashMap child) {
	if (dbg_check_refs) {
	    ctxt.w.println("Updating "+parent.toString());
	    ctxt.w.flush();
	}
	Iterator it = child.keySet().iterator();
	while (it.hasNext()) {
	    Expr r = (Expr)it.next();
	    if (parent.containsKey(r)) {
		Status s = (Status)child.get(r);
		Status ps = (Status)parent.get(r);
		if (s.o.status != ps.o.status)
		    setStatus(parent, r, s.e, s.o);
	    }
	}
    }

    /* make sure that

       1. st1 and st2 agree on all references from their parent.
       2. all other references except ret1 for st1 and ret2 for st2
          are OWNED.

       The states will be modified in an unspecified way in the process.
    */
    protected void statesCompatible(Context ctxt,
				    NamedHashMap parent, 
				    NamedHashMap st1, NamedHashMap st2,
				    Position p) {
	Iterator it = parent.keySet().iterator();
	while (it.hasNext()) {
	    Expr r = (Expr)it.next();
	    Status s1 = (Status)st1.get(r);
	    Status s2 = (Status)st2.get(r);
	    if (s1.o.status != s2.o.status)
		handleError(p, parent,
			    "The states resulting from two cases of a"
			    +" match-term have different ownership\n"
			    +"status for the same reference.\n"
			    +"1. the first state: "
			    +st1.toString()+"\n"
			    +"2. the second state: "
			    +st2.toString()+"\n"
			    +"3. the reference: "+r.toString(ctxt)
			    +"\n4. the associated source term: "
			    +s1.e.toString(ctxt)
			    +"\n5. the status in the first case: "
			    +s1.o.toString(ctxt)
			    +"\n6. the status in the second case: "
			    +s2.o.toString(ctxt));
	}
    }

    public Expr[] simulate(Expr[] X, NamedHashMap st) throws AbortException {
	int iend = X.length;
	Expr[] nX = new Expr[iend];
	for (int i = 0; i < iend; i++)
	    nX[i] = simulate(X[i], st);
	return nX;
    }

    static public class AbortException extends Exception { 
	AbortException() { super(); }
    }

    protected void setStatus(HashMap st, Expr x, Expr srce, Ownership status) {
	if (dbg_check_refs) {
	    ctxt.w.println(x.toString(ctxt) + " to "
			   + status.toString(ctxt) + " in " 
			   + st.toString());
	    ctxt.w.flush();
	}
	st.put(x, new Status(status, srce));
    }

    // consume r with given new ownership status.
    protected void consumeRef(NamedHashMap st, Expr r, Ownership ownership) {
	Status s = (Status)st.get(r);
	if (ownership.status == UNOWNED || ownership.status == UNIQUE_UNOWNED) 
	    setStatus(st, r, s.e, new Ownership(KILLED));
	else if (ownership.status == OWNEDBY) {
	    if (s.o.status == NEW)
		setStatus(st, r, s.e, new Ownership(UNOWNED));
	    // otherwise, we do not change the status 
	}
	// if (ownership == UNIQUE_OWNED) we do not change the status.
    }

    /* if var_owned is the nominal status of a pattern variable
       matching (part of) a scrutinee with reference ref which has
       OWNED or UNIQUE_OWNED status, then compute the actual status to
       use for that pattern variable in the match case. */
    static public Ownership patternVarStatus(Expr owner, 
					     Ownership ref_stat,
					     Ownership var_owned) {
	if (ref_stat.status == OWNEDBY ||
	    ref_stat.status == UNIQUE_OWNEDBY)
	    owner = ref_stat.e;
	if (var_owned.status == UNOWNED) 
	    return new Ownership(OWNEDBY, owner);
	if (var_owned.status == UNIQUE_UNOWNED)
	    return new Ownership(UNIQUE_OWNEDBY, owner);
	return var_owned;
    }

    public Expr simulate(Expr e, NamedHashMap st) throws AbortException {
	if (dbg_check_refs) {
	    ctxt.w.println("Simulating term { "+e.toString(ctxt));
	    ctxt.w.flush();
	}

	Expr ret = null;
	switch (e.construct) {
	case Expr.IMPOSSIBLE:
	case Expr.ABORT:
	    throw new AbortException();
	case Expr.VAR:
	    ret = e;
	    break;
	case Expr.STRING_EXPR: 
	    ret = simulate(((StringExpr)e).expand(ctxt), st);
	    break;
	case Expr.CONST: {
	    Const c = (Const)e;
	    if (ctxt.isDefined(c)) {
		ret = e;
		break;
	    }

	    // c is a term or type ctor.
	    
	    Expr T = ctxt.getClassifier(c);
	    if (T.isTrackedType(ctxt)) {
		/* this will be compiled to C code calling a function
		   to create an element representing this 0-ary ctor.
		   So we must return a new reference here. */
		ret = nextTmp(st,new Ownership(NEW),c,T);
		break;
	    }

	    setStatus(st, c, c, new Ownership(NOT_TRACKED));
	    ret = c;
	    break;
	}
	case Expr.LET: {
	    Let l = (Let)e;
	    Expr r1 = simulate(l.t1, st);
	    Status s = (Status)st.get(r1);
	    if (l.x1_stat.status == UNOWNED && s.o.status != UNOWNED) {
		/* UNOWNED is the default, which we allow to be filled
		   in with other ownership statuses. */
		if (dbg_check_refs) {
		    ctxt.w.println("Changing status of let-bound variable "
				   +l.x1.toString(ctxt)
				   +" to: "
				   +s.o.toString(ctxt));
		    ctxt.w.flush();
		} 
		l.x1_stat = s.o; 
	    }
	    if (!s.o.subStatus(l.x1_stat))
		handleError(e.pos, st,
			    "A let-term is changing the ownership view "
			    +"of its first subterm\nin a disallowed way.\n"
			    +"1. the first subterm: "+l.t1.toString(ctxt)
			    +"\n2. the corresponding reference: "
			    +r1.toString(ctxt)
			    +"\n3. its ownership status: "
			    +s.o.toString(ctxt)
			    +"\n4. the new status from the let-term: "
			    +l.x1_stat.toString(ctxt));
	    if (l.x1_stat.status == OWNEDBY
		|| l.x1_stat.status == UNIQUE_OWNEDBY) {
		setStatus(st, l.x1, l.t1, l.x1_stat);
		ret = simulate(l.t2, st);
		break;
	    }
	    
	    /* kill the reference produced, and create a new one.
	       We cannot just substitute r1 for l.x1 here, because
	       we are modifying expressions by setting statuses in
	       match- and let-terms. */
	    setStatus(st, r1, l.t1, new Ownership(KILLED));
	    setStatus(st, l.x1, r1, s.o);
	    ret = simulate(l.t2, st);
	    break;
	}
	case Expr.CAST: {
	    Cast c = (Cast)e;
	    Expr r = simulate(c.t, st);
	    if (!c.T.isTrackedType(ctxt))
		setStatus(st, r, c, new Ownership(NOT_TRACKED));
	    ret = r;
	    break;
	}
	case Expr.MATCH: {
	    Match m = (Match)e;
	    Expr nt = simulate(m.t,st);
	    Status s = (Status)st.get(nt);
	    m.scrut_stat = s.o;
	    Expr scruttp = m.t.classify(ctxt,Expr.APPROX_TRIVIAL,false);
	    if (!scruttp.isTrackedType(ctxt))
		m.scrut_stat = new Ownership(Ownership.NOT_TRACKED);

	    if (dbg_check_refs) {
		ctxt.w.println("Scrutinee's status for this match-term is: "
			       +m.scrut_stat.toString(ctxt));
		ctxt.w.flush();
	    }
	    if (m.scrut_stat.status == KILLED)
		handleError(e.pos, st,
			    "The scrutinee of a match-term has been killed"
			    +" before\nthe match begins.\n"
			    +"1. the scrutinee: "+m.t.toString(ctxt)+"\n"
			    +"2. the corresponding reference: "
			    +nt.toString(ctxt));
	    if (m.scrut_stat.status == UNOWNED
		|| m.scrut_stat.status == UNIQUE_UNOWNED
		|| m.scrut_stat.status == NEW)
		// match consumes unowned references
		setStatus(st,nt,s.e,new Ownership(KILLED));
	    int iend = m.C.length;
	    Ownership first_stat = null;
	    Expr first_ref = null;
	    NamedHashMap first_st = null;
	    boolean all_aborted = true;
	    for (int i = 0; i < iend; i++) {

		// for each case of the match-term

		Case C = m.C[i];
		if (C.impossible)
		    continue;
		String cstr = C.getPattern().toString(ctxt);
		if (dbg_check_refs)
		    ctxt.w.println("Starting match case: "+cstr);
		NamedHashMap stc = new NamedHashMap(cstr, st);
		Expr T = ctxt.getClassifier(C.c);
		for (int j = 0, jend = C.x.length; j < jend; j++) {
		    FunType F = (FunType)T;
		    Ownership varstat = F.owned[0];
		    Expr vT = ctxt.getClassifier(C.x[j]);
		    if (dbg) {
			ctxt.w.println("Pattern var "+C.x[j].toString(ctxt)
				       +" : "+vT.toString(ctxt)
				       + " def. eq. to "
				       +(vT.defExpandTop(ctxt,false,false)
					 .toString(ctxt)));
			ctxt.w.flush();
		    }
		    if (!vT.isTrackedType(ctxt))
			/* this can happen when varstat at this point
			   is unowned, due to type refinement */
			varstat = new Ownership(Ownership.NOT_TRACKED);
		    else
			if (m.scrut_stat.status == OWNEDBY
			    || m.scrut_stat.status == UNIQUE_OWNEDBY)
			    varstat = patternVarStatus(nt,m.scrut_stat,varstat);
		    setStatus(stc, C.x[j], C, varstat);
		    T = F.next();
		}

		Expr b;
		try {
		    b = simulate(C.body, stc);
		}
		catch(AbortException ae) {
		    continue; // with the other cases
		}

		all_aborted = false;
		Status tmpstat = (Status)stc.get(b);
		Ownership bstat = tmpstat.o;

		/* we must now consume this reference if it is UNOWNED.
		   In that case, we will produce a new UNOWNED reference
		   for the whole match-term. But we will kill this reference,
		   to signal that it was consumed. */

		Ownership newbstat = bstat;
		if (bstat.status == UNOWNED || bstat.status == UNIQUE_UNOWNED)
		    newbstat = new Ownership(KILLED);
		setStatus(stc,b,tmpstat.e,newbstat);

		checkOtherRefs(ctxt,st,stc,b,e.pos);

		if (first_st == null) {
		    first_st = stc;
		    first_ref = b;
		    first_stat = bstat;
		}
		else {
		    /* make sure results are consistent across cases,
		       and update first_state, which will be the status
		       of the returned reference, if necessary. */
		    if ((first_stat.status == NEW && 
			 bstat.status == UNOWNED) 
			||
			(first_stat.status == UNOWNED && 
			 bstat.status == NEW))
			first_stat = new Ownership(UNOWNED);
		    else if ((first_stat.status == NEW
			      && bstat.status == UNIQUE_UNOWNED)
			     || 
			     (first_stat.status == UNIQUE_UNOWNED
			      && bstat.status == NEW))
			first_stat = new Ownership(UNIQUE_UNOWNED);
		    else if (first_stat.status != bstat.status)
			handleError(C.pos, st,
				    "Different cases in a match return "
				    +"references with different\nownership"
				    +" status.\n"
				    +"1. first case: "
				    +m.C[0].getPattern().toString(ctxt)
				    +"\n2. its body's ownership status: "
				    +first_stat.toString(ctxt)
				    +"\n"
				    +"3. differing case: "
				    +C.getPattern().toString(ctxt)
				    +"\n4. its body's ownership status: "
				    +bstat.toString(ctxt));
		    statesCompatible(ctxt, st, first_st, stc, e.pos);
		}
	    }
	    if (all_aborted)
		throw new AbortException();
	    updateParent(ctxt, st, first_st);
	    ret = nextTmp(st, first_stat, e, m.T /* bodies' type */);
	    break;
	}
	case Expr.INC: {
	    Inc i = (Inc)e;
	    Expr r = simulate(i.t,st);
	    Status s = (Status)st.get(r);
	    if (s.o.status == KILLED)
		handleError(e.pos, st,
			    "A killed reference is being incremented.\n"
			    +"\n1. the source term: "
			    +i.t.toString(ctxt)
			    +"\n2. the associated reference: "
			    +r.toString(ctxt));
	    if (s.o.status == UNIQUE_UNOWNED || s.o.status == UNIQUE_OWNEDBY)
		handleError(e.pos, st,
			    "A unique reference is being incremented.\n"
			    +"\n1. the source term: "
			    +i.t.toString(ctxt)
			    +"\n2. the associated reference: "
			    +r.toString(ctxt));
	    if (s.o.status == NOT_TRACKED)
		handleError(e.pos, st,
			    "An untracked reference is being incremented.\n"
			    +"\n1. the source term: "
			    +i.t.toString(ctxt)
			    +"\n2. the associated reference: "
			    +r.toString(ctxt));

	    if (s.o.status == NEW)
		/* we are duplicating a NEW resource, so the old
		   ref must change to UNOWNED (since it is no longer
		   legal to change it to UNIQUE). */
		setStatus(st, i.t, s.e, new Ownership(UNOWNED));

	    ret = nextTmp(st, new Ownership(UNOWNED), i.t, 
			  i.t.classify(ctxt,Expr.APPROX_TRIVIAL,false));
	    break;
	}
	case Expr.DEC: {
	    Dec d = (Dec)e;
	    Expr nI = simulate(d.I, st);
	    Status s = (Status)st.get(nI);
	    if (s.o.status == OWNEDBY || s.o.status == KILLED ||
		s.o.status == UNIQUE_OWNEDBY) 
		handleError(e.pos, st,
			    "A reference that is owned or killed "
			    +"is being decremented.\n"
			    +"\n1. the reference: "+nI.toString(ctxt)
			    +"\n2. the associated source expression: "
			    +s.e.toString(ctxt)
			    +"\n3. the dec-term: "
			    +e.toString(ctxt));
	    if (s.o.status == NOT_TRACKED)
		handleError(e.pos, st,
			    "An untracked reference is being decremented.\n"
			    +"\n1. the source term: "
			    +s.e.toString(ctxt)
			    +"\n2. the associated reference: "
			    +nI.toString(ctxt));

	    setStatus(st,nI,s.e,new Ownership(KILLED));
	    ret = simulate(d.t, st);
	    break;
	}
	case Expr.TERM_APP: {
	    TermApp a = (TermApp)e;

	    FunType F;
	    boolean ctor_head = false; // is the head of a term ctor
	    if (a.head.construct == Expr.CONST) {
		Const c = (Const)a.head;
		F = (FunType)ctxt.getClassifier(c).defExpandTop(ctxt);
		ctor_head = ctxt.isTermCtor(c);
	    }
	    else 
		// note that here, the head could be a reference
		F = (FunType)(ctxt.getClassifier((Var)a.head)
			      .defExpandTop(ctxt));
	    if (dbg && !dbg_check_refs) {
		ctxt.w.println("Simulating application of "
			      +a.head.toString(ctxt));
		ctxt.w.flush();
	    }

	    F = (FunType)F.coalesce(ctxt,false);
	    Expr[] nX = simulate(a.X, st);
	    Ownership[] owned = F.owned;

	    int iend = a.X.length;
	    if (iend != owned.length)
		handleError(e.pos, st,
			    "Internal error: the ownership list in an "
			    +" application is not the same length\n"
			    +"as the ownership list for the applied "
			    +"function.\n"
			    +"1. the application: "+a.toString(ctxt)
			    +"\n2. the type of the head: "+F.toString(ctxt));

	    
	    boolean have_unique_arg = false;
	    HashSet S = new HashSet();
	    for (int i = 0; i < iend; i++) {

		// for each argument

		if (nX[i].isTypeOrKind(ctxt) || nX[i].isProof(ctxt))
		    // nothing to simulate here.
		    continue;
		Status s = (Status)st.get(nX[i]);

		// check some error conditions
		Ownership argstat = s.o;
		Ownership oi = owned[i];

		if (dbg) {
		    ctxt.w.println("Checking substatus relationship before "
				   +"consuming "+nX[i].toString(ctxt)
				   +"\n1. its status: "+argstat.toString(ctxt)
				   +"\n2. parameter status: "+oi.toString(ctxt));
		    ctxt.w.flush();				   
		}

		if (!argstat.subStatus(oi))
		    handleError(e.pos, st,
				"An application is using argument "
				+ (new Integer(i)).toString()
				+ " in a disallowed way\nbased on ownership.\n"
				+"1. the argument: "+a.X[i].toString(ctxt)
				+"\n2. the corresponding reference: "
				+nX[i].toString(ctxt)
				+"\n3. its ownership status: "
				+argstat.toString(ctxt)
				+"\n4. the head of the application: "
				+a.head.toString(ctxt)
				+"\n5. the expected ownership status (from "
				+"the head's type): "
				+oi.toString(ctxt));

		if (argstat.status == NOT_TRACKED)
		    continue; // with other arguments

		have_unique_arg = 
		    (have_unique_arg || (argstat.status == UNIQUE_UNOWNED));

		consumeRef(st, nX[i], oi);
	    }

	    Ownership ret_stat = F.ret_stat;
	    if (ctor_head)
		ret_stat = new Ownership(NEW);

	    /* this is the only place new functional references can be
	       introduced.  If we do introduce such, we need to set its
	       status to be NOT_TRACKED. */

	    Expr eT = e.classify(ctxt, Expr.APPROX_TRIVIAL,false);
	    Ownership tmpstat = (eT.isTrackedType(ctxt) ? ret_stat
				 : new Ownership(NOT_TRACKED));
	    if (have_unique_arg && ctor_head &&
		(tmpstat.status == UNOWNED || tmpstat.status == NEW))
		tmpstat = new Ownership(UNIQUE_UNOWNED);
	    ret = nextTmp(st, tmpstat, e, eT);
	    break;
	}
	default: 
	    // annotations are not tracked
	    ret = nextTmp(st, new Ownership(NOT_TRACKED), e, 
			  e.classify(ctxt,Expr.APPROX_TRIVIAL,false));
	    break;
	}
	
	if (dbg_check_refs) {
	    ctxt.w.println("Finished simulating "+e.toString(ctxt));
	    ctxt.w.println("} returning "+ret.toString(ctxt));
	    ctxt.w.flush();
	}
	return ret;
    }

}