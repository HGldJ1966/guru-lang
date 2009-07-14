package guru.carraway;
import guru.Position;
import java.util.HashSet;
import java.util.Collection;
import java.util.Iterator;

public class Match extends Expr {
    public Expr t; // scrutinee
    public boolean consume_first; // should we consume the scrut at the start or end of each case
    public Case[] C;

    Sym x; // var naming the scrutinee
    Sym s; // datatype of first pattern
    boolean untracked_scrut;
    Expr rettype; // filled in by simpleType(), used only by linearize()

    public Match(){
	super(MATCH);
    }

    // use during compilation
    public Match(Expr t, Sym x, Sym s, Case[] C, Position p){
	super(MATCH);
	this.t = t;
	this.x = x;
	this.s = s;
	this.C = C;
	// consume_first not used any more
	this.pos = p;
    }

    public void do_print(java.io.PrintStream w, Context ctxt) {
	if (ctxt.stage <= 2) {
	    w.print("match ");
	    if (consume_first)
		w.print("$ ");
	    t.print(w,ctxt);
	    if (x != null) {
		w.print(" as ");
		x.print(w,ctxt);
	    }
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
	else {
	    if (untracked_scrut)
		w.print("switch ((int)");
	    else
		w.print("switch ctor(");
	    t.print(w,ctxt);
	    w.println(") {\n");
	    for(int i = 0, iend = C.length; i < iend; i++) {
		C[i].print(w,ctxt);
		w.println("");
	    }
	    w.println("default:\n");
	    w.println("fprintf(stderr,\"Match failure at: "+pos.toStringNoQuotes()+"\\n\"); exit(EXIT_FAILURE);\n");
	    w.println("}");
	}
    }    

    protected Expr simpleTypeCase(Context ctxt, Case C, Expr scrut_t) {
	Expr cT = ctxt.getType(C.c);
	if (C.vars.length == 0) {
	    if (cT.construct != SYM && cT.construct != UNTRACKED)
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

	/* first map the variables from the ctor's type to the pattern
	   vars, and set the types of the pattern vars.  This must be
	   done first in this order, because next we will modify the
	   body by wrapping it in one let-construct for each pattern
	   var -- and that has to be done in reverse order. */

	for (int i = 0, iend = C.vars.length; i < iend; i++) {
	    Expr vT = f.types[i].applySubst(ctxt);
	    ctxt.setType(C.vars[i], vT);
	    ctxt.setSubst(f.vars[i],C.vars[i]);
	}

	for (int i = C.vars.length - 1; i >= 0; i--) {
	    if (rf.types[i].construct != UNTRACKED) {
		// we have a runtime type for this var

		Sym rt = null;
		try {
		    rt = (Sym)rf.types[i].applySubst(ctxt);
		}
		catch(Exception e) {
		    C.classifyError(ctxt,"Internal error: the runtime type we have for a constructor argument"
				    +"\nis untracked, but not a symbol."
				    +"\n\n1. the constructor: "+C.c.toString(ctxt)
				    +"\n\n2. the argument: "+C.vars[i].toString(ctxt)
				    +"\n\n3. its runtime type: "+rf.types[i].applySubst(ctxt).toString(ctxt));
		}
		
		Sym q = null;
		if (f.types[i].construct == SYM)
		    q = (Sym)f.types[i];
		else
		    q = ((Pin)f.types[i]).s;

		if (scrut_t.construct == UNTRACKED) {
		    Expr vT = ctxt.getType(C.vars[i]);
		    C.classifyError(ctxt, "A match-term requires initialization from untracked data.\n\n"
				    +"1. the pattern variable: "+C.vars[i].toString(ctxt)
				    +"\n\n2. its type: "+vT.toString(ctxt)
				    +"\n\n3. the scrutinee's type: "+scrut_t.toString(ctxt));
		}

		Context.InitH h = ctxt.getInit((Sym)scrut_t,q);

		if (h == null) {
		    Expr vT = ctxt.getType(C.vars[i]);
		    C.classifyError(ctxt, "An initialization function is missing for a variable in a match-case.\n\n"
				    +"1. the pattern variable: "+C.vars[i].toString(ctxt)
				    +"\n\n2. its type: "+vT.toString(ctxt)
				    +"\n\n3. the scrutinee's type: "+scrut_t.toString(ctxt));
		}

		Expr n = new InitTerm(h,rt,x,s,C.c,rf.vars[i],C.vars[i]);
		n.pos = C.pos;
		Position p = C.body.pos;
		C.body = new Let(C.vars[i],n,C.body);
		C.body.pos = p;
	    }
	    else {
		Expr n = new InitTerm(null,null,x,s,C.c,rf.vars[i],C.vars[i]);
		n.pos = C.pos;
		Position p = C.body.pos;
		C.body = new Let(C.vars[i],n,C.body);
		C.body.pos = p;
	    }
	}

	// clear the substitution of f's vars now.
	for (int i = 0, iend = f.vars.length; i < iend; i++) 
	    ctxt.setSubst(f.vars[i],null);
	
	return C.body.simpleType(ctxt);
    }

    public Expr simpleType(Context ctxt) {
	if (t.construct == SYM) 
	    x = (Sym)t;
	else 
	    x = ctxt.newVar(pos);

	Expr expected = null;
	Expr T = t.simpleType(ctxt);

	Expr scrut_t = null;
	if (T.construct == SYM && ctxt.isResourceType((Sym)T))
	    scrut_t = (Sym)T;
	else if (T.construct == PIN)
	    scrut_t = ((Pin)T).s;
	else if (T.construct == UNTRACKED) {
	    untracked_scrut = true;
	    scrut_t = T;
	}
	else
	    classifyError(ctxt,"The type computed for a scrutinee is not an attribute or pin-type.\n\n"
			  +"1. the scrutinee: "+t.toString(ctxt)
			  +"\n\n2. its type: "+T.toString(ctxt));

	if (s == null)
	    s = ctxt.getDatatype(C[0].c);
	for (int i = 0, iend = C.length; i < iend; i++) {
	    Expr CT = simpleTypeCase(ctxt,C[i],scrut_t);
	    if (expected == null)
		expected = CT;
	    else
		if (!CT.eqType(ctxt,expected))
		    classifyError(ctxt,"The type computed for a match-case is different from the one expected from the earlier cases.\n\n"
				  +"1. the case: "+C[i].c.toString(ctxt)
				  +"\n\n2. the computed type: "+CT.toString(ctxt)
				  +"\n\n3. the expected type: "+expected.toString(ctxt));
	}

	if (!ctxt.isNotConsumed(x) && scrut_t.construct != UNTRACKED) {

	    // we are consuming x, so include cleanup code at the end of each case.
	    for (int i = 0, iend = C.length; i < iend; i++) {
		Sym dropf = ctxt.getDropFunction((Sym)scrut_t);
		Expr drop = new DropTerm(dropf,s,x,consume_first);
		drop.pos = C[i].lastpos;
		
		if (consume_first) {
		    Do tmp = new Do();
		    tmp.pos = C[i].body.pos;
		    tmp.ts = new Expr[2];
		    tmp.ts[0] = drop;
		    tmp.ts[1] = C[i].body;
		    C[i].body = tmp;
		}
		else {
		    if (expected.construct == VOID) {
			Do tmp = new Do();
			tmp.pos = C[i].body.pos;
			tmp.ts = new Expr[2];
			tmp.ts[0] = C[i].body;
			tmp.ts[1] = drop;
			C[i].body = tmp;
		    }
		    else {
			Let tmp1 = new Let();
			tmp1.pos = C[i].body.pos;
			tmp1.x = ctxt.newVar(C[i].body.pos);
			tmp1.t1 = C[i].body;
			
			Do tmp = new Do();
			tmp.pos = C[i].body.pos;
			tmp.ts = new Expr[2];
			tmp.ts[0] = drop;
			tmp.ts[1] = tmp1.x;
			
			tmp1.t2 = tmp;
			
			C[i].body = tmp1;
		    }
		}
	    }
	}

	rettype = expected;

	return expected;
    }

    protected Context.RefStat findRef(Context ctxt, Sym r, Collection c) {
	Iterator it = c.iterator();
	if (ctxt.getFlag("debug_findRef")) {
	    ctxt.w.println("\nfindRef, r = "+r.refString(ctxt)+"(");
	    ctxt.w.flush();
	}
	while (it.hasNext()) {
	    Context.RefStat u = (Context.RefStat)it.next();
	    if (ctxt.getFlag("debug_findRef")) {
		ctxt.w.println("  -- "+u.ref.refString(ctxt));
		ctxt.w.flush();
	    }
		
	    if (u.ref == r) {
		if (ctxt.getFlag("debug_findRef")) {
		    ctxt.w.println(") found the reference.\n");
		    ctxt.w.flush();
		}
		return u;
	    }
	}
	if (ctxt.getFlag("debug_findRef")) {
	    ctxt.w.println(") did not find the reference r = "+r.refString(ctxt)+".\n");
	    ctxt.w.flush();
	}
	return null;
    }

    // try to return a RefStat that is in c1 but whose ref does not have a RefStat in c2.
    protected Context.RefStat findDiff(Context ctxt,Collection c1, Collection c2) {
	Iterator it = c1.iterator();
	while (it.hasNext()) {
	    Context.RefStat u = (Context.RefStat)it.next();
	    if (findRef(ctxt,u.ref,c2) == null)
		return u;
	}
	return null;
    }

    protected void printRefs(java.io.PrintStream w, Context ctxt, Collection c) {
	Iterator it = c.iterator();
	while (it.hasNext()) {
	    Context.RefStat u = (Context.RefStat)it.next();
	    u.print(ctxt.w,ctxt);
	}
    }

    public Sym simulate_h(Context ctxt, Position p) {
	Sym r = t.simulate(ctxt,pos);
	if (r == null)
	    return null;
	Sym prev_x = ctxt.getSubst(x);
	ctxt.setSubst(x,r);
	Collection[] S = new Collection[C.length];
	Sym[] rs = new Sym[C.length];
	Context.RefStat ret_data = null;
	for (int i = 0, iend = C.length; i < iend; i++) {
	    ctxt.checkpointRefs();

	    rs[i] = C[i].simulate(ctxt,pos);

	    // consume the reference produced by the case (the case checks to make sure the reference is returnable).
	    Context.RefStat s1 = ctxt.refStatus(rs[i]);
	    if (s1 == null) {
		// rs[i] must be untracked
		if (ctxt.getFlag("debug_refs")) {
		    ctxt.w.println("Reference "+rs[i].toString(ctxt)+" returned by case is untracked.");
		    ctxt.w.flush();
		}
	    }
	    else {
		if (rs[i] != null) {
		    if (ret_data == null)
			ret_data = ctxt.refStatus(rs[i]);
		    else 
			if (!ret_data.pinnedby.equals(s1.pinnedby) ||
			    !ret_data.pinning.equals(s1.pinning))
			    simulateError(ctxt,"The reference returned in a match-case has a different pinning/pinnedby profile than "
					  +"\nthe earlier cases.\n\n"
					  +"1. the case: "+C[i].c.toString(ctxt)
					  +"\n\n2. its reference profile:\n"+s1.toString(ctxt)
					  +"\n\n3. the earlier cases' reference profile:\n"+ret_data.toString(ctxt));
		    
		    ctxt.dropRef(rs[i],C[i],C[i].lastpos);
		}
	    }

	    S[i] = ctxt.restoreRefs();
	}

	/* check that the cases create and consume references in the allowed way:
	   
	   1. any created references must be consumed, except the one returned by the case.
	   2. any references existing before the checkpoint are consumed the same way in
   	      all cases.

           In the loop just below, we check (1) and compute the set of dropped references
           which existed before the checkpoint.
	*/

	HashSet[] S2 = new HashSet[C.length];
	for (int i = 0, iend = C.length; i < iend; i++) {
	    if (rs[i] == null) {
		S2[i] = null;
		continue;
	    }
	    S2[i] = new HashSet(256);
	    Iterator it = S[i].iterator();
	    while (it.hasNext()) {
		Context.RefStat u = (Context.RefStat)it.next();
		if (u.dropping_expr == null) {
		    if (u.ref != rs[i])
			C[i].simulateError(ctxt,"A reference created in a case but not returned by it is being leaked.\n\n"
					   +"1. "+u.ref.refString(ctxt,u));
		    continue;
		}
		
		if (ctxt.refStatus(u.ref) != null) 
		    // this reference existed before
		    S2[i].add(u);
	    }
	}

	// check that the sets of dropped pre-existing references are the same

	HashSet first = null;
	for (int i = 0, iend = C.length; i < iend; i++) {
	    if (S2[i] == null)
		continue;
	    if (ctxt.getFlag("debug_simulate")) {
		ctxt.w.println("Dropped pre-existing references for match-case "+C[i].c.toString(ctxt)+":");
		printRefs(ctxt.w, ctxt, S2[i]);
	    }
	    if (first == null) {
		first = S2[i];
		continue;
	    }
	    Expr e1 = null, e2 = null;
	    Position p1 = null, p2 = null;
	    Context.RefStat u = findDiff(ctxt,first,S2[i]);
	    if (u == null) {
		u = findDiff(ctxt,S2[i],first);
		if (u == null)
		    // the sets are the same
		    continue;
		else {
		    e2 = u.dropping_expr;
		    p2 = u.dropping_pos;
		}
	    }
	    else {
		e1 = u.dropping_expr;
		p1 = u.dropping_pos;
	    }

	    C[i].simulateError(ctxt,"Two match-cases consume different sets of earlier references.\n\n"
			       +"1. the first case: "+C[0].c.toString(ctxt)
			       +"\n\n2. the second case: "+C[i].c.toString(ctxt)
			       +"\n\n3. " +u.ref.refString(ctxt)
			       +"\n\n4. the first case "+(p1 == null ? "does not consume it." : "consumes it at "+e1.toString(ctxt) + " ("+p1.toString()+")")
			       +"\n\n5. the second case "+(p2 == null ? "does not consume it." : "consumes it at: "+e2.toString(ctxt) + " ("+p2.toString()+")"));
	}
	
	ctxt.setSubst(x,prev_x);

	if (first == null)
	    // all cases abort
	    return null;

	// drop the pre-existing references that are dropped in all cases

	Iterator it = first.iterator();
	while(it.hasNext()) {
	    Context.RefStat u = (Context.RefStat)it.next();
	    if (u.dropping_expr != null)
		ctxt.dropRef(u.ref,u.dropping_expr,u.dropping_pos);
	}

	if (ret_data == null)
	    // this can only happen if we are returning void
	    return ctxt.voidref;

	return ctxt.newRef(this,pos,ret_data.non_ret,ret_data.consume);
    }

    public Expr linearize(Context ctxt, guru.Position p, Sym dest, Collection decls, Collection defs) {
	boolean toplevel = (dest != null);
	if (dest == null && rettype.construct != VOID)
	    dest = ctxt.newVar(pos);
	Expr nt = null;
	if (t != x) {
	    decls.add(x);
	    nt = t.linearize(ctxt,pos,x /* var naming scrutinee */,
			     decls,defs);
	}

	Case[] nC = new Case[C.length];
	for (int i = 0, iend = C.length; i < iend; i++) {

	    // linearize each body in a new scope (we are calling Expr.linearize())

	    Expr nbody = C[i].body.linearize(ctxt,pos,dest);
	    nC[i] = new Case(C[i].c,nbody,C[i].pos);
	}
	Match m = new Match(x,x,s,nC,pos);
	m.untracked_scrut = untracked_scrut; // needed for stage 3 printing.
	if (toplevel)
	    if (nt != null)
		return new Do(nt,m,pos);
	    else
		return m;
	if (nt != null)
	    defs.add(nt);
	defs.add(m);
	return dest;
    }
}