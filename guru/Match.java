package guru;

import java.util.*;
import java.io.*;

public class Match extends CasesExpr{
    public Expr T;
    public boolean consume_scrut;
    
    public Match() {
	super(MATCH);
    }

    public Match(CasesExpr a, Expr T, boolean consume_scrut) {
	super(MATCH, a);
	this.T = T;
	this.consume_scrut = consume_scrut;
    }

    public Match(Expr t, Var x1, Var x2, Expr T, Case[] C, boolean consume_scrut) {
	super(MATCH, t, x1, x2, C);
	this.T = T;
	this.consume_scrut = consume_scrut;
    }

    public void do_print(java.io.PrintStream w, 
			 Context ctxt) {
	w.print("match ");
	if (!consume_scrut)
	    w.print("! ");
	do_print1(w,ctxt);
	if (T != null) {
	    w.print(" return ");
	    T.print(w,ctxt);
	}
	do_print2(w,ctxt);
    }

    public int hashCode_h(Context ctxt) {
	int h = t.hashCode_h(ctxt);
	for (int i = 0, iend = C.length; i < iend; i++) 
	    h += C[i].hashCode_h(ctxt);
	return h;
    }

    public int numOccInCases(Expr e) {
	return super.numOcc(e);
    }

    public int numOcc(Expr e) {
	int n = numOccInCases(e);
	if (T != null)
	    n += T.numOcc(e);
	return n;
    }

    public Expr subst(Expr e, Expr x) {
	Expr nT = (T == null ? null : T.subst(e,x));
	CasesExpr nC = (CasesExpr)super.subst(e,x);
	if (nT != T || nC != this)
	    return new Match(nC, nT, consume_scrut);
	return this;
    }
    
    public Expr do_rewrite(Context ctxt, Expr e, Expr x, Stack boundVars) {
	Expr nT = T;
	CasesExpr nC = (CasesExpr)super.do_rewrite(ctxt,e,x,boundVars);
	if (nT != T || nC != this)
	    return new Match(nC, nT, consume_scrut);
	return this;
    }

    // if e matches one of our cases, instantiate that case with e.
    // otherwise, return null.
    protected Expr instantiate(Context ctxt, Expr e) {
	e = e.defExpandTop(ctxt);

	Expr h = e;
	if (h.construct == TERM_APP) {
	    TermApp a = (TermApp)h;
	    h = a.getHead(ctxt,true);
	}

	if (h.construct != CONST){ 
	    return null;
	}
	
	Integer ii = ctxt.getWhichTermCtor((Const)h);
	
	if (ii == null)
	    return null;
	int i = ii.intValue();
	if (i >= C.length)
	    return null;

	return C[i].instantiate(ctxt, e);
    }


    public Expr dropAnnos(Context ctxt) {
	Expr r = super.dropAnnos(ctxt);
	if (r != this)
	    return new Match((CasesExpr)r,T,consume_scrut);
	return this;
    }

    // we assume proofs have been dropped already
    public Expr evalStep(Context ctxt) {
	Expr e = t.evalStep(ctxt);
	if (e != t)
	    return new Match(e,x1,x2,T,C,consume_scrut);
	if (t.construct == ABORT)
	    //return ctxt.abort;
		return t;
	
	Expr ret = instantiate(ctxt, e);
	if (ret == null) 
	    return this;
	return ret;
    }

    public boolean subtermDefEqNoAnno(Context ctxt, Expr e) {
	return (t.subtermDefEqNoAnno(ctxt, e) || super.subtermDefEqNoAnno(ctxt, e));
    }
    
    public Expr classify(Context ctxt, int approx, boolean spec) {
	Expr T1 = super.classify(ctxt,approx,spec);
	if (T != null) {
	    Expr cT = T.classify(ctxt,approx,spec);
	    if (cT.construct != TYPE)
		handleError(ctxt,
			    "The return type of a match-term is not a type.\n"
			    +"1. the return type:"+T.toString(ctxt)+"\n"
			    +"2. its classifier:"+cT.toString(ctxt));
	    if (!T1.defEq(ctxt,T,approx,spec))
		handleError(ctxt,"The stated return type of a match-term"
			    +" is not def. eq. to\nthe type computed"
			    +" for the cases.\n"
			    +"1. stated type: "+T.toString(ctxt)+"\n"
			    +"2. computed: "+T1.toString(ctxt));
	}
	else
	    T = T1;
	return T;
    }

    public java.util.Set getDependences() {
        java.util.Set s = super.getDependences();
        if (T != null)
            s.addAll(T.getDependences());
        return s;
    }


    public void checkSpec(Context ctxt, boolean in_type, Position p){
	t.checkSpec(ctxt, in_type, pos);
	for (int i = 0; i < C.length; i++){
	    C[i].checkSpec(ctxt, in_type, pos);
	}
    }
    
    //Override from Expr
    public UnjoinDeduction Unjoin(
			Expr target, 
			UnjoinContext uctxt,
			Context baseCtxt,
			boolean eq
	)
    {
    	UnjoinDeduction ret = UnjoinDeduction.contradiction;
    	
    	Expr t_ = uctxt.lemmaSet.rewrite(t); 
    		
    	//baseCtxt.lemmaSet.instantiate(t);
    	//while (t_.construct != TERM_APP && t_ != t_.evalStep(baseCtxt))
    	//	t_ = t_.evalStep(baseCtxt);
    	    	
    	//Set ret to the disjunction of the deductions that can be made from
    	//each branch.
    	for(int i = 0; i < C.length; ++i)
    	{
        	UnjoinDeduction branch;
        	
    		Case c = C[i];
    		
    		//TODO: do we really have to do this to detect term constructors?
    		boolean isConstructorTerm = t_.construct == TERM_APP;
    		if (isConstructorTerm)
    			isConstructorTerm &= ((TermApp)t_).head.construct == Expr.CONST;
    		
    		if (isConstructorTerm)
    			isConstructorTerm &= baseCtxt.isTermCtor( (Const)((TermApp)t_).head ); 
    	
    		// Prepend immediate deductions onto case body deductions -----
	    	if (c.x.length == 0) {
	    	
	    		if (!UnjoinBase.plausible(t_, c.c, uctxt, baseCtxt,true))
	    			continue;
	    		
    			Expr matchEq = (new Atom(true, t_, c.c)).dropAnnos(baseCtxt);
    			Var matchEqVar = new Var("p" + uctxt.proofCounter);
	    		
	    		if (t_.construct != CONST)
	    		{
	    			uctxt.proofCounter++;
	    			uctxt.lemmaSet.addLemma(matchEq);
	    		}
	    		
	        	// Make deductions from case body -----
	    		branch = c.body.Unjoin(
	    			target,
	    			uctxt,
	        		baseCtxt,
	        		eq
	        	);
	    		
	    		if (t_.construct != CONST) {
	    			uctxt.proofCounter--;
	    			uctxt.lemmaSet.removeLemma(matchEq);

	    			branch = new UnjoinIntro(matchEqVar, matchEq, branch);
	    		}
	    	} 
	    	else {

	    		if (!UnjoinBase.plausible(t_, new TermApp(c.c,c.x), uctxt, baseCtxt,true))
	    			continue;
	    		
	    		Expr body = c.body;
	    		
	    		// Create argument variables -----
	        	if (isConstructorTerm) {
	        		TermApp ta = (TermApp)t_;
	        		
	    			for (int j = 0; j < ta.X.length; ++j)
	    				body = body.subst(ta.X[j], c.x[j]);
	    			
		    		branch = body.Unjoin(
	        			target,
	        			uctxt,
	        			baseCtxt,
	        			eq
		        	);
	        	}
	        	else {
		    		FunType consType = (FunType)c.c.classify(baseCtxt);//.defExpandTop(baseCtxt);
		    		Expr scrutType = t_.classify(baseCtxt);
		    		
		    		assert(consType.vars.length == c.x.length);
		    		
		    		Expr[] clones = new Expr[consType.vars.length];
		    		boolean[] isConcrete = new boolean[consType.vars.length];
		    		Expr[] types = new Expr[consType.vars.length];
		    		int last = consType.vars.length-1;
		    		
		    		//index into non-specificational args
		    		int uInd = 0;
		    		
		        	HashMap varMap = new HashMap();
		    		UnjoinBase.InferVars(varMap, consType.body, scrutType);
		    		
		        	for(int j = 0; j < clones.length; ++j)
		        	{		        		
		        		if (varMap.containsKey(consType.vars[0]))
		        		{
		        			clones[j] = (Expr)varMap.get(consType.vars[0]);
		        			types[j] = clones[j].classify(baseCtxt);
		        			isConcrete[j] = true;
		        		}
		        		else
		        		{
			        		String name;
			        		if (t_.construct == VAR)
			        			name = ((Var)t_).name + j;
			        		else
			        			name = "c" + j;
			        		
		        			clones[j] = new Var(name);
		        			types[j] = consType.types[0];
		        			isConcrete[j] = false;
		        		}
		        		
		        		baseCtxt.setClassifier((Var)clones[j], types[j]);
		        		
		        		/*
		        		int spec = (consType.owned[0].status & Ownership.SPEC);
		        		
		        		if (!(clones[j].isTypeOrKind(baseCtxt) || 
		        			  clones[j].isProof(baseCtxt) ||
		        			  spec != 0) ) {
		        			
		        			nonSpecificationalClones[uInd] = clones[j];
		        			body = body.subst(clones[j], c.x[uInd]);
		        			uInd++;
		        		}
		        		*/

		        		// Instantiating the last argument would result in the
		        		// return type, which may not be a function type.
		        		// we're doing something similar in lemma set, 
		        		// should we factor this out?
		        		if (j != last)
		        			consType = (FunType)consType.instantiate(clones[j]);	        		
		        	}
		        	
		        	Expr consTypeResult = consType.instantiate(clones[clones.length-1]);

		        	for (int j = clones.length-1; j >= 0; --j)
		        		body = body.subst(clones[j], c.x[j]);
		        	
		        	Expr matchEq = new Atom(
		        		true, 
		        		t_, 
		        		new TermApp(c.c,clones)
		        	).dropAnnos(baseCtxt);
		        	
		        	Var matchEqVar = new Var("p" + uctxt.proofCounter);
		        	baseCtxt.setClassifier(matchEqVar, matchEq);
		        	

		        	uctxt.proofCounter++;
		        	uctxt.lemmaSet.addLemma(matchEq);
		        	
		        	// Make deductions from case body -----
		    		branch = body.Unjoin( 
	    				target, 
	    				uctxt, 
	    				baseCtxt, 
	    				eq
		    		);
		    		
		    		uctxt.proofCounter--;
		    		uctxt.lemmaSet.removeLemma(matchEq);
		        	
		    		//prepend immediate deductions to case body deductions
		        	branch = new UnjoinIntro(matchEqVar, matchEq.dropAnnos(baseCtxt), branch);
		    		
		        	for (int j = clones.length-1; j >= 0; --j)
		        	{
		        		if (!isConcrete[j])	
		        			branch = new UnjoinIntro((Var)clones[j], types[j], branch);
		        	}
	        	}
	    	}
	    	
        	//Or the current return value with the deduction for the
        	//current branch (if ret is null, we set it to the current branch)
        	ret = new UnjoinOr(ret, branch);
    	}
    	
    	return ret;
    }
    
    public guru.carraway.Expr toCarraway(Context ctxt) {
	guru.carraway.Match m = new guru.carraway.Match();
	m.pos = pos;
	m.consume_scrut = consume_scrut;
	m.t = t.toCarraway(ctxt);
	int iend = C.length;
	ArrayList a = new ArrayList();
	for (int i = 0; i < iend; i++)
	    if (!C[i].impossible)
		a.add((guru.carraway.Case)C[i].toCarraway(ctxt));
	
	m.C = guru.carraway.Parser.toCaseArray(a);
	m.consume_scrut = consume_scrut;
	return m;
    }
}
