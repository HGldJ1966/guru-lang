package guru;

import java.io.PrintStream;
import java.util.List;
import java.util.Stack;
import java.util.Vector;

public abstract class UnjoinBase extends Expr {

	// An expression which proves the scrutinee atom.
	public final Expr scrutineeProof;
	
	public UnjoinBase(int construct, Expr scrutineeProof)
	{
		super(construct);
		
		assert(scrutineeProof != null);
		assert(construct == UNJOIN || construct == UNJOIN_CONTRA);
		
		this.scrutineeProof = scrutineeProof;
	}
	
	public static boolean placeHolder(Expr e, Context ctxt)
	{
		if (e.construct == VAR)
			return true;
		
		if (e.construct == CONST && e.evalStep(ctxt) != e)
			return true;
		
		return false;
	}
	
	class VarValue
	{
		public final Var var;
		public final Expr classifier;
	
		public VarValue(Var var, Expr classifier)
		{
			this.var = var;
			this.classifier = classifier;
		}
	}
	
	public static boolean plausible(
		Expr term,
		Expr target,
		UnjoinContext uCtxt,
		Context baseCtxt,
		boolean eq
	)
	{		
		assert(eq == true);
		
		target = uCtxt.lemmaSet.simplify(target);

		if (target.construct == Expr.VAR)
			return true;
		
		switch (term.construct)
		{
		case Expr.TERM_APP:
			TermApp taTerm = (TermApp)term;
			
			if (taTerm.head.construct == CONST && baseCtxt.isCtor((Const)taTerm.head))
			{
				if (target.construct != TERM_APP)
					return false;
				
				TermApp taTarget = (TermApp)target;
				
				if (taTarget.head != taTerm.head)
					return false;
				

				boolean ret = true;
				for (int i = 0; i < taTerm.X.length; ++i)
				{
					ret = ret && plausible(
						taTerm.X[i],
						taTarget.X[i],
						uCtxt,
						baseCtxt,
						eq
					);
				}
				
				return ret;
			}
			else
			{	
	    		if (taTerm.head.eval(baseCtxt).construct != Expr.FUN_TERM)
	    			return true; // maybe it could be a variable
	    		
	    		FunTerm inst = (FunTerm)taTerm.head.eval(baseCtxt);
	   
	    		Var oldRec = uCtxt.recVar;
	    		uCtxt.recVar = inst.r;
	    		
	    		// Apply all arguments except last.
	    		for (int i = 0; i < taTerm.X.length-1; ++i)
	    			inst = (FunTerm)inst.substituteForParam(taTerm.X[i]);   
	    		
	    		// Apply last argument.
	    		// Instantiating a function with one argument may result in an
	    		// arbitrary term, so we need to use an Expr rather than
	    		// a FunTerm to hold the result.
				Expr fullInst = inst.substituteForParam(taTerm.X[taTerm.X.length-1]);
				
	    		boolean ret = plausible(
	    			fullInst,
	    			target,
	    			uCtxt,
	    			baseCtxt,
	    			eq
	    		);		
	    		
	    		uCtxt.recVar = oldRec;
	    		
	    		return ret;
			}
		case Expr.FUN_TERM:
			return target.construct == FUN_TERM;
		case Expr.VAR:
			return true;
		case Expr.CONST:
			if (term.evalStep(baseCtxt) != term) {
				return plausible(
					term.evalStep(baseCtxt),
					target,
					uCtxt,
					baseCtxt,
					eq
				);
			}
			
			return target == term;
		case Expr.MATCH:
			Match m = (Match)term;
	    	boolean ret = false;
	    	Expr t_ = uCtxt.lemmaSet.simplify(m.t);
	    	boolean branchPlausible;
	    	
	    	Case[] C = m.C;
	    	
	    	for(int i = 0; i < C.length; ++i)
	    	{
	    		Case c = C[i];
	    		
	    		// We need to factor this out
	    		boolean isScrutConstructor = t_.construct == TERM_APP;
	    		if (isScrutConstructor)
	    			isScrutConstructor &= ((TermApp)t_).head.construct == Expr.CONST;
	    		
	    		if (isScrutConstructor)
	    			isScrutConstructor &= baseCtxt.isTermCtor( (Const)((TermApp)t_).head ); 
	    		
	    		// If the case is for a constructor without any arguments,
	    		// we have this simple case involving no substitutions.
		    	if (c.x.length == 0)
		    	{
    				boolean scrutPlausible = plausible(
    					t_,
	    				c.c,
		    			uCtxt,
		    			baseCtxt,
		    			true
		    		);
    				
    				if (!scrutPlausible)
    					continue;
        				
		        	Atom matchEq = new Atom(true, t_, c.c);
		        	Var matchEqVar = new Var("p");
		        	
		    		if (t_.construct != Expr.CONST)	
		    			uCtxt.lemmaSet.addLemma(matchEq);
		    		
		        	// Make deductions from case body -----
		    		branchPlausible = plausible(
		    			c.body,
		    			target,
		    			uCtxt,
		    			baseCtxt,
		    			eq
		    		);
		    		
		    		if (t_.construct != CONST)
		    			uCtxt.lemmaSet.removeLemma(matchEq);
		    	} 
		    	// if the case is for a constructor with arguments,
		    	// things are a bit more complicated.
		    	else
		    	{
    				boolean scrutPlausible = plausible(
    					t_,
	    				new TermApp(c.c,c.x),
		    			uCtxt,
		    			baseCtxt,
		    			true
		    		);		
    				
    				if (!scrutPlausible)
    					continue;
        				
		        	if (isScrutConstructor)
		        	{
		        		TermApp ta = (TermApp)t_;
		        		Expr substitutedBody = c.body;
		        		
		    			for (int j = 0; j < ta.X.length; ++j)
		    				substitutedBody = substitutedBody.subst(ta.X[j], c.x[j]);
		    			
			    		branchPlausible = plausible(
			    			substitutedBody,
			        		target,
			        		uCtxt,
			        		baseCtxt,
			        		eq
			        	);
		        	}
		        	else
		        	{
		        		//
		        		Expr substitutedBody = c.body;;
		        		
			    		FunType consType = (FunType)c.c.classify(baseCtxt).defExpandTop(baseCtxt);
			    		Var[] clones = new Var[consType.vars.length];
			    		Var[] nonSpecificationalClones = new Var[c.x.length];
			    		Expr[] types = new Expr[consType.vars.length];
			    		
			    		int last = consType.vars.length-1;
			    		
			    		//index into non-specificational args
			    		int uInd = 0;
			    		
			        	for(int j = 0; j < clones.length; ++j)
			        	{
			        		clones[j] = new Var("z");
			        		types[j] = consType.types[0];
			        		baseCtxt.setClassifier(clones[j], types[j]);
			        		
			        		int spec = (consType.owned[0].status & Ownership.SPEC);
			        		
			        		if (!(clones[j].isTypeOrKind(baseCtxt) || 
			        			  clones[j].isProof(baseCtxt) ||
			        			  spec != 0) ) {
			        			
			        			nonSpecificationalClones[uInd] = clones[j];
			        			substitutedBody = substitutedBody.subst(clones[j], c.x[uInd]);
			        			uInd++;
			        		}
			        		
			        		// Instantiating the last argument would result in the
			        		// return type, which may not be a function type.
			        		if (j != last)
			        			consType = (FunType)consType.instantiate(clones[j]);	        		
			        	}
			        	
			        	Atom matchEq = new Atom(
			        		true, 
			        		t_, 
			        		new TermApp(c.c,nonSpecificationalClones)
			        	);
			        			    
			        	uCtxt.lemmaSet.addLemma(matchEq);
			        	
			        	// Make deductions from case body -----
			    		branchPlausible = plausible(
			    			substitutedBody,
		    				target, 
		    				uCtxt, 
		    				baseCtxt, 
		    				eq
			    		);
			    		
			    		uCtxt.lemmaSet.removeLemma(matchEq);
		        	}
		    	}
		    	
	        	//Or the current return value with the deduction for the
	        	//current branch (if ret is null, we set it to the current branch)
	        	ret = ret || branchPlausible;
	    	}
	    	
	    	return ret;
		case Expr.BANG:
			return target.construct == Expr.BANG;
		case Expr.DO:
			Do d = (Do)term;
			return plausible(
				d.t,
				target,
				uCtxt,
				baseCtxt,
				eq
			);
		case Expr.VOIDI:
			return target.construct == VOIDI;
		case Expr.LET:
			return plausible(
				term.evalStep(baseCtxt),
				target,
				uCtxt,
				baseCtxt,
				eq
			);
		default:
			assert(false);
			return false;
		}	
	}
	
	//Non-unfolding evaluation step
	public Expr nustep(Expr e, Context ctxt)
	{
		switch (e.construct)
		{
		case Expr.TERM_APP:
			TermApp ta = (TermApp)e;
			
			Expr h = ta.head;
			if (h.construct != CONST) {
			  h = nustep(h, ctxt);
			
			  if (h != ta.head) {
				Expr ret = new TermApp(h, ta.X);
				ret.pos = pos;
				return ret;
			  }
			}
			
			if (h.construct == ABORT)
			  //return ctxt.abort;
			  return h;
			
			int iend = ta.X.length;
			Expr[] X2 = new Expr[iend];
			for (int i = 0; i < iend; i++) {
			    X2[i] = nustep(ta.X[i], ctxt);
			    if (X2[i] != ta.X[i]) {
				  for (int j = i+1; j < iend; j++)
				    X2[j] = ta.X[j];
				  Expr ret = new TermApp(h, X2);
				  ret.pos = pos;
				  return ret;
			    }
			    else if (ta.X[i].construct == ABORT) {
				    //return ctxt.abort;
					return ta.X[i];
			    }
			}
			
			// none of the args evaluated to something different
			if (h.construct != FUN_TERM)
				return e;

		    FunTerm f = (FunTerm)h;
		    
		    // We do not instantiate recursive functions to avoid
		    // explosion.
		    if (f.r != null)
		    	return e;
		    
		    iend = X2.length;

		    Expr hh = f.substituteForParam(X2[0]);
		    if (iend == 1)
		    	return hh;
		    
		    iend--;
		    Expr[] X3 = new Expr[iend];
		    for (int i = 0; i < iend; i++)
		    	X3[i] = X2[i+1];
		    Expr ret = new TermApp(hh, X3);
		    ret.pos = pos;
		    return ret;
		case Expr.FUN_TERM:
			return e;
		case Expr.VAR:
			return e.defExpandTop(ctxt);
		case Expr.CONST:
			return e;
		case Expr.MATCH:
			return e;
		case Expr.BANG:
			return e;
		case Expr.DO:
			Do d = (Do)e;
			return d.t;
		case Expr.VOIDI:
			return e;
		case Expr.LET:
			Let l = (Let)e;
			Expr et1 = nustep(l.t1, ctxt);
			if (et1 != l.t1)
			    return new Let(l.x1, l.x1_stat, et1, l.x2, l.t2);
			if (l.t1.construct == ABORT)
				return l.t1;
			return l.t2.subst(l.t1, l.x1);
		default:
			assert(false);
			return null;
		}
	}
	
	public Expr nueval(Expr e, Context ctxt)
	{
    	Expr e2 = e;
    	
		while (e2 != nustep(e2,ctxt))
		{
			//System.out.println(e2.toString(ctxt));
			e2 = nustep(e2,ctxt);
		}
		
		return e2;
	}
	
	class LiftedMatch
	{
		public final Expr scrut;
		public final Var hole;
		public final Case[] cases;
		public final Expr context;
		
		public LiftedMatch(Expr scrut, Var hole, Case[] cases, Expr context) {
			assert(matchFree(scrut));
			
			for (int i = 0; i < cases.length; ++i) {
				assert(cases[i] != null);
				assert(matchFree(cases[i].body));
			}
			
			this.scrut = scrut;
			this.hole = hole;
			this.cases = cases;
			this.context = context;
		}
	}
	
	public LiftedMatch liftSingleMatch(Expr e)
	{
		switch (e.construct)
		{
		case Expr.TERM_APP:
			TermApp ta = (TermApp)e;

			LiftedMatch lift = liftSingleMatch(ta.head);
			if (lift != null)
			{
				return new LiftedMatch(
					lift.scrut,
					lift.hole,
					lift.cases,
					new TermApp(lift.context, ta.X)
				);
			}
			
			for (int i = 0; i < ta.X.length; ++i) {
				lift = liftSingleMatch(ta.X[i]);
				if (lift != null) {
					Expr[] X2 = new Expr[ta.X.length];
					
					for (int j = 0; j < ta.X.length; ++j)
					{
						if (i == j)
							X2[j] = lift.context;
						else
							X2[j] = ta.X[j];
					}
					
					return new LiftedMatch(
						lift.scrut,
						lift.hole,
						lift.cases,
						new TermApp(ta.head, X2)	
					);
				}
			}

			return null;
		case Expr.FUN_TERM:
			return null;
		case Expr.VAR:
			return null;
		case Expr.CONST:
			return null;
		case Expr.BANG:
			return null;
		case Expr.VOIDI:
			return null;
		case Expr.MATCH:
			Match m = (Match)e;
			
			lift = liftSingleMatch(m.t);
			
			if (lift != null) {
				return new LiftedMatch(
				  lift.scrut,
				  lift.hole,
				  lift.cases,
				  new Match(
					lift.context,
					m.x1,
					m.x2,
					m.T,
					m.C,
					m.consume_scrut
				  )
				);
			}
			
			for (int i = 0; i < m.C.length; ++i) {
				lift = liftSingleMatch(m.C[i].body);
				
				if (lift != null) {
					Case[] cases = (Case[])m.C.clone();
					cases[i].body = lift.context;
					
					return new LiftedMatch(
					  lift.scrut,
					  lift.hole,
					  lift.cases,
					  new Match(
						m.t,
						m.x1,
						m.x2,
						m.T,
						cases,
						m.consume_scrut
					  )
					);
				}
				
			}
			
			Var hole = new Var("hole");
			return new LiftedMatch(
				m.t,
				hole,
				m.C,
				hole
			);
		case Expr.LET:
			Let l = (Let)e;
			lift = liftSingleMatch(l.t1);
			
			if (lift != null) {
				return new LiftedMatch(
					lift.scrut,
					lift.hole,
					lift.cases,
					new Let(
						l.x1,
						l.x1_stat,
						lift.context,
						l.x2,
						l.t2
					)
				);
			}
			
			lift = liftSingleMatch(l.t2);
			
			if (lift != null) {
				return new LiftedMatch(
					lift.scrut,
					lift.hole,
					lift.cases,
					new Let(
						l.x1,
						l.x1_stat,
						l.t1,
						l.x2,
						lift.context
					)
				);
			}
			
			return null;
		case Expr.ABORT:
			return null;
		default:
			assert(false);
			return null;
		}		
	}
	
	public boolean matchFree(Expr e)
	{	
		switch(e.construct)
		{
		case Expr.TERM_APP:
			TermApp ta = (TermApp)e;
			
			boolean ret = true;
			
			ret |= matchFree(ta.head);
			
			for (int i = 0; i < ta.X.length; ++i)
				ret |= matchFree(ta.X[i]);
			
			return ret;
		case Expr.FUN_TERM:
			
			// We could lift matches from function bodies as well,
			// but this wouldn't really reflect guru's
			// call-by-value semantics.
			return true;
		case Expr.VAR:
			return true;
		case Expr.CONST:
			return true;
		case Expr.MATCH:
			return false;
		case Expr.LET:
			Let let = (Let)e;
			return matchFree(let.t1) && matchFree(let.t2);
		case Expr.ABORT:
			return true;
		default:
			assert(false);
			return false;
		}		
	}
	
	// Returns some variable used as a match inside expression e,
	// or null if e contains no matches.
//	public Var UnAnnotatedTermTemplate(Expr e)
//	{
//		switch(e.construct)
//		{
//		case Expr.TERM_APP:
//			TermApp ta = (TermApp)e;
//			break;
//		case Expr.FUN_TERM:
//			FunTerm ft = (FunTerm)e;
//			break;
//		case Expr.VAR:
//			return null;
//  	case Expr.CONST:
//		case Expr.MATCH:
//			Match m = (Match)e;
//			return m.t;
//			break;
//		case Expr.LET:
//			break;
//		default:
//			return null;
//		}
//	}
	
	public Expr liftMatches(Expr e)
	{
		Vector lifts = new Vector();
		
		LiftedMatch currentLift = liftSingleMatch(e);
		while (currentLift != null)
		{
			lifts.add(currentLift);
			currentLift = liftSingleMatch(currentLift.context);
		}
		
		if (lifts.size() == 0)
			return e;
		else
			return liftsToExp(lifts,0);
	}
	
	public Expr liftsToExp(Vector lifts, int liftInd)
	{
		LiftedMatch lift = (LiftedMatch)lifts.get(liftInd);
		
		Case[] cases = new Case[lift.cases.length];
		
		for (int i = 0; i < lift.cases.length; ++i)
		{
			Case liftCase = lift.cases[i];
		
			Expr body;
			
			
			if (liftInd == lifts.size()-1) {
				body = lift.context.subst(liftCase.body, lift.hole);
			}
			else {
				body = liftsToExp(lifts, liftInd+1).subst(liftCase.body, lift.hole);
			}
			
			cases[i] = new Case(
				liftCase.c,
				liftCase.x,
				body,
				liftCase.impossible
			);
		}
		
		Var junk = new Var("junk");
		
		return new Match(
			lift.scrut,
			junk,
			junk,
			junk,
			cases,
			false
		);
	}
	
	// An experimental version of instantiate using nueval
	public Expr instantiate2(Context ctxt, Expr lhs)
	{
		if (lhs.construct != TERM_APP)
			return lhs;
		
		Expr lhs2 = lhs;
		
		while (true) {
			//System.out.println("a.");
			//System.out.println(lhs2.toString(ctxt));
			
	    	lhs2 = nueval(lhs2, ctxt);
	    	
	    	//System.out.println("b.");
	    	//System.out.println(lhs2.toString(ctxt));
	    	
	    	lhs2 = liftMatches(lhs2);
	    	
	    	//System.out.println("c.");
	    	//System.out.println(lhs2.toString(ctxt));
	    	
	    	if (lhs2.construct == TERM_APP)
	    	{
	    		TermApp ta = (TermApp)lhs2;
	    		
	    		if (ta.head.construct != CONST)
	    			return lhs2;
	    		
		    	// The pre-instantiated value of the head.
	    		Const c = (Const)ta.head;
	    		
	    		// A variable used to instantiate the head
	    		Expr ev = c.eval(ctxt);
	    		
	    		if (ev.construct != FUN_TERM)
	    		{
		    		handleError(ctxt,
							"The left hand side of an unjoin scrutinee " +
							"evaluates to a term app whose head is not a function.\n" +
							"1. lhs:" + lhs.toString(ctxt) + "\n" +
							"2. evaluated lhs: " + ev.toString(ctxt) + "\n"
			    		);
	    		}
	    		
	    		FunTerm inst = (FunTerm)ev;
	    		Var r = inst.r;
	    		
	    		// Apply all arguments except last.
	    		for (int i = 0; i < ta.X.length-1; ++i)
	    			inst = (FunTerm)inst.substituteForParam(ta.X[i]);   
	    		
	    		// Apply last argument.
	    		// Instantiating a function with one argument may result in an
	    		// arbitrary term, so we need to use an Expr rather than
	    		// a FunTerm to hold the result.
				lhs2 = inst.substituteForParam(ta.X[ta.X.length-1]);
	    	
	    		// If we are unjoining an application of a recursive, top-level
	    		// function, we substitute the function's constant for occurrences
	    		// of the function's recursive variable in the body. 
	    		// 
	    		// This way, any facts deduced about recursive calls will mention
	    		// the constant which, unlike the recursive variable, is accessible
	    		// via the current context.
				if (r != null)		
					lhs2= (Expr)lhs2.subst(c, r);
	    	}
	    	else
	    	{
	    		return lhs2;
	    	}
		}		
	}
	
	// TODO: we need a base class for Unjoin and UnjoinContra which implements
	// this.
	//
	// Converts the left hand side of the scrutinee atom into an equivalent term 
	// from which unjoin can derive useful information. This equivalent term
	// will either be a match, a let, or an abbrev. 
	//
	// The conversion process is as follows:
	//
	// - While t is a term app:
	// -   if the head is a const defined to be some recursive function,
	//       establish a correspondence between the constant and the function's
	//       recursive variable in the unjoin context
	// -   evaluate the head if possible
	// -   if the resulting head is a function term, instantiate the function
	//     in a lazy manner, substituting each actual argument for its corresponding
	//     formal argument without evaluating the actuals.
	//     otherwise, generate an error and halt.
	// -   assign t to the instantiated function.
	// - return t
	//
	// TODO: We might have to prove an equivalence between the strict function
	// call semantics used by guru and the lazy approach taken by unjoin. Since
	// guru is functional, this should work.
	private Expr instantiate(Context ctxt, Expr lhs)
	{	
		if (lhs.construct != TERM_APP)
			return lhs;
		
		TermApp ta = (TermApp)lhs;

		while (true) {
	    	Expr h = ta.head.evalStep(ctxt);
	    	//The constant or variable initially used for the head.
	    	Expr pre = ta.head;
		
			while (h != h.evalStep(ctxt));
			{
				if (h.construct == MATCH)
					handleError(ctxt, 
							"Unjoin cannot handle terms containing term apps" +
							" whose heads evaluate to matches.");
				
				h = h.evalStep(ctxt);
				
			}
	    	
	    	//TODO: we really need to loop here, evaluating the head
	    	//one step at a time until normalization, generating an 
	    	//error message if any intermediate form is not a constant.
	    	//We only need to establish a correspondence between the 
	    	//initial const and the recursive variable of the normal form.
	    	
			// If the head does not normalize to a function, we cannot
	    	// instantiate it, so we cannot unjoin this term app. 
	    	if (h.construct != FUN_TERM) {
	    		handleError(ctxt,
					"The left hand side of an unjoin scrutinee " +
					"evaluates to a term app whose head is not a function.\n" +
					"1. lhs:" + lhs.toString(ctxt) + "\n" +
					"2. evaluated lhs: " + h.toString(ctxt) + "\n"
	    		);
	    	}
	    	
	    	// The pre-instantiated value of the head.
    		FunTerm f = (FunTerm)h;
    		// A variable used to instantiate the head
    		FunTerm inst = f;
    		
    		// Apply all arguments except last.
    		for (int i = 0; i < ta.X.length-1; ++i)
    			inst = (FunTerm)inst.substituteForParam(ta.X[i]);   
    		
    		// Apply last argument.
    		// Instantiating a function with one argument may result in an
    		// arbitrary term, so we need to use an Expr rather than
    		// a FunTerm to hold the result.
			Expr fullInstantiation = inst.substituteForParam(ta.X[ta.X.length-1]);
    	
    		// If we are unjoining an application of a recursive, top-level
    		// function, we substitute the function's constant for occurrences
    		// of the function's recursive variable in the body. 
    		// 
    		// This way, any facts deduced about recursive calls will mention
    		// the constant which, unlike the recursive variable, is accessible
    		// via the current context.
			if (f.r != null && pre.construct == CONST)		
				fullInstantiation = (Expr)fullInstantiation.subst((Const)pre, f.r);
			
			//continue past lets and abbrevs
			fullInstantiation = fullInstantiation.eval(ctxt);
			
			if (fullInstantiation.construct != TERM_APP)
				return fullInstantiation;
			
			ta = (TermApp)fullInstantiation;
		}
	}

	private void DumpUnjoinPaths(List unjoinPaths, Context ctxt)
	{
		for(int i = 0; i < unjoinPaths.size(); ++i) {
			String pathString = "";
			Stack path = (Stack)unjoinPaths.get(i);
			for(int j = 0; j < path.size(); ++j) {
				UnjoinIntro u = (UnjoinIntro)path.get(j);				
				pathString += "(" + u.introVar.toString(ctxt) + " : " + 
					u.introVarType.toString(ctxt) + ")";
			}
			
			System.out.println(pathString);
		}
	}

	// Expr override
	public Expr dropAnnos(Context ctxt) {
		return new Bang();
	}

}
