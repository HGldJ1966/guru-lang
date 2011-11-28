package guru;

import java.io.PrintStream;
import java.util.List;
import java.util.Stack;
import java.util.Vector;
import java.util.Map;
import java.util.Map.Entry;
import java.util.HashMap;

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
		public final Expr value;
	
		public VarValue(Var var, Expr value)
		{
			this.var = var;
			this.value = value;
		}
	}
	
	// Not sure how robust this is... might have to revisit it.
	static public void InferVars(HashMap varMap, Expr abstr, Expr concrete)
	{
		switch (abstr.construct)
		{
		case TYPE_APP:
			assert(concrete.construct == TYPE_APP);
			TypeApp taAbstr = (TypeApp)abstr;
			TypeApp taConcrete = (TypeApp)concrete;
			assert(taAbstr.X.length == taConcrete.X.length);
			
			for (int i = 0; i < taAbstr.X.length; ++i)
				InferVars(varMap, taAbstr.X[i], taConcrete.X[i]);
			
			break;
		case TERM_APP:
			assert(concrete.construct == TERM_APP);
			TermApp termAppAbstr = (TermApp)abstr;
			TermApp termAppConcrete = (TermApp)concrete;
			
			assert(termAppAbstr.X.length == termAppConcrete.X.length);
			assert(termAppAbstr.head == termAppConcrete.head);
			
			for (int i = 0; i < termAppAbstr.X.length; ++i)
				InferVars(varMap, termAppAbstr.X[i], termAppConcrete.X[i]);
			
			break;
		case VAR:
			if (abstr != concrete)
				varMap.put(abstr, concrete);
			break;
		case CONST:
			break;
		case FUN_TYPE:
			assert(concrete.construct == FUN_TYPE);
			FunType ftAbstr = (FunType)abstr;
			FunType ftConcrete = (FunType)concrete;
			
			assert(ftAbstr.vars.length == ftConcrete.vars.length);
			
			for(int i = 0; i < ftAbstr.vars.length; ++i)
			{
				InferVars(varMap, ftAbstr.vars[0], ftConcrete.vars[0]);
				
				if (i != (ftAbstr.vars.length-1))
				{
					//maybe I should instantiate these with null instead.
					//this is closely coupled with the case for Var.
					ftAbstr = (FunType)ftAbstr.instantiate(ftConcrete.vars[0]);
					ftConcrete = (FunType)ftConcrete.instantiate(ftConcrete.vars[0]);
				}
			}
			
			Expr instAbstr = ftAbstr.instantiate(ftConcrete.vars[0]);
			Expr instConcrete = ftConcrete.instantiate(ftConcrete.vars[0]);
			
			InferVars(varMap, instAbstr,instConcrete);
			
			break;
		default:
			// I think you are allowed to have any terms in type apps,
			// but I have only seen those listed above.
			assert(false);
		}
	}
	
	public Expr InferType(Expr t, Context ctxt)
	{
		switch (t.construct)
		{
		case Expr.TERM_APP:
			Expr annotatedApp = RebuildAnnotations((TermApp)t, ctxt);
			return annotatedApp.classify(ctxt);
		case Expr.VAR:
			return ctxt.getClassifier((Var)t);
		case Expr.CONST:
			return ctxt.getClassifier((Const)t);
		default:
			// A precondition for this function is that t is a term
			// containing only the above constructs.
			assert(false);
			return null;
		}
	}
	
	public static Expr RebuildAnnotations(
			Expr uTerm,
			Context ctxt
		)
	{
		HashMap varMap = new HashMap();
		Expr rebuilt = RebuildAnnotationsAux(varMap, uTerm, ctxt);
		rebuilt = substitute(varMap, rebuilt);
		return rebuilt;
	}
	
	public static Expr RebuildAnnotationsAux(HashMap varMap, Expr uTerm, Context ctxt)
	{
		if (uTerm.construct == TERM_APP) {
			TermApp ta = (TermApp)uTerm;
			
			FunType ty = (FunType)ta.head.classify(ctxt);
			
			return RebuildAnnotationsTargetedAux(varMap, uTerm, ty.body, ctxt);			
		}
		else if (uTerm.construct == CONST) {
			Const c = (Const)uTerm;
			
			if(!ctxt.isCtor(c))
				return c;
			
			Expr termTy = c.classify(ctxt); 
			if(termTy.construct != Expr.FUN_TYPE)
				return c;
			
			FunType ty = (FunType)termTy;
			return RebuildAnnotationsTargetedAux(varMap, uTerm, ty.body, ctxt);
		}
		else if (uTerm.construct == VAR) {
			return uTerm;
		}
		else {
			// A precondition to this function is that the term
			// consists solely of TermApps, Consts, and Vars
			assert(false);
			return null;
		}
	}
	
	public static Expr substitute(HashMap subs, Expr target)
	{
		if (target.construct == TERM_APP) {
			TermApp ta = (TermApp)target;
			
			Expr[] X = new Expr[ta.X.length];
			for (int i = 0; i < ta.X.length; ++i)
				X[i] = substitute(subs, ta.X[i]);
			
			return new TermApp(ta.head, X);
		}
		else if (target.construct == CONST) {
			return target;
		}
		else if (target.construct == VAR) {
			Expr sub = (Expr)subs.get(target);
			return (sub != null) ? sub : target;
		}
		else {
			// A precondition to this function is that the term
			// consists solely of TermApps, Consts, and Vars
			assert(false);
			return null;
		}			
	}
	
	public static Expr RebuildAnnotationsTargeted(
		Expr uTerm,
		Expr targetTy,
		Context ctxt
	)
	{
		HashMap varMap = new HashMap();
		Expr rebuilt = RebuildAnnotationsTargetedAux(varMap, uTerm, targetTy, ctxt);
		rebuilt = substitute(varMap, rebuilt);
		return rebuilt;
	}
	
	//
	//
	public static Expr RebuildAnnotationsTargetedAux(
		HashMap varMap, 
		Expr uTerm, 
		Expr targetTy,
		Context ctxt
	)
	{
		if (uTerm.construct == TERM_APP) {
			TermApp ta = (TermApp)uTerm;
			
			// TODO: One more case I really think this strategy is going to work...
			// keep at it!
			//
			FunType ftHead = (FunType)ta.head.classify(ctxt);
			
			HashMap subs = new HashMap();
			InferVars(subs, ftHead.body, targetTy);
			
			FunType ftHead2 = ftHead;
			
			Var[] vars2 = new Var[ftHead.vars.length];
			for (int i = 0; i < vars2.length; ++i)
			{
				Expr sub = (Expr)subs.get(ftHead2.vars[i]);
				
				//TODO: the var classifiers aren't going to match the types.
				//but does it matter? They should match (look at VarListExp.subst)
				if (sub != null)
					ftHead2 = (FunType)ftHead2.subst(sub, ftHead.vars[i]);
			}
			
			Expr[] X = new Expr[ftHead2.vars.length];
			int uInd = 0;
			for(int i = 0; i < ftHead2.vars.length; ++i)
			{
				boolean spec;
				spec = ftHead2.owned[i].status == Ownership.SPEC;
				
	    		if (!(ftHead2.vars[i].isTypeOrKind(ctxt) || 
	    			  ftHead2.vars[i].isProof(ctxt) ||
	        		  spec) ) {
	    		
	    			X[i] = RebuildAnnotationsTargetedAux(
	    				varMap, 
	    				ta.X[uInd], 
	    				ftHead2.types[i], 
	    				ctxt
	    			);
	    			
	    			uInd++;
	    		}
	    		else
	    		{
	    			X[i] = ftHead2.vars[i];
	    		}
			}
			
			return new TermApp(ta.head, X);		
		}
		else if (uTerm.construct == CONST) {
			Const c = (Const)uTerm;
			
			if(!ctxt.isCtor(c))
			{
				InferVars(varMap, targetTy, c.classify(ctxt));
				return c;
			}
			
			Expr headTy = c.classify(ctxt); 
			if(headTy.construct != Expr.FUN_TYPE)
			{
				InferVars(varMap, targetTy, c.classify(ctxt));
				return c;
			}
			
			FunType ft = (FunType)headTy;
			HashMap subs = new HashMap();
			InferVars(subs, ft.body, targetTy);
			
			Var[] vars = new Var[ft.vars.length];
			
			// Inherited specificational vars are used rather than those from
			// the constructor type so that we keep track of as few vars as possible.
			for (int i = 0; i < ft.vars.length; ++i)
			{
				vars[i] = (Var)subs.get(ft.vars[i]);
				assert(vars[i] != null);
			}
			
			return new TermApp(c, vars);
		}
		else if (uTerm.construct == VAR) {
			Expr varTy = uTerm.classify(ctxt);
			InferVars(varMap, varTy, targetTy);
			return uTerm;
		}
		else {
			// A precondition to this function is that the term
			// consists solely of TermApps, Consts, and Vars
			assert(false);
			return null;
		}		
	}
	
	/*
	public Expr RebuildAnnotations(HashMap varMap, Expr uTerm, Context ctxt)
	{
		if (uTerm.construct == FUN_TERM) {
			TermApp uApp = (TermApp)uTerm;
			FunType ft = (FunType)uApp.head.classify(ctxt);
			
			Expr[] X = uApp.X;
			int uInd = 0;
			
			Vector values = new Vector();
			
			for (int i = 0; i < ft.vars.length; ++i) {
				boolean spec = (ft.owned[i].status & (1<<Ownership.SPEC)) != 0;
				
	    		if (!(ft.vars[i].isTypeOrKind(ctxt) || 
	      			  ft.vars[i].isProof(ctxt) ||
	      			  spec) ) {
	      			
	    			
	    			assert(uApp.X[uInd].construct == TERM_APP ||
	    					uApp.X[uInd].construct == VAR ||
	    					uApp.X[uInd].construct == CONST);

	    			// Rebuilding to the best of our abilities at this point
	    			// may leave out items which are deduced from other
	    			// arguments, but it is done for the purpose of extracting all
	    			// of the useful data we need. A full rebuild happens later.
	      			Expr rebuiltArg;
	      			if (uApp.X[uInd].construct == TERM_APP)
	      				rebuiltArg = RebuildAnnotations(varMap, (TermApp)uApp.X[uInd], ctxt);
	      			else
	      				rebuiltArg = uApp.X[uInd];
	      			
	      			varMap.put(ft.vars[i], rebuiltArg);
	      			InferVars(varMap, ft.types[i], rebuiltArg.classify(ctxt));
	      			
	      			uInd++;
	      		}
			}
			
			Expr[] retArgs = new Expr[ft.vars.length];
			
			for(int i = 0; i < retArgs.length; ++i) {
				retArgs[i] = RebuildAnnotations(
					varMap,
					(Expr)varMap.get(ft.vars[i]),
					ctxt
				);
			}
			
			return new TermApp(uApp.head, retArgs);			
		}
		else if (uTerm.construct == CONST)
		{
			Expr termTy = uTerm.classify(ctxt); 
			if(termTy.construct != Expr.FUN_TYPE)
				return uTerm;
			
			UnjoinBase.InferVars(varMap, ((FunType)termTy).body, targetTy);
			
			FunType ftTermTy = (FunType)termTy;
			
			retArgs = new Expr[ftTermTy.vars.length];
			
			for(int i = 0; i < retArgs.length; ++i) {
				retArgs[i] = (Expr)varMap.get(ftTermTy.vars[i]);
				assert(retArgs[i] != null);
			}
			
			return new TermApp(uterm, retArgs);			
		}
		else if (uTerm.construct == VAR)
		{
			
		}
		else
		{
			assert(false);
			return null;
		}
	}
	
	public static Expr RebuildAnnotations(TermApp uApp, Expr targetTy, Context ctxt)
	{
		FunType ft = (FunType)uApp.head.classify(ctxt);
		
		Expr[] X = uApp.X;
		int uInd = 0;
		
		Vector values = new Vector();
		HashMap varMap = new HashMap();
		
		for (int i = 0; i < ft.vars.length; ++i) {
			boolean spec = (ft.owned[i].status & (1<<Ownership.SPEC)) != 0;
			
    		if (!(ft.vars[i].isTypeOrKind(ctxt) || 
      			  ft.vars[i].isProof(ctxt) ||
      			  spec) ) {
      			
    			
    			assert(uApp.X[uInd].construct == TERM_APP ||
    					uApp.X[uInd].construct == VAR ||
    					uApp.X[uInd].construct == CONST);

      			Expr rebuiltArg;
      			if (uApp.X[uInd].construct == TERM_APP)
      				rebuiltArg = RebuildAnnotations((TermApp)uApp.X[uInd], ctxt);
      			else
      				rebuiltArg = uApp.X[uInd];
      			
      			varMap.put(ft.vars[i], rebuiltArg);
      			InferVars(varMap, ft.types[i], rebuiltArg.classify(ctxt));
      			
      			uInd++;
      		}
		}
		
		Expr[] retArgs = new Expr[ft.vars.length];
		
		for(int i = 0; i < retArgs.length; ++i) {
			retArgs[i] = (Expr)varMap.get(ft.vars[i]);
		}
		
		return new TermApp(uApp.head, retArgs);
	}
	*/
	
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
	    		
	    		FunTerm inst = (FunTerm)taTerm.head.defExpandTop(baseCtxt,false,true);
	   
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
        				
		        	Expr matchEq = (new Atom(true, t_, c.c)).dropAnnos(baseCtxt);
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
		        		
		        		Expr scrutClassifier = t_.classify(baseCtxt);
			    		FunType consType = (FunType)c.c.classify(baseCtxt).defExpandTop(baseCtxt);
			    		
			    		HashMap varMap = new HashMap();
			    		//TODO: I can't remember why I did this. Is this necessary
			    		//for plausibility?
			    		InferVars(varMap, consType.body, scrutClassifier);
			    		
			    		for (int j = 0; j < consType.vars.length; ++j)
			    		{
			    			Expr sub = (Expr)varMap.get(consType.vars[j]);
			    			if (sub != null)
			    			{
			    				Var newVar = new Var(c.x[j].name);
			    				baseCtxt.setClassifier(newVar, sub);
			    				
			    				substitutedBody = substitutedBody.subst(newVar, c.x[j]);
			    			}
			    		}
			    		
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
			        		
			        		boolean spec = (consType.owned[0].status == Ownership.SPEC);
			        		
			        		if (!(clones[j].isTypeOrKind(baseCtxt) || 
			        			  clones[j].isProof(baseCtxt) ||
			        			  spec) ) {
			        			
			        			nonSpecificationalClones[uInd] = clones[j];
			        			substitutedBody = substitutedBody.subst(clones[j], c.x[uInd]);
			        			uInd++;
			        		}
			        		
			        		// Instantiating the last argument would result in the
			        		// return type, which may not be a function type.
			        		if (j != last)
			        			consType = (FunType)consType.instantiate(clones[j]);	        		
			        	}
			        
			        	Expr matchEq = new Atom(
			        		true, 
			        		t_, 
			        		new TermApp(c.c,clones)
			        	).dropAnnos(baseCtxt);
			        			    
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
		case Expr.ABBREV:
			Abbrev a = (Abbrev)e;
			lift = liftSingleMatch(a.U);
			
			if (lift != null) {
				return new LiftedMatch(
					lift.scrut,
					lift.hole,
					lift.cases,
					new Abbrev(
						a.flags,
						a.x,
						lift.context,
						a.G
					)
				);
			}
			
			lift = liftSingleMatch(a.U);
			
			if (lift != null) {
				return new LiftedMatch(
					lift.scrut,
					lift.hole,
					lift.cases,
					new Abbrev(
						a.flags,
						a.x,
						a.U,
						lift.context
					)
				);
			}
			
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
		case Expr.ABBREV:
			Abbrev a = (Abbrev)e;
			return matchFree(a.G) && matchFree(a.U); 
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
		
		//TODO: generate an error if lhs has anything other than
		//term apps, variables, and constants.
		
		Expr lhs2 = RebuildAnnotations((TermApp)lhs, ctxt);
		
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
	    		
	    		// Def expand the head without dropping annotations.
	    		Expr ev = c.defExpandTop(ctxt, false, true);
	    		
	    		if (ev.construct != FUN_TERM)
	    		{
		    		handleError(ctxt,
						"The left hand side of an unjoin scrutinee " +
						"evaluates to a term app whose head is not a function.\n" +
						"1. lhs:" + lhs.toString(ctxt) + "\n" +
						"2. evaluated head: " + ev.toString(ctxt) + "\n"
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
