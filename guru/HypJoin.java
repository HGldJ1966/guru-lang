package guru;

import java.util.*;

public class HypJoin extends Expr{
    
    public Expr t1;
    public Expr t2;
    public Expr [] Ps;
    public boolean mark = false;
    
    private Vector varOrderVec = new Vector();
    
    public HypJoin() {
        super(HYPJOIN);
    }

    public HypJoin(Expr t1, Expr t2, Expr[] Ps) {
        super(HYPJOIN);
        this.t1 = t1;
        this.t2 = t2;
        this.Ps = Ps;
    }
    
    public Expr dropAnnos(Context ctxt) {
    	return new Bang();
    }

    public void do_print(java.io.PrintStream w, 
		      Context ctxt) 
    {
		w.print("hypjoin ");
		t1.print(w,ctxt);
		w.print(" ");
		t2.print(w,ctxt);
		w.print(" by ");
		for(int i = 0; i < Ps.length; ++i)
		{
			Ps[i].print(w, ctxt);
			w.print(" ");
		}
		w.print("end");
    }

    public int numOcc(Expr e) {
    	int returnValue = t1.numOcc(e) + t2.numOcc(e);
    	for(int i = 0; i < Ps.length; ++i)
    	{
    		returnValue += Ps[i].numOcc(e);
    	}
    	return returnValue;
    }
    
    public Expr subst(Expr e, Expr x) 
    {
    	boolean changed = false;
    	Expr returnValue = this;
        Expr[] newPs = new Expr[Ps.length];
        for(int i = 0; i < Ps.length; ++i)
        {
            newPs[i] = Ps[i].subst(e, x);
            if(newPs[i] != Ps[i])
            {
            	changed = true;
            }
        }
        Expr substT1 = t1.subst(e,x);
        if(substT1 != t1)
        {
        	changed = true;
        }
        Expr substT2 = t2.subst(e,x);
        if(substT2 != t2)
        {
        	changed = true;
        }
        if(changed)
        {
        	returnValue =  new HypJoin(substT1, substT2, newPs);
        }
        
        return returnValue;
    }
    
    private boolean contains(Context ctxt, Atom[] theAtoms, Atom theAtom)
    {
    	boolean returnValue = false;
    	
    	for(int i = 0; i < theAtoms.length; ++i)
    	{
    		if(theAtoms[i].defEq(ctxt, theAtom))
    		{
    			returnValue = true;
    			break;
    		}
    		
    	}
    	
    	return returnValue;
    }
    
    private Atom[] complete(Context ctxt, Atom[] thePs, Stack boundVars)
    {
    	for(int i = 0; i < thePs.length; ++i)
    	{
    		Atom curAtom = thePs[i];
    		for(int j = 0; j < thePs.length; ++j)
    		{
    			if(i != j)
    			{
    				Expr rewY1 = curAtom.Y1.rewrite(ctxt, thePs[j].Y2, thePs[j].Y1, boundVars);
    				if(!rewY1.defEq(ctxt, curAtom.Y1))
    				{
    					// there is an overlap
    					Atom newRule = new Atom(curAtom.equality, rewY1, curAtom.Y2);
    					Atom orientedNewRule = orient(ctxt, newRule);			
    					if(!contains(ctxt, thePs, orientedNewRule))
    					{
    						Atom[] newRuleArr = new Atom[thePs.length + 1];
    						{
    							for(int k = 0; k < thePs.length; ++k)
    							{
    								newRuleArr[k] = thePs[k];
    							}
    							newRuleArr[newRuleArr.length - 1] = orientedNewRule;
    						}
    						return complete(ctxt, newRuleArr, boundVars);
    					}
    				}

    			}
    		}
    	}
    	
    	return thePs;
    }
    
    Expr orderedRewrite(Context ctxt, Expr e, Atom[] rewriteAtoms, Stack boundVars)
    {
    	Expr returnValue = e;
    	
	if (ctxt.getFlag("debug_ordered_rewrite")) {
	    returnValue.print(ctxt.w,ctxt);
	    ctxt.w.println(" --> ");
	    ctxt.w.flush();
	}

    	for(int i = 0; i < rewriteAtoms.length; ++i)
	    returnValue = returnValue.rewrite(ctxt, rewriteAtoms[i].Y2, rewriteAtoms[i].Y1, boundVars);

    	if(!returnValue.defEq(ctxt, e)) {
	    //   ctxt.printDefEqErrorIf();
	    returnValue = orderedRewrite(ctxt, returnValue, rewriteAtoms, boundVars);
	}

	if (ctxt.getFlag("debug_ordered_rewrite")) {
	    returnValue.print(ctxt.w,ctxt);
	    ctxt.w.println("");
	    ctxt.w.flush();
	}

    	return returnValue;
    }
    
    private Expr boundVarPreservingEval(Context ctxt, Expr e, Stack boundVars)
    {
    	Expr returnValue = e;
    	
    	if(!returnValue.containsVars(boundVars))
    	{
    		returnValue = returnValue.eval(ctxt);
    	}
    	
    	return returnValue;
    }

    private Expr buildExpr(Context ctxt, Expr e, Expr[] subExprs)
    {
    	Expr returnValue = null;
    	
    	if(e.construct == TERM_APP)
    	{
    		Expr[] X = new Expr[subExprs.length - 1];
    		for(int i = 0; i < subExprs.length - 1; ++i)
    		{
    			X[i] = subExprs[i+1];
    		}
    		returnValue = new TermApp(subExprs[0], X);
    	}
    	else if(e.construct == SIZE)
    	{
	    returnValue = new Size(subExprs[0]);
    	}
    	else if(e.construct == VAR)
    	{
    		returnValue = e;
    	}
    	else if(e.construct == LET)
    	{
    		Let lete = (Let)e;
    		Expr subExpr2 = lete.t2;
    		if(subExprs.length > 1)
    		{
    			subExpr2 = subExprs[1];
    		}
    		returnValue = new Let(lete.x1, lete.x1_stat, subExprs[0], lete.x2, subExpr2);
    	}
    	else if(e.construct == MATCH)
    	{
    		Match matche = (Match)e;
    		Case[] newCases = new Case[matche.C.length];
    		for(int i = 0; i < newCases.length; ++i)
    		{
    			newCases[i] = matche.C[i];
    		}
    		for(int i = 0; i < newCases.length; ++i)
    		{
    			if(subExprs.length > i + 1)
    			{
			    newCases[i] = new Case(matche.C[i].c, matche.C[i].x, subExprs[i+1],
						   false);   		
    			}
    		}
    		returnValue = new Match(subExprs[0], matche.x1, matche.x2, matche.T, newCases, matche.scrut_stat);
    	}
    	else if(e.construct == FUN_TERM)
    	{
    		FunTerm fune = (FunTerm)e;
    		Expr newBody = fune.body;
    		if(subExprs.length > 0)
    		{
    			newBody = subExprs[0];
    		}
    		returnValue = new FunTerm(fune.r, fune.T, fune.vars, fune.types, fune.owned, fune.ret_stat, newBody);
    	}
    	else if(e.construct == CONST)
    	{
    		returnValue = e;
    	}
    	else
    	{
    		handleError(ctxt,
     			   "Hypjoin does not support this sort of term: " + e.toString(ctxt));
     			
    		returnValue = e;
    	}
    	
    	return returnValue;
    }
    
    private Expr removeAbbrev(Context ctxt, Expr e)
    {
    	Expr returnValue = e;
    	
    	if(returnValue.construct == VAR)
    	{
    		if(ctxt.isMacroDefined((Var)returnValue))
    		{
    			return removeAbbrev(ctxt, ctxt.getDefBody((Var)returnValue).dropAnnos(ctxt));
    		}
    	}
    	
    	if(returnValue.construct == ABBREV)
    	{
    		return removeAbbrev(ctxt, ((Abbrev)returnValue).subst());
    	}
    	
    	int subtermsCount = getSubtermsCount(ctxt, returnValue);
    	Expr[] newSubterms = new Expr[subtermsCount];
    	boolean subtermChanged = false;
    	for(int i = 0; i < subtermsCount; ++i)
    	{
    		Expr curSubterm = getSubterm(ctxt, returnValue, i);
    		newSubterms[i] = removeAbbrev(ctxt, curSubterm);
    		if(newSubterms[i] != curSubterm)
    		{
    			subtermChanged = true;
    		}	
    	}
    	
    	if(subtermChanged)
    	{
    		returnValue = buildExpr(ctxt, returnValue, newSubterms);
    	}
    	
    	return returnValue;
    }
    
    private Expr normalizeWithCompleteRules(Context ctxt, Expr theExpr, Atom[] completeAtoms, Stack boundVars)
    {  
    	boolean subtermChanged = false;
    	int subtermCount = getEvaluationSubtermsCount(ctxt, theExpr);
    	Expr[] subtermsArr = new Expr[subtermCount];
    	
    	for(int i = 0; i < subtermCount; ++i)
    	{
    		Expr curSubterm = getSubterm(ctxt, theExpr, i);
    		
    		pushBoundVars(ctxt, theExpr, i, boundVars);
    		Expr normSubterm = normalizeWithCompleteRules(ctxt, curSubterm, completeAtoms, boundVars);
    		subtermChanged = subtermChanged || normSubterm != curSubterm;
    		popBoundVars(ctxt, theExpr, i, boundVars);
    		
    		subtermsArr[i] = normSubterm;
    	}
    	
    	
    	Expr normSubtermsExpr = theExpr;
    	if(subtermChanged)
    	{
    		normSubtermsExpr = buildExpr(ctxt, theExpr, subtermsArr);
    	}
    	
    	Expr rewrittenExpr = orderedRewrite(ctxt, normSubtermsExpr, completeAtoms, boundVars);
    	Expr evaldExpr = boundVarPreservingEval(ctxt, rewrittenExpr, boundVars);

    	if(!evaldExpr.defEq(ctxt, normSubtermsExpr))
    	{
    		return normalizeWithCompleteRules(ctxt, evaldExpr, completeAtoms, boundVars);
    	}
    	else
    	{
    		return normSubtermsExpr;
    	}
    }
    
    private int getLPO_ConstructValue(Context ctxt, Expr e)
    {
    	if(e.construct == ABORT)
    	{
    		return 8;
    	}
    	else if(e.construct == BANG)
    	{
    		return 7;
    	}
    	else if(e.construct == VAR)
    	{
    		return 6;
    	}
    	else if(e.construct == LET)
    	{
    		return 5;
    	}
    	else if(e.construct == MATCH || e.construct == SIZE)
    	{
    		return 4;
    	}
    	else if(e.construct == FUN_TERM)
    	{
    		return 3;
    	}
    	else if(e.construct == TERM_APP)
    	{
    		return 2;
    	}
    	else if(e.construct == CONST)
    	{
    		return 1;
    	}
    	else
    	{
    		handleError(ctxt,
     			   "Hypjoin does not support this sort of term: " + e.toString(ctxt));
     			
    		return 0;
    	}
    }
    
    private int getSubtermsCount(Context ctxt, Expr e)
    {
    	if(e.construct == TERM_APP)
    	{
    		TermApp appe = (TermApp)e;
    		return appe.X.length + 1;
    	}
    	else if(e.construct == VAR)
    	{
    		return 0;
    	}
    	else if(e.construct == LET)
    	{
    		return 2;
    	}
    	else if(e.construct == MATCH)
    	{
    		Match matche = (Match)e;
    		return matche.C.length + 1;
    	}
    	else if(e.construct == FUN_TERM)
    	{
    		return 1;
    	}
    	else if(e.construct == SIZE)
    	{
    		return 1;
    	}
    	else if(e.construct == CONST)
    	{
    		return 0;
    	}
    	else if(e.construct == BANG)
    	{
    		return 0;
    	}
    	else if(e.construct == ABORT)
    	{
    		return 0;
    	}
    	else
    	{
    		handleError(ctxt,
     			   "Hypjoin does not support " + e.getClass().toString() + "  The term is: " + e.toString(ctxt));
     			
    		return 10;
    	}
    }
    
    private int getEvaluationSubtermsCount(Context ctxt, Expr e)
    {
    	if(e.construct == TERM_APP)
    	{
    		TermApp appe = (TermApp)e;
    		return appe.X.length + 1;
    	}
    	else if(e.construct == VAR)
    	{
    		return 0;
    	}
    	else if(e.construct == LET)
    	{
    		return 1;
    	}
    	else if(e.construct == MATCH)
    	{
    		return 1;
    	}
    	else if(e.construct == SIZE)
    	{
    		return 1;
    	}
    	else if(e.construct == FUN_TERM)
    	{
    		return 0;
    	}
    	else if(e.construct == CONST)
    	{
    		return 0;
    	}
    	else if(e.construct == BANG)
    	{
    		return 0;
    	}
    	else if(e.construct == ABORT)
    	{
    		return 0;
    	}
    	else
    	{
    		handleError(ctxt,
     			   "Hypjoin does not support " + e.getClass().toString() + "  The term is: " + e.toString(ctxt));
     			
    		return 10;
    	}
    }
    
    private Expr getSubterm(Context ctxt, Expr e, int index)
    {
    	Expr returnValue = null;
    	if(e.construct == TERM_APP)
    	{
    		TermApp appe = (TermApp)e;
    		if(index == 0)
    		{
    			returnValue = appe.head;
    		}
    		else
    		{
    			returnValue = appe.X[index - 1];
    		}
    	}
    	else if(e.construct == LET)
    	{
    		Let lete = (Let)e;
    		if(index == 0)
    		{
    			returnValue = lete.t1;
    		}
    		else if(index == 1);
    		{
    			returnValue = lete.t2;
    		}
    	}
    	else if(e.construct == SIZE)
    	{
    		Size se = (Size)e;
		returnValue = se.t;
    	}
    	else if(e.construct == MATCH)
    	{
    		Match matche = (Match)e;
    		if(index == 0)
    		{
    			returnValue = matche.t;
    		}
    		else
    		{
    			returnValue = matche.C[index - 1].body;
    		}
    	}
    	else if(e.construct == FUN_TERM)
    	{
    		FunTerm fune = (FunTerm)e;
    		return fune.body;
    	}
    	else
    	{
    		handleError(ctxt,
     			   "Hypjoin does not support this sort of term: " + e.toString(ctxt));
     			
    	}
    	
    	return returnValue;
    }
    
    private void pushBoundVars(Context ctxt, Expr e, int index, Stack boundVars)
    {
    	if(e.construct == TERM_APP || e.construct == SIZE)
    	{
    		// do nothing
    	}
    	else if(e.construct == LET)
    	{
    		Let lete = (Let)e;
    		if(index == 1);
    		{
    			boundVars.push(lete.x1);
    			if(ctxt.getClassifier(lete.x1) == null)
    			{
    				ctxt.setClassifier(lete.x1, lete.t1.classify(ctxt));
    			}
    		}
    	}
    	else if(e.construct == MATCH)
    	{
    		Match matche = (Match)e;
    		if(index != 0)
    		{
    			Var[] newVars = matche.C[index - 1].x;
    			for(int i = 0; i < newVars.length; ++i)
    			{
    				boundVars.push(newVars[i]);
    				if(ctxt.getClassifier(newVars[i]) == null)
        			{
        				ctxt.setClassifier(newVars[i], newVars[i].classify(ctxt));
        			}
    			}
    		}

    	}
    	else if(e.construct == FUN_TERM)
    	{
    		FunTerm fune = (FunTerm)e;
    		for(int i = 0; i < fune.vars.length; ++i)
			{
				boundVars.push(fune.vars[i]);
				if(ctxt.getClassifier(fune.vars[i]) == null)
    			{
    				ctxt.setClassifier(fune.vars[i], fune.types[i]);
    			}
			}
    		
    	}
    	else
    	{
    		handleError(ctxt,
     			   "Hypjoin does not support this sort of term: " + e.toString(ctxt));
     			
    	}
    	
    }
    
    private void popBoundVars(Context ctxt, Expr e, int index, Stack boundVars)
    {
    	if(e.construct == TERM_APP || e.construct == SIZE)
    	{
    		// do nothing
    	}
    	else if(e.construct == LET)
    	{
    		if(index == 1);
    		{
    			boundVars.pop();
    		}
    	}
    	else if(e.construct == MATCH)
    	{
    		Match matche = (Match)e;
    		if(index != 0)
    		{
    			Var[] newVars = matche.C[index - 1].x;
    			for(int i = 0; i < newVars.length; ++i)
    			{
    				boundVars.pop();
    			}
    		}

    	}
    	else if(e.construct == FUN_TERM)
    	{
    		FunTerm fune = (FunTerm)e;
    		for(int i = 0; i < fune.vars.length; ++i)
			{
				boundVars.pop();
				
			}
    		
    	}
    	else
    	{
    		handleError(ctxt,
     			   "Hypjoin does not support this sort of term: " + e.toString(ctxt));
     			
    	}
    	
    }
    
    private int varOrderIndex(Var v)
    {
    	int returnValue = -1;
    	for(int i = 0; i < varOrderVec.size(); ++i)
    	{
    		if(varOrderVec.elementAt(i) == v)
    		{
    			returnValue = i;
    			break;
    		}
    	}
    	
    	return returnValue;
    }
    
    private void addToVarOrder(Var v)
    {
    	if(varOrderIndex(v) < 0)
    	{
    		varOrderVec.insertElementAt(v, 0);
    	}
    }
    
    private boolean varGreaterThan(Var v1, Var v2)
    {
    	if(varOrderIndex(v2) < 0)
    	{
    		varOrderVec.add(v2);
    	}
    	if(varOrderIndex(v1) < 0)
    	{
    		varOrderVec.insertElementAt(v1, 0);
    	}
    	
    	return varOrderIndex(v1) < varOrderIndex(v2);
    }
    
    private boolean functionGreaterThanLPO(Context ctxt, Expr e1, Expr e2)
    {
    	boolean returnValue = false;
    	if(getLPO_ConstructValue(ctxt, e1) > getLPO_ConstructValue(ctxt, e2))
    	{
    		returnValue = true;
    	}
    	else if(getLPO_ConstructValue(ctxt, e1) == getLPO_ConstructValue(ctxt, e2))
    	{
    		returnValue = getSubtermsCount(ctxt, e1) > getSubtermsCount(ctxt, e2);
    	
    		if(e1.construct == VAR && e2.construct == VAR)
    		{
    			Var vare1 = (Var)e1;
    			Var vare2 = (Var)e2;
    			returnValue = varGreaterThan(vare1, vare2);
    		}
    	}
    	
    	return returnValue;	
    }
    
    private boolean functionEqualsLPO(Context ctxt, Expr e1, Expr e2)
    {
    	boolean returnValue = false;
    	if(getLPO_ConstructValue(ctxt, e1) == getLPO_ConstructValue(ctxt, e2))
    	{
    		returnValue = getSubtermsCount(ctxt, e1) == getSubtermsCount(ctxt, e2);
    		
    		if(e1.construct == VAR && e2.construct == VAR)
    		{
    			returnValue = e1 == e2;
    		}
    	}
    	
    	return returnValue;	
    }
    
    private boolean greaterThanLPO_Subterms(Context ctxt, Expr e1, Expr e2)
    {
    	boolean returnValue = true;
    	
    	int subtermsCount = getSubtermsCount(ctxt, e2);
		for(int i = 0; i < subtermsCount; ++i)
		{
			Expr curSubterm = getSubterm(ctxt, e2, i);	
			if(!greaterThanLPO(ctxt, e1, curSubterm))
			{
				returnValue = false;
				break;
			}
		}
		return returnValue;
    }
    
    // Compares e1 and e2 in a lexicographic path ordering
    // returns true if e1 > e2 in LPO
    // returns false otherwise
    private boolean greaterThanLPO(Context ctxt, Expr e1, Expr e2)
    {
    	while(e1.construct == ABBREV)
    	{
    		e1 = ((Abbrev)e1).subst();
    	}
    	while(e2.construct == ABBREV)
    	{
    		e2 = ((Abbrev)e2).subst();
    	}
    	
    	boolean returnValue = false;
    	if(functionGreaterThanLPO(ctxt, e1, e2))
    	{
    		returnValue = greaterThanLPO_Subterms(ctxt, e1, e2);
    	}
    	else if(functionEqualsLPO(ctxt, e1, e2))
    	{
    		if(greaterThanLPO_Subterms(ctxt, e1, e2))
    		{
    			int subtermsCount = getSubtermsCount(ctxt, e1);
    			for(int i = 0; i < subtermsCount; ++i)
    			{
    				Expr e1Subterm = getSubterm(ctxt, e1, i);
    				Expr e2Subterm = getSubterm(ctxt, e2, i);
    				if(greaterThanLPO(ctxt, e1Subterm, e2Subterm))
    				{
    					returnValue = true;
    					break;
    				}
    				else if(greaterThanLPO(ctxt, e2Subterm, e1Subterm))
    				{
    					break;
    				}
    			}
    		}
    	}
    	return returnValue;
    }
    
    // we use Atoms to store ordered rewrite rules 
    // of the form Y1 -> Y2
    private Atom orient(Context ctxt, Atom theP)
    {
    	Atom returnValue = theP;
    	
    	if(theP.Y1.construct == VAR)
    	{
    		addToVarOrder((Var)theP.Y1);
    	}
    	if(theP.Y2.construct == VAR)
    	{
    		addToVarOrder((Var)theP.Y2);
    	}
    	
    	if(greaterThanLPO(ctxt, theP.Y2, theP.Y1))
    	{
    		returnValue = new Atom(theP.equality, theP.Y2, theP.Y1);
    	}
    	
    	return returnValue;
    }
    
    private Atom[] orient(Context ctxt, Atom[] thePs)
    {
    	Atom[] returnValue = new Atom[thePs.length];
    	for(int i = 0; i < thePs.length; ++i)
    	{
    		returnValue[i] = orient(ctxt, thePs[i]);
    	}
    	return returnValue;
    }
    
    private void checkConsistency(Context ctxt, Atom[] completeRules)
    {
    	for(int i = 0; i < completeRules.length; ++i)
    	{
    		Expr curY1 = completeRules[i].Y1;
    		Expr curY2 = completeRules[i].Y2;
    		
    		if(curY1 instanceof TermApp)
    		{
    			TermApp appY1 = (TermApp)curY1;
    			if(appY1.head instanceof Const &&
    			   ctxt.isTermCtor((Const)appY1.head))
    			{
    				if(curY2 instanceof TermApp)
    				{
    					TermApp appY2 = (TermApp)curY2;
    					if(appY2.head instanceof Const &&
    					   ctxt.isTermCtor((Const)appY2.head) &&
    					   !appY1.head.defEq(ctxt, appY2.head))
    					{
    						handleError(ctxt,
    			    				   "Atoms in hypjoin may not allow equality of applications headed by two different term constructors: " + completeRules[i].toString(ctxt));
    			    			
    					}
    				}
    				else if(curY2 instanceof Const &&
    						ctxt.isTermCtor((Const)curY2))	
					{
						handleError(ctxt,
		    				   "Atoms in hypjoin may not allow equality of a term constructor and an application headed by a term constructor: " + completeRules[i].toString(ctxt));
		    			
					}
    				
    			}
    		}
    		else if(curY1 instanceof Const)
    		{
    			// due to ordering, curY2 must be a constant
    			// these terms must be equal
    			if(!curY1.defEq(ctxt, curY2))
    			{
    				handleError(ctxt,
    				   "Atoms in hypjoin may not allow equality of two different term constructors: " + completeRules[i].toString(ctxt));
    			}
    		}
    	}
    }
    
    
    private Expr normalize(Context ctxt, Expr theExpr, Atom[] thePs)
    {

    	theExpr = theExpr.dropAnnos(ctxt);
    	theExpr = removeAbbrev(ctxt, theExpr);
    	
    	Stack emptyBoundVars = new Stack();
    	Atom[] orientedPs = orient(ctxt, thePs);
    	Atom[] completePs = complete(ctxt, orientedPs, emptyBoundVars);

    	checkConsistency(ctxt, completePs);
    	
    	return normalizeWithCompleteRules(ctxt, theExpr, completePs, emptyBoundVars);
    }
    
    private Atom[] getAtomArray(Context ctxt, Expr[] theExprs)
    {
    	Atom[] returnValue = new Atom[theExprs.length];
    	for(int i = 0; i < theExprs.length; ++i)
    	{
    		Expr curExpr = theExprs[i].classify(ctxt);
    		if(curExpr.construct == ATOM)
    		{
    			returnValue[i] = (Atom)curExpr;
    			if(!returnValue[i].equality)
    			{
			    handleError
				(ctxt,
				 "A proof in a hypjoin proves a disequality"
				 +" instead of an equality."
				 +"\n1. the proof: "+theExprs[i].toString(ctxt)
				 +"\n2. its classifier: "+ curExpr.toString(ctxt));
    			}
    		}
    		else
    		{
		    handleError
			(ctxt,
			 "A proof in a hypjoin does not prove an equality."
			 +"\n1. the proof: "+theExprs[i].toString(ctxt)
			 +"\n2. its classifier: "+ curExpr.toString(ctxt));
    			
    		}
    	}
    	return returnValue;
    }
    
    // changes thePs array and puts all atoms in normal form
    // returns true if something was changed, false otherwise
    private boolean normalize(Context ctxt, Atom[] thePs)
    {
    	if(thePs.length == 0)
    	{
    		return false;
    	}
    	
    	for(int i = 0; i < thePs.length; ++i)
    	{
    		Atom curAtom = thePs[i];
    		Atom[] smallerAtoms = new Atom[thePs.length - 1];
    		int smallerIndex = 0;
    		for(int j = 0; j < thePs.length; ++j)
    		{
    			if(j != i)
    			{
    				smallerAtoms[smallerIndex++] = thePs[j];
    			}
    		}
    		boolean smallerAtomsChanged = normalize(ctxt, smallerAtoms);

    		Expr normY1 = normalize(ctxt, curAtom.Y1, smallerAtoms);
    		Expr normY2 = normalize(ctxt, curAtom.Y2, smallerAtoms);
    		Atom normCurAtom = new Atom(curAtom.equality, normY1, normY2);
    		boolean curAtomChanged = !normY1.defEq(ctxt, curAtom.Y1) || !normY2.defEq(ctxt, curAtom.Y2);

		smallerIndex = 0;
		for(int j = 0; j < thePs.length; ++j)
		    {
			if (j == i)
			    thePs[j] = normCurAtom;
			else
			    thePs[j] = smallerAtoms[smallerIndex++];
		    }
		if(smallerAtomsChanged || curAtomChanged)
		    {
			normalize(ctxt, thePs);
			return true;
		    }
    	}
    	
    	return false;
    }
    
    private boolean equalModEquations(Context ctxt, Expr e1, Expr e2,
				      Atom[] equations, Stack boundVars)
    {
    	Atom[] orientedPs = orient(ctxt, equations);
    	Atom[] completePs = complete(ctxt, orientedPs, boundVars);
    	Expr ne1 = orderedRewrite(ctxt, e1, completePs, boundVars);
    	Expr ne2 = orderedRewrite(ctxt, e2, completePs, boundVars);
    	return ne1.defEq(ctxt, ne2);
    }
    
    private String getArrString(Context ctxt, Atom[] theAtoms)
    {
    	StringBuffer buf = new StringBuffer();
    	for(int i = 0; i < theAtoms.length; ++i)
    	{
    		buf.append("\t"+(i+1)+") "+theAtoms[i].toString(ctxt)+"\n");
    	}
    	return buf.toString();
    }

    public Expr classify(Context ctxt) 
    {
    	if(mark)
    	{
    		int i = 0;
    	}
    	
		Atom[] proofAtoms = getAtomArray(ctxt, Ps);
		normalize(ctxt, proofAtoms);

    	Expr e1 = normalize(ctxt, t1, proofAtoms);
        Expr e2 = normalize(ctxt, t2, proofAtoms);
        
        Stack emptyContext = new Stack();
        if(equalModEquations(ctxt, e1, e2, proofAtoms, emptyContext))
	    return new Atom(true, t1, t2);
        
        handleError(ctxt,
      		    "Evaluation cannot join two terms" 
      		    +" in a hypjoin proof.\n"
      		    +"1. Normal form of first term: "+e1.toString(ctxt)+"\n"
      		    +"2. Normal form of second term: "+e2.toString(ctxt)+"\n"
      		    +"3. Normal form of equations:\n" + getArrString(ctxt, proofAtoms));
   
    
      	return null;
	      	
    }

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars)
    { 
    	for(int i = 0; i < Ps.length; ++i)
    	{
    		Ps[i].checkTermination(ctxt, IH,arg,vars);
    	}
    }

    public java.util.Set getDependences() {
        java.util.Set s = t1.getDependences();
        s.addAll(t2.getDependences());
        for(int i = 0, n = Ps.length; i < n; ++i)
            s.addAll(Ps[i].getDependences());
        return s;
    }
}
