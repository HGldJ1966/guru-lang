package guru;

import java.util.*;

public class HypJoin extends Expr{
    
    public Expr t1;
    public Expr t2;
    public Expr [] Ps;
    public boolean mark = false;
    
    private Expr stuck;
    private Expr[] stucks;

    private class UnorderableException extends Exception {}
    private class OrderingRestartRequiredException extends Exception {}
    private class InconsistentException extends Exception
    {
    	public InconsistentException(String s)
    	{
    		super(s);
    	}
    }
    
    private class OrderMap
    {
    	public static final int UNKNOWN = 0;
    	public static final int GREATER = 1;
    	public static final int NOT_GREATER = 2;
    	
    	private class MapEntry
    	{
    		private Expr e1;
    		private Expr e2;
    		private Context ctxt;
    		
    		public MapEntry(Expr e1, Expr e2, Context ctxt)
    		{
    			this.e1 = e1;
    			this.e2 = e2;
    			this.ctxt = ctxt;
    		}
    		
    		public int hashCode()
    		{
		    return e1.hashCode(ctxt) + e2.hashCode(ctxt);

		    // very slow this way:
		    //return e1.toString(ctxt).hashCode() + e2.toString(ctxt).hashCode();
    		}
    		public boolean equals(Object objEntry)
    		{
    			MapEntry entry = (MapEntry)objEntry;
    			return e1.defEq(ctxt, entry.e1) && e2.defEq(ctxt, entry.e2);
    			
    		}
    	}
    	
    	private Hashtable map = new Hashtable();
    	
    	// the following variables are used to measure the performance of the map
    	int hits = 0;
    	int misses = 0;
    	
    	public int compare(Expr e1, Expr e2, Context ctxt)
    	{
    		int result = UNKNOWN;
    		MapEntry entry = new MapEntry(e1, e2, ctxt);
    		Boolean greater = (Boolean)map.get(entry);
    		if(greater != null)
    		{
    			++hits;
    			if(greater.booleanValue())
    			{
    				result = GREATER;
    			}
    			else
    			{
    				result = NOT_GREATER;
    			}
    		}
    		else
    		{
    			++misses;
    		}
    		return result;
    	}
    	
    	public void addGreaterThan(Expr e1, Expr e2, boolean greater, Context ctxt)
    	{
    		MapEntry entry = new MapEntry(e1, e2, ctxt);
    		map.put(entry, new Boolean(greater));
    	}
    }
    
    private class VarOrder
    {
    	
    	private class ConstraintTable extends Hashtable{}
    	
    	private ConstraintTable requiredConstraints = new ConstraintTable();
    	private ConstraintTable arbitraryConstraints = new ConstraintTable();
    	
    	public static final int CONSTRAINT_ADD_RESULT_SUCCESS = 0;
    	public static final int CONSTRAINT_ADD_RESULT_RESTART_REQUIRED = 1;
    	public static final int CONSTRAINT_ADD_RESULT_FAIL = 2;
    	
    	public void clearArbitraryConstraints()
    	{
    		arbitraryConstraints.clear();
    	}
    	
    	public boolean varGreaterThan(Var v1, Var v2)
    	{
    		if(checkVarGreaterThan(v1, v2))
    		{
    			return true;
    		}
    		if(checkVarGreaterThan(v2, v1))
    		{
    			return false;
    		}
    		if(v1 == v2)
    		{
    			return false;
    		}
    		addArbitraryConstraint(v1, v2);
    		return true;
    	}
    	
    	private boolean checkVarGreaterThanRequired(Var v1, Var v2)
    	{
    		// v1 >* v2 iff exists v3 such that v1 > v3 v3 >* v2
    		Vector constraints = getRequiredConstraintEntriesStartingWith(v1);
    		Iterator constraintIter = constraints.iterator();
    		while(constraintIter.hasNext())
    		{
		    Var curEntry = (Var)constraintIter.next();
    			if(curEntry == v2)
    			{
    				return true;
    			}
    		}
    		
    		constraintIter = constraints.iterator();
    		while(constraintIter.hasNext())
    		{
		    Var curEntry = (Var)constraintIter.next();
    			if(checkVarGreaterThanRequired(curEntry, v2))
    			{
    				return true;
    			}
    		}
    		
    		return false;
    		
    	}
    	
    	private Vector getRequiredConstraintEntriesStartingWith(Var v)
    	{
	    Vector result = (Vector)requiredConstraints.get(v);
    		if(result == null)
    		{
    			result = new Vector();
    			requiredConstraints.put(v, result);
    		}
    		return result;
    	}
    	
    	private Vector getArbitraryConstraintEntriesStartingWith(Var v)
    	{
	    Vector result = (Vector)arbitraryConstraints.get(v);
    		if(result == null)
    		{
    			result = new Vector();
    			arbitraryConstraints.put(v, result);
    		}
    		return result;
    	}
    	
    	private boolean checkVarGreaterThan(Var v1, Var v2)
    	{
    		// v1 >* v2 iff exists v3 such that v1 > v3 v3 >* v2
    		Vector requiredConstraints = getRequiredConstraintEntriesStartingWith(v1);
    		Vector arbitraryConstraints = getArbitraryConstraintEntriesStartingWith(v1);
    		
    		Iterator constraintIter = requiredConstraints.iterator();
    		while(constraintIter.hasNext())
    		{
		    Var curEntry = (Var)constraintIter.next();
    			if(curEntry == v2)
    			{
    				return true;
    			}
    		}
    		constraintIter = arbitraryConstraints.iterator();
    		while(constraintIter.hasNext())
    		{
    			Var curEntry = (Var)constraintIter.next();
    			if(curEntry == v2)
    			{
    				return true;
    			}
    		}
    		
    		constraintIter = requiredConstraints.iterator();
    		while(constraintIter.hasNext())
    		{
    			Var curEntry = (Var)constraintIter.next();
    			if(checkVarGreaterThan(curEntry, v2))
    			{
    				return true;
    			}
    		}
    		
    		constraintIter = arbitraryConstraints.iterator();
    		while(constraintIter.hasNext())
    		{
    			Var curEntry = (Var)constraintIter.next();
    			if(checkVarGreaterThan(curEntry, v2))
    			{
    				return true;
    			}
    		}
    		
    		return false;
    		
    	}
    	
    	// Add an arbitrary constraint that v1 > v2
    	private void addArbitraryConstraint(Var v1, Var v2)
    	{
    		if(v1 == v2)
    		{
    			throw new RuntimeException("Attempt to add " + v1.name + ">" + v2.name + " to var order");
    		}
    		
    		Vector constraintList = (Vector)arbitraryConstraints.get(v1);
    		if(constraintList == null)
    		{
    			constraintList = new Vector();
    			arbitraryConstraints.put(v1, constraintList);
    		}
    		constraintList.add(v2);
    	}
    	
    	// Add a required constraint that v1 > v2
    	public int addRequiredConstraint(Var v1, Var v2)
    	{
    		if(v1 == v2)
    		{
    			// do nothing
    			// note that the desire to add v>v may indicate inconsistency,
    			//	which will be found later
    			return CONSTRAINT_ADD_RESULT_SUCCESS;
    		}
    		
    		if(checkVarGreaterThanRequired(v2, v1))
    		{
    			return CONSTRAINT_ADD_RESULT_FAIL;
    		}
    		
    		int returnValue = CONSTRAINT_ADD_RESULT_SUCCESS;  		
    		if(checkVarGreaterThan(v2, v1))
    		{
    			returnValue = CONSTRAINT_ADD_RESULT_RESTART_REQUIRED;
    		}
    		
    		Vector constraintList = (Vector)requiredConstraints.get(v1);
    		if(constraintList == null)
    		{
    			constraintList = new Vector();
    			requiredConstraints.put(v1, constraintList);
    		}
    		constraintList.add(v2);

    		return returnValue;
    	}
    	
    	public int addRequiredConstraints(Var v1, Collection v2s)
    	{
    		int returnValue = CONSTRAINT_ADD_RESULT_SUCCESS;
    		Iterator varIter = v2s.iterator();
    		while(varIter.hasNext())
    		{
		    Var curVar = (Var)varIter.next();
    			int curReturn = addRequiredConstraint(v1, curVar);
    			if(curReturn != CONSTRAINT_ADD_RESULT_SUCCESS)
    			{
    				return curReturn;
    			}
    		}
    		
    		return returnValue;
    	}
    }
    
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
    
    private Atom[] complete(Context ctxt, Atom[] thePs, Stack boundVars, VarOrder theVarOrder, OrderMap theOrderMap)
    	throws OrderingRestartRequiredException, UnorderableException
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
    					Atom orientedNewRule = orient(ctxt, newRule, theVarOrder, theOrderMap);			
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
    						return complete(ctxt, newRuleArr, boundVars, theVarOrder, theOrderMap);
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
    		returnValue = new Match(subExprs[0], matche.x1, matche.x2, matche.T, newCases, false);
    	}
    	else if(e.construct == FUN_TERM)
    	{
    		FunTerm fune = (FunTerm)e;
    		Expr newBody = fune.body;
    		if(subExprs.length > 0)
    		{
    			newBody = subExprs[0];
    		}
    		returnValue = new FunTerm(fune.r, fune.T, fune.vars, fune.types, fune.owned, fune.consumps,
					  fune.ret_stat, newBody);
    	}
    	else if(e.construct == CONST)
    	{
    		returnValue = e;
    	}
	else if (e.construct == DO) {

    		Expr[] X = new Expr[subExprs.length - 1];
    		for(int i = 0; i < subExprs.length - 1; ++i)
    		{
    			X[i] = subExprs[i];
    		}
    		returnValue = new Do(X, subExprs[subExprs.length - 1]);
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
    	
	if (ctxt.getFlag("debug_hypjoin_normalize")) {
	    ctxt.w.println("(Hyjpoin.normalizeWithCompleteRules");
	    ctxt.w.print("theExpr = ");
	    theExpr.print(ctxt.w,ctxt);
	    ctxt.w.println("");
	    ctxt.w.flush();
	}

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
    	
	if (ctxt.getFlag("debug_hypjoin_normalize")) {
	    ctxt.w.print("normSubtermsExpr = ");
	    normSubtermsExpr.print(ctxt.w,ctxt);
	    ctxt.w.println("");
	    ctxt.w.flush();
	}


    	Expr rewrittenExpr = orderedRewrite(ctxt, normSubtermsExpr, completeAtoms, boundVars);
    	Expr evaldExpr = boundVarPreservingEval(ctxt, rewrittenExpr, boundVars);

	Expr ret = normSubtermsExpr;

    	if(!evaldExpr.defEq(ctxt, normSubtermsExpr))
    	{
	    ret = normalizeWithCompleteRules(ctxt, evaldExpr, completeAtoms, boundVars);

    	}

	if (stuck == null) {
	    if (ret.construct == Expr.MATCH)
		if (normSubtermsExpr.construct != Expr.MATCH)
		    stuck = normSubtermsExpr;
		else if (theExpr.construct != Expr.MATCH)
		    stuck = theExpr;
	    if (stuck != null && ctxt.getFlag("debug_hypjoin_normalize")) {
		ctxt.w.print("stuck = ");
		stuck.print(ctxt.w,ctxt);
		ctxt.w.println("");
		ctxt.w.flush();
	    }
	}

	if (ctxt.getFlag("debug_hypjoin_normalize")) {
	    ctxt.w.print("ret = ");
	    ret.print(ctxt.w,ctxt);
	    ctxt.w.println(")");
	    ctxt.w.flush();
	}

	return ret;
    }
    
    private int getLPO_ConstructValue(Context ctxt, Expr e)
    {
    	if(e.construct == ABORT)
    	{
    		return 10;
    	}
    	else if(e.construct == BANG)
    	{
	    return 9;
    	}
    	else if(e.construct == LET)
    	{
    		return 8;
    	}
    	else if(e.construct == DO)
    	{
	    return 7;
    	}
    	else if(e.construct == MATCH || e.construct == SIZE)
    	{
	    return 6;
    	}
    	else if(e.construct == TERM_APP && 
    			((TermApp)e).head.construct != CONST )
    	{
	    return 5;
    	}
    	else if(e.construct == VAR)
    	{
    		return 4;
    	}
    	else if(e.construct == FUN_TERM)
    	{
    		return 3;
    	}
    	else if(e.construct == TERM_APP && 
    			((TermApp)e).head.construct == CONST )
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
	else if (e.construct == DO) {
	    return ((Do)e).ts.length+1;
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
	else if (e.construct == DO) {
	    return ((Do)e).ts.length+1;
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
    	else if(e.construct == DO)
    	{
    		Do doe = (Do)e;
    		if(index >= doe.ts.length)
    		{
		    returnValue = doe.t;
    		}
    		else
    		{
		    returnValue = doe.ts[index];
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
    	if(e.construct == TERM_APP || e.construct == SIZE || e.construct == DO)
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
    	if(e.construct == TERM_APP || e.construct == SIZE || e.construct == DO)
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
    
    private boolean functionGreaterThanLPO(Context ctxt, Expr e1, Expr e2, VarOrder theVarOrder)
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
    			returnValue = theVarOrder.varGreaterThan(vare1, vare2);
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
    		else if(e1.construct == CONST && e2.construct == CONST)
    		{
    			returnValue = e1 == e2;
    		}
    	}
    	
    	return returnValue;	
    }
    
    // Compares e1 and e2 in a lexicographic path ordering
    // returns true if e1 > e2 in LPO
    // returns false otherwise
    private boolean greaterThanLPO(Context ctxt, Expr e1, Expr e2, VarOrder theVarOrder, OrderMap theOrderMap)
    {
    	if(e1.defEq(ctxt, e2))
    	{
    		return false;
    	}
    	
    	//System.out.println("in greaterThanLPO with \n" + 
    	//		"\te1 = " + e1.toString(ctxt) + "\n" + 
    	//		"\te2 = " + e2.toString(ctxt));
    	
    	while(e1.construct == ABBREV)
    	{
    		e1 = ((Abbrev)e1).subst();
    	}
    	while(e2.construct == ABBREV)
    	{
    		e2 = ((Abbrev)e2).subst();
    	}  	
    	
    	int mapResult = theOrderMap.compare(e1, e2, ctxt);
    	if(mapResult == OrderMap.GREATER)
    	{
    		return true;
    	}
    	else if(mapResult == OrderMap.NOT_GREATER)
    	{
    		return false;
    	}
    	
    	boolean returnValue = false;
    	if(!returnValue)
    	{
	    	for(int i = 0; i < getSubtermsCount(ctxt, e1); ++i)
	    	{
	    		Expr curSubTerm = getSubterm(ctxt, e1, i);
	    		if(greaterThanLPO(ctxt, curSubTerm, e2, theVarOrder, theOrderMap) || curSubTerm.defEq(ctxt, e2))
	    		{
	    			returnValue = true;
	    			break;
	    		}
	    	}
    	}
    	if(!returnValue)
    	{
	    	if(functionGreaterThanLPO(ctxt, e1, e2, theVarOrder) && greaterLPO_ThanAllSubterms(ctxt, e1, e2, theVarOrder, theOrderMap))
	    	{
	    		returnValue = true;		
	    	}
    	}
    	if(!returnValue)
    	{
	    	if(functionEqualsLPO(ctxt, e1, e2))
	    	{
	    		if(greaterLPO_ThanAllSubterms(ctxt, e1, e2, theVarOrder, theOrderMap))
	    		{
	    			int subtermsCount = getSubtermsCount(ctxt, e1);
	    			for(int i = 0; i < subtermsCount; ++i)
	    			{
	    				Expr e1Subterm = getSubterm(ctxt, e1, i);
	    				Expr e2Subterm = getSubterm(ctxt, e2, i);
	    				if(greaterThanLPO(ctxt, e1Subterm, e2Subterm, theVarOrder, theOrderMap))
	    				{
	    					returnValue = true;
	    					break;
	    				}
	    				else if(greaterThanLPO(ctxt, e2Subterm, e1Subterm, theVarOrder, theOrderMap))
	    				{
	    					break;
	    				}
	    			}
	    		}
	    	}
    	}
    		
    	theOrderMap.addGreaterThan(e1, e2, returnValue, ctxt);
    	
    	return returnValue;
    }
    
    private boolean greaterLPO_ThanAllSubterms(Context ctxt, Expr e1, Expr e2, VarOrder theVarOrder, OrderMap theOrderMap) 
    {
		boolean returnValue = true;
		for(int i = 0; i < getSubtermsCount(ctxt, e2); ++i)
		{
			if(!greaterThanLPO(ctxt, e1, this.getSubterm(ctxt, e2, i), theVarOrder, theOrderMap))
			{
				returnValue = false;
				break;
			}
		}
		return returnValue;
	}

	// we use Atoms to store ordered rewrite rules 
    // of the form Y1 -> Y2
    private Atom orient(Context ctxt, Atom theP, VarOrder theVarOrder, OrderMap theOrderMap) 
    	throws OrderingRestartRequiredException, UnorderableException
    {
    	Atom returnValue = theP;
  
    	int constraintAddResult = VarOrder.CONSTRAINT_ADD_RESULT_SUCCESS;
    	
    	if(theP.Y1.construct == VAR && theP.Y2.construct == TERM_APP &&
    			((TermApp)theP.Y2).head.construct == CONST)
    	{
    		Vector y2Vars = new Vector();
    		theP.Y2.getFreeVarsComputational(ctxt, y2Vars);
    		theVarOrder.addRequiredConstraints((Var)theP.Y1, y2Vars);
    	}
    	else if(theP.Y2.construct == VAR && theP.Y1.construct == TERM_APP &&
    			((TermApp)theP.Y1).head.construct == CONST)
    	{
    		Vector y1Vars = new Vector();
    		theP.Y1.getFreeVarsComputational(ctxt, y1Vars);
    		theVarOrder.addRequiredConstraints((Var)theP.Y2, y1Vars);
    	}
    	
    	if(constraintAddResult == VarOrder.CONSTRAINT_ADD_RESULT_RESTART_REQUIRED)
    	{
    		throw new OrderingRestartRequiredException();
    	}
    	else if(constraintAddResult == VarOrder.CONSTRAINT_ADD_RESULT_FAIL)
    	{
    		throw new UnorderableException();
    	}
    	
    	// test code
    	/*
    	if(greaterThanLPO(ctxt, theP.Y1, theP.Y2, theVarOrder))
    	{
    		if(greaterThanLPO(ctxt, theP.Y2, theP.Y1, theVarOrder))
    		{
    			throw new RuntimeException("Two terms are greater than each other in LPO\n1: "+theP.Y1.toString(ctxt)+"\n2: "+theP.Y2.toString(ctxt));
    		}
    		if(theP.Y1.defEq(ctxt, theP.Y2))
    		{
    			throw new RuntimeException("Term one is greater than AND equal to term 2 in LPO\n1: "+theP.Y1+"\n2: "+theP.Y2);
    		}
    	}
    	else
    	{
    		if(!greaterThanLPO(ctxt, theP.Y2, theP.Y1, theVarOrder) && !theP.Y1.defEq(ctxt, theP.Y2))
    		{
    			throw new RuntimeException("Two terms are unrelated in LPO\n1: "+theP.Y1+"\n2: "+theP.Y2);
    		}
    	}
    	*/
    	// end test code
    	
    	if(greaterThanLPO(ctxt, theP.Y2, theP.Y1, theVarOrder, theOrderMap))
    	{
    		returnValue = new Atom(theP.equality, theP.Y2, theP.Y1);
    	}
    	
    	return returnValue;
    }
    
    private Atom[] orient(Context ctxt, Atom[] thePs, VarOrder theVarOrder, OrderMap theOrderMap)
    	throws OrderingRestartRequiredException, UnorderableException
    {
    	Atom[] returnValue = new Atom[thePs.length];
    	for(int i = 0; i < thePs.length; ++i)
    	{
    		returnValue[i] = orient(ctxt, thePs[i], theVarOrder, theOrderMap);
    	}
    	return returnValue;
    }
    
    private void checkConsistency(Context ctxt, Atom[] completeRules)
    {
    	for(int i = 0; i < completeRules.length; ++i)
    	{
    		Expr curY1 = completeRules[i].Y1;
    		Expr curY2 = completeRules[i].Y2;
    		
    		if(curY1.defEq(ctxt, curY2))
    		{
    			// a term can always be equal to itself, regardless of other rules
    			continue;
    		}
    		
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
    		
    		if(isValueContainingExpr(ctxt, curY2, curY1) || 
    		   isValueContainingExpr(ctxt, curY1, curY2))
			{
				handleError(ctxt, 
					"Atoms in hypjoin may not allow equality of an expression and a value containing that expression: " + completeRules[i].toString(ctxt));
				
			}
    		
    	}
    }
    
    private boolean isValueContainingExpr(Context ctxt, Expr e, Expr v)
    {
    	boolean returnValue = false;
    	
    	if(e.defEq(ctxt, v))
    	{
    		returnValue = true;
    	}
    	else if(e instanceof TermApp)
    	{
    		TermApp appE = (TermApp)e;
    		if(appE.head instanceof Const)
    		{
    			for(int i = 0; i < appE.X.length; ++i)
    			{
    				returnValue = returnValue || isValueContainingExpr(ctxt, appE.X[i], v);
    			}
    		}
    	}
    	
    	return returnValue;
    }
    
    private Expr[] normalize(Context ctxt, Expr[] theExprs, Atom[] thePs)
    {

    	Expr[] result = new Expr[theExprs.length];
	stucks = new Expr[theExprs.length];
    	
    	Stack emptyBoundVars = new Stack();
    	VarOrder theVarOrder = new VarOrder();
    	
    	for(int i = 0; i < 100; ++i)
    	{
    		try
    		{
    			OrderMap theOrderMap = new OrderMap();
		    	Atom[] orientedPs = orient(ctxt, thePs, theVarOrder, theOrderMap);
		    	Atom[] completePs = complete(ctxt, orientedPs, emptyBoundVars, theVarOrder, theOrderMap);
		
		    	checkConsistency(ctxt, completePs);
		    	
		    	for(int exprIndex = 0; exprIndex < theExprs.length; ++exprIndex)
		    	{
		    		Expr curExpr = theExprs[exprIndex];
		    		curExpr = curExpr.dropAnnos(ctxt);
		    		curExpr = removeAbbrev(ctxt, curExpr);
				stuck = null;
		    		result[exprIndex] = normalizeWithCompleteRules(ctxt, curExpr, completePs, emptyBoundVars);
				stucks[exprIndex] = stuck;
				
		    	}
		    	
		    	return result;
    		}
    		catch(UnorderableException ex)
    		{
    			handleError(ctxt, "Unable to order the variables in the supplied equations: " + 
    					getArrString(ctxt, thePs));
    		}
    		catch(OrderingRestartRequiredException ex)
    		{
    			theVarOrder.clearArbitraryConstraints();
    		}
    	}
    	
    	handleError(ctxt, "Unable to order the variables in the supplied equations: " + 
				getArrString(ctxt, thePs));
    	return null;
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

    		Expr [] sourceExprs = new Expr[2];
    		sourceExprs[0] = curAtom.Y1;
    		sourceExprs[1] = curAtom.Y2;
    		Expr[] normExprs = normalize(ctxt, sourceExprs, smallerAtoms);
    		Atom normCurAtom = new Atom(curAtom.equality, normExprs[0], normExprs[1]);
    		boolean curAtomChanged = !normExprs[0].defEq(ctxt, curAtom.Y1) || !normExprs[1].defEq(ctxt, curAtom.Y2);

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
    	VarOrder theVarOrder = new VarOrder();
    	for(int i = 0; i < 100; ++i)
    	{
    		try
    		{	    
    			OrderMap theOrderMap = new OrderMap();
		    	Atom[] orientedPs = orient(ctxt, equations, theVarOrder, theOrderMap);
		    	Atom[] completePs = complete(ctxt, orientedPs, boundVars, theVarOrder, theOrderMap);
		    	Expr ne1 = orderedRewrite(ctxt, e1, completePs, boundVars);
		    	Expr ne2 = orderedRewrite(ctxt, e2, completePs, boundVars);
		    	return ne1.defEq(ctxt, ne2);
    		}
    		catch(UnorderableException ex)
    		{
    			handleError(ctxt, "Unable to order the variables in the supplied equations: " + 
    					getArrString(ctxt, equations));
    		}
    		catch(OrderingRestartRequiredException ex)
    		{
    			theVarOrder.clearArbitraryConstraints();
    		}
    	}
    	handleError(ctxt, "Unable to order the variables in the supplied equations: " + 
				getArrString(ctxt, equations));
    	return false;
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
	    //@SuppressWarnings("unused")
			int i = 0;
    	}
    	
	if (ctxt.getFlag("trust_hypjoins")) {
	    return new Atom(true, t1, t2);
	}

		Atom[] proofAtoms = getAtomArray(ctxt, Ps);
		normalize(ctxt, proofAtoms);

		Expr[] sourceExprs = new Expr[2];
		sourceExprs[0] = t1;
		sourceExprs[1] = t2;
		Expr[] normExprs = normalize(ctxt, sourceExprs, proofAtoms);
        
        Stack emptyContext = new Stack();
        if(equalModEquations(ctxt, normExprs[0], normExprs[1], proofAtoms, emptyContext))
        {
        	return new Atom(true, t1, t2);
        }
        
        handleError(ctxt,
      		    "Evaluation cannot join two terms" 
      		    +" in a hypjoin proof.\n\n"
      		    +(stucks[0] == null ? 
		      "1. Normal form of the first term: "+normExprs[0].toString(ctxt) :
		      "1. While evaluating the first term, the following term gets stuck: "+stucks[0].toString(ctxt))
      		    +(stucks[1] == null ? 
		      "\n\n2. Normal form of the second term: "+normExprs[1].toString(ctxt) :
		      "\n\n2. While evaluating the second term, the following term gets stuck: "+stucks[1].toString(ctxt)+"\n"));

	    //	    +"\n3. Normal form of equations:\n" + getArrString(ctxt, proofAtoms));
   
    
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
