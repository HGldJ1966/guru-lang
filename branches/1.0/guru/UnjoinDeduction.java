package guru;

import java.util.*;

public abstract class UnjoinDeduction {
	
	public static final int INTRO = 0;
	public static final int OR = 1;
	public static final int EMPTY = 2;
	public static final int CONTRADICTION = 3;
	
	public static final UnjoinDeduction contradiction = new UnjoinContradiction();
	public static final UnjoinDeduction empty = new UnjoinEmpty();
	
	abstract public int GetDeductionType();
	
	static public UnjoinDeduction Simplify(UnjoinDeduction target)
	{
		switch (target.GetDeductionType())
		{
		case INTRO:
			UnjoinIntro intro = (UnjoinIntro)target;
			UnjoinDeduction rest = Simplify(intro.rest);
			if (rest == contradiction)
				return contradiction;
			else
				return new UnjoinIntro(
					intro.introVar, 
					intro.introVarType,
					rest
				);
		case OR:
			UnjoinOr or = (UnjoinOr)target;
			if (or.d0 == contradiction && or.d1 == contradiction)
				return contradiction;
			else if (or.d0 == contradiction)
				return or.d1;
			else if (or.d1 == contradiction)
				return or.d0;
			else
				return or;
		case CONTRADICTION:
			return contradiction;
		case EMPTY:
			return empty;
		}
		
		assert(false);
		return null;
	}
	
	static public UnjoinDeduction FancyAppend(
			UnjoinDeduction baseDeduction,
			Expr startTerm,
			Expr target,
			UnjoinContext uCtxt,
			Context baseCtxt,
			boolean eq
	)
	{
		switch (baseDeduction.GetDeductionType())
		{
		case INTRO:
			UnjoinIntro intro = (UnjoinIntro)baseDeduction;
			
			//okay... basically, I need to collapse contradictory
			//paths, as I was originally planning to do, so that
			//I can add everything to the context here.
			if (intro.introVarType.construct == Expr.ATOM)
				uCtxt.lemmaSet.addLemma(intro.introVarType);
			else if (intro.introVarType.isTypeOrKind(baseCtxt))
				baseCtxt.setClassifier(intro.introVar, intro.introVarType);
			
			UnjoinDeduction ret = new UnjoinIntro(
				intro.introVar,
				intro.introVarType,
				FancyAppend(
					intro.rest,
					startTerm,
					target,
					uCtxt,
					baseCtxt,
					eq
				)
			);
			
			if (intro.introVarType.construct == Expr.ATOM)
				uCtxt.lemmaSet.removeLemma(intro.introVarType);
			
			return ret;
		case OR:
			UnjoinOr or = (UnjoinOr)baseDeduction;
			
			UnjoinDeduction d0 = FancyAppend(
				or.d0,
				startTerm,
				target,
				uCtxt,
				baseCtxt,
				eq
			);
			
			UnjoinDeduction d1 = FancyAppend(
				or.d1,
				startTerm,
				target,
				uCtxt,
				baseCtxt,
				eq
			);	
			
			return new UnjoinOr(d0, d1);
		case CONTRADICTION:
			return contradiction;
		case EMPTY:
			return startTerm.Unjoin(target, uCtxt, baseCtxt, eq);
		}
		
		assert(false);
		return null;	
	}
	
	static public UnjoinDeduction Append(
			UnjoinDeduction appendThis,
			UnjoinDeduction ontoThis
	)
	{
		switch (ontoThis.GetDeductionType())
		{
		case INTRO:
			UnjoinIntro intro = (UnjoinIntro)ontoThis;
			return new UnjoinIntro(
					intro.introVar,
					intro.introVarType,
					Append(appendThis, ((UnjoinIntro)ontoThis).rest)
			);
		case OR:
			UnjoinOr or = (UnjoinOr)ontoThis;
			return new UnjoinOr(Append(appendThis, or.d0), Append(appendThis, or.d1));
		case CONTRADICTION:
			return contradiction;
		case EMPTY:
			return appendThis;
		}
		
		assert(false);
		return null;
	}
	
	static private void FlattenDfs(
			UnjoinDeduction currDeduction, 
			Stack currPathDeduction, 
			List paths
	)
	{	
		switch (currDeduction.GetDeductionType())
		{
		case INTRO:
			UnjoinIntro intro = (UnjoinIntro)currDeduction;
			currPathDeduction.push(intro);
			FlattenDfs(intro.rest, currPathDeduction, paths);
			currPathDeduction.pop();
			return;
		case OR:
			UnjoinOr or = (UnjoinOr)currDeduction;
			FlattenDfs(or.d0, currPathDeduction, paths);
			FlattenDfs(or.d1, currPathDeduction, paths);
			return;
		case CONTRADICTION:
			return;
		case EMPTY:
			paths.add(currPathDeduction.clone());
			return;
		}
	}
	
	// Returns a vector containing, for each evaluation path, an array of 
	// UnjoinIntro values which describe variables deduced to exist in the case 
	// of an execution of that path.
	static public List Flatten(UnjoinDeduction deduction, Context ctxt)
	{
		Stack deductions = new Stack();
		List paths = new Vector();
		
		//Get a list existentially quantified variables for each eval path
		FlattenDfs(deduction, deductions, paths);
		
		return paths;
	}
}
