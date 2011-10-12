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
	
	static public UnjoinDeduction Append(
			UnjoinDeduction appendThis,
			UnjoinDeduction ontoThis
	)
	{
		switch (ontoThis.GetDeductionType())
		{
		case INTRO:
			return Append(appendThis, ((UnjoinIntro)ontoThis).rest);
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
