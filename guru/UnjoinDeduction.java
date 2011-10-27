package guru;

import java.util.*;

/*
 * A heterogenous tree containing nodes of the following types:
 * - Introduction, which asserts the existence of a expression having a specified classifier
 * - Or, which introduces nondeterminism
 * - Contradiction, which asserts false
 * - Empty, which asserts true
 * 
 * UnjoinDeductions are produced by Expr.Unjoin, and have the property that
 * all of the assertions from some root-to-leaf path must hold if the some 
 * instantiation of the expression being unjoined can join with the target under 
 * the given context.
 */
public abstract class UnjoinDeduction {
	
	public static final int INTRO = 0;
	public static final int OR = 1;
	public static final int EMPTY = 2;
	public static final int CONTRADICTION = 3;
	
	// An UnjoinDeduction which asserts false
	public static final UnjoinDeduction contradiction = new UnjoinContradiction();
	
	// An UnjoinDeduction which asserts true
	public static final UnjoinDeduction empty = new UnjoinEmpty();
	
	// Returns an int identifying the type of this deduction node:
	// INTRO, OR, EMPTY, or CONTRADICTION
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
	
	// Backtrack through the given deduction, inserting a copy of 
	// each root-to-leaf path into the paths vector.
	static private void FlattenAux(
			UnjoinDeduction currDeduction, 
			Stack currPathDeduction, 
			Vector paths
	)
	{	
		switch (currDeduction.GetDeductionType())
		{
		case INTRO:
			UnjoinIntro intro = (UnjoinIntro)currDeduction;
			currPathDeduction.push(intro);
			FlattenAux(intro.rest, currPathDeduction, paths);
			currPathDeduction.pop();
			return;
		case OR:
			UnjoinOr or = (UnjoinOr)currDeduction;
			FlattenAux(or.d0, currPathDeduction, paths);
			FlattenAux(or.d1, currPathDeduction, paths);
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
	static public Vector Flatten(UnjoinDeduction deduction, Context ctxt)
	{
		Stack deductions = new Stack();
		Vector paths = new Vector();
		
		FlattenAux(deduction, deductions, paths);
		
		return paths;
	}
}
