package guru;

import java.util.HashSet;
import java.util.HashMap;

//TODO: comment all methods

// When we unjoin a term, we need to have information about the execution
// path that lead to the term. For example, we need to keep track of the names
// of variables introduced so that we don't have any duplicates. We also need
// to keep track of equational facts that we have discovered so that we
// can use them to prevent unnecessary nondeterminism and getting stuck.
public class UnjoinContext {
	
	// Counts the number of proof variables in the current unjoin path.
	// Whenever we introduce a new proof variable, we append the current value
	// of proofCounter onto the name of the new variable in order to make it 
	// unique.
	public int proofCounter;
	
	public final LemmaSet lemmaSet;
	
	//Whenever we enter recursively defined functions, testing for plausibility,
	//we need to make sure we don't traverse recusive function calls. recVars
	//is equal to the current recursive variable, if any, so we can use 
	//it to check for this.
	public Var recVar;
	
	public UnjoinContext(LemmaSet baseLemmaSet)
	{
		this.proofCounter = 0;
		this.lemmaSet = baseLemmaSet.copy();
		this.recVar = null;
	}
}
