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
	//The context that the unjoin proof is being classified under.
	private final Context baseContext;
	
	// A set of lemmas that may be used for rewriting and simplification.
	public final LemmaSet lemmaSet;
	
	// A set of the names of all variables encountered so far. 
	private final HashSet varNames;
	
	// Whenever we expand a constant that contains a recursive function as
	// an immediate subterm, we map (in funcVarToConst) the variable representing 
	// the recursive function to the constant. This allows us to refer to the 
	// constant rather than the variable in our deduced formulas.
	private final HashMap funcVarToConst;
	
	// The set of all variables that correspond to recursive function calls.
	// We keep track of these so that we don't expand them while unjoining.
	// TODO: can we prove things about a function inside its own body?
	private final HashSet recFuncVars;

	public UnjoinContext(Context baseContext) {
		this.baseContext = baseContext;
		lemmaSet = baseContext.lemmaSet.copy();
		varNames = new HashSet();
		funcVarToConst = new HashMap();
		recFuncVars = new HashSet();
	}
	
	public void setFuncConst(Var v, Const c) {
		assert(!funcVarToConst.containsKey(v));
		assert(!funcVarToConst.containsValue(c));
		funcVarToConst.put(v, c);
	}
	
	public Const getFuncConst(Var v)
	{
		return (Const)funcVarToConst.get(v);
	}
	
	public void removeFuncConst(Var v) {
		assert(funcVarToConst.containsKey(v));
		funcVarToConst.remove(v);
	}
	
	public void addRecFuncVar(Var v) {
		assert(!recFuncVars.contains(v));
		recFuncVars.add(v);
	}
	
	public boolean hasRecFuncVar(Var v)
	{
		return recFuncVars.contains(v);
	}
	
	public void removeRecFuncVar(Var v) {
		assert(recFuncVars.contains(v));
		recFuncVars.remove(v);
	}
	
	// Generates a name for a variable introduction. If the suggested name
	// has not already been used on this execution path, we use it. Otherwise,
	// we add primes to the end of the suggestion until no currently-introduced
	// variable has a matching name.
	public String genName(String suggestion) {
		assert(suggestion != null);
		
		String currentCandidate = suggestion;
		boolean alreadyUsed = varNames.contains(currentCandidate);
		alreadyUsed |= (baseContext.lookup(currentCandidate) != null); 
		
		while (alreadyUsed) {
			currentCandidate += "'";
			alreadyUsed = varNames.contains(currentCandidate);
			alreadyUsed |= (baseContext.lookup(currentCandidate) != null); 
		}
		
		varNames.add(currentCandidate);
		return currentCandidate;
	}
	
	// Remove a name for the varNames set
	public void removeName(String name) {
		assert(varNames.contains(name));
		varNames.remove(name);
	}
}
