package guru;

import java.io.PrintStream;
import java.util.List;
import java.util.Stack;
import java.util.Vector;

import guru.Atom;
import guru.Context;
import guru.Exists;
import guru.Existse;
import guru.Expr;
import guru.Foralli;
import guru.UnjoinContext;
import guru.UnjoinDeduction;
import guru.UnjoinIntro;
import guru.Var;


/*
 * A proof construct, taking a proof of a formula of the form { t = v }, 
 * which allows us to automatically derive a contradiction by determining
 * that no normalization path from t to v exists given that the formulas
 * in the unnamed lemma set are true. 
 *
 * UnjoinContra appears in source as "unjoin u contra F", where u is a proof 
 * whose classifier has the form { t = v } and F is the formula we wish our
 * unjoin construct to classify as.  
 *
 * Here is an example of a usage of UnjoinContra.
 * 
 * Define lt_Z2 : Forall(a:nat).{ (lt a Z) = ff } :=
 *  foralli(a : nat).
 *  case (lt a Z) by v ign with
 *  | ff =>
 *    v
 *  | tt =>
 *    unjoin v contra { (lt a Z) = ff }
 *  end.
 *  
 * UnjoinContra's implementation is very similar to Unjoin's. See 
 * Unjoin.java for a more detailed explanation of how unjoining works.
 */
public class UnjoinContra extends Expr {

	// An expression which proves the scrutinee atom.
	public final Expr scrutineeProof;
	
	// The formula, written by the programmer, which the contradiction
	// is being used to prove.
	public final Expr conclusion;
	
	public UnjoinContra(Expr scrutineeProof, Expr conclusion)
	{
		super(UNJOIN_CONTRA);
		
		assert(scrutineeProof != null);
		assert(conclusion != null);
		
		this.scrutineeProof = scrutineeProof;
		this.conclusion = conclusion;
	}
	
	private void DumpUnjoinPaths(List unjoinPaths, Context ctxt) {
		for(int i = 0; i < unjoinPaths.size(); ++i) {
			String pathString = "";
			Stack path = (Stack)unjoinPaths.get(i);
			for(int j = 0; j < path.size(); ++j)
			{
				UnjoinIntro u = (UnjoinIntro)path.get(j);
				
				pathString += "(" + u.introVar.toString(ctxt) + " : " + 
					u.introVarType.toString(ctxt) + ")";
			}
			
			System.out.println(pathString);
		}
	}
	
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
	private Expr instantiate(Context ctxt, Expr lhs)
	{	
		if (lhs.construct != TERM_APP)
			return lhs;
		
		TermApp ta = (TermApp)lhs;

		while (true) {
	    	//The head, normalized to a function term
	    	Expr h = ta.head.evalStep(ctxt);
	    	//The constant or variable initially used for the head.
	    	Expr pre = ta.head;
	    	
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
					"simplifies to a term app whose head is not a function.\n" +
					"1. lhs:" + lhs.toString(ctxt) + "\n" +
					"2. simplified lhs: " + h.toString(ctxt) + "\n"
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
			
			//TODO: substitute lets and abbrevs here?
			
			if (fullInstantiation.construct != TERM_APP)
				return fullInstantiation;
			
			ta = (TermApp)fullInstantiation;
		}
	}
	
	public Expr classify(Context ctxt) {
		Expr cScrutProof = scrutineeProof.classify(ctxt);
		
		if (cScrutProof.construct != ATOM) {
			handleError(ctxt,
					"Attempted to unjoin an expression not classified as an equation" +
					" or disequation.\n" + 
					"1. classifier of expression: " + cScrutProof.toString(ctxt)
			);
			
			System.exit(0);
		}
		
		Atom scrutinee = (Atom)cScrutProof;
		
		if (!scrutinee.Y2.isI(ctxt)) {
			handleError(ctxt,
					"Right hand side of unjoin scrutinee classifier is not" +
					"a value.\n" + 
					"1. scrutinee classifier: " + cScrutProof.toString(ctxt)
			);
			
			System.exit(0);
		}
		
		Expr instantiated = instantiate(ctxt, scrutinee.Y1);
		instantiated = ctxt.lemmaSet.instantiate(instantiated);
		
		UnjoinDeduction deduction = instantiated.Unjoin(
			scrutinee.Y2,
			0,
			ctxt,
			scrutinee.equality
		);
    	
		List unjoinPaths = UnjoinDeduction.Flatten(deduction, ctxt);
		
		if (unjoinPaths.size() != 0) {
			DumpUnjoinPaths(unjoinPaths, ctxt);
			handleError(ctxt, 
					"Unjoin did not derive a contradiction. Unjoin has deduced\n" +
					"the execution paths listed above.");
		}
		
		return conclusion;
	}
	
    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars) { 
    	conclusion.checkTermination(ctxt,IH,arg,vars);
	}
	
	protected void do_print(PrintStream w, Context ctxt) {
		w.print("unjoin ");
		scrutineeProof.print(w, ctxt);
		w.print(" contra ");
		conclusion.print(w, ctxt);
	}

	// Expr override
	public int numOcc(Expr e) {
		return scrutineeProof.numOcc(e) + conclusion.numOcc(e);
	}

	// Expr override
	public Expr subst(Expr e, Expr x) {
		return new UnjoinContra(
			scrutineeProof.subst(e, x), 
			conclusion.subst(e, x)
		);
	}

	// Expr override
	public Expr dropAnnos(Context ctxt) {
		return new Bang();
	}

}
