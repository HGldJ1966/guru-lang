package guru;

import java.io.PrintStream;
import java.util.*;


/*
 * A proof construct, taking a proof of a formula of the form { t = v }, 
 * which allows us to decompose the proof into cases for all normalization 
 * paths from t to v. Unjoin uses the unnamed lemma set (see Lemma, LemmaSet) 
 * in order to constrain the list of paths which must be handled.
 *
 * Decomposing a proof using unjoin relieves us from the tedious task of deriving 
 * contradictions for impossible cases.
 *
 * Unjoin appears in source as "unjoin u with | p1 | p2 ... | pn end",
 * where u is a proof whose classifier has the form { t = v } and p1, ... pn
 * are forall proofs.  
 *
 * To use unjoin, first add the following syntax at the position in which
 * you want to use unjoin:
 * 
 * unjoin u with
 * end
 *
 * Then classify your proof. You should see a classification error listing
 * all cases which must be handled inside the unjoin. Copy these cases
 * into your unjoin (between with and end) and then handle them.
 *
 *
 * As an example, consider the following proof.
 *
 * Define eqnatEq : Forall(n m:nat)(u:{(eqnat n m) = tt}). { n = m } :=
 * induction(n:nat) return
 *   Forall(m:nat)(u:{(eqnat n m) = tt}). { n = m } 
 * with
 * | Z =>
 *   foralli(m: nat)(u : { (eqnat n m) = tt }).
 *   lemma n_eq in
 *   unjoin u with
 *   | foralli(p0 : { m = Z }).
 *     trans : { n = Z } n_eq
 *           : { Z = m } symm p0
 *   end 
 * | S n' =>
 *   foralli(m: nat)(u : { (eqnat n m) = tt }).
 *   lemma n_eq in
 *   | foralli(m' : nat)(p3 : { m = (S m') })(u : { (eqnat n' m') = tt }).            
 *     hypjoin n m by
 *       : { n' = m' } [n_IH n' m' u]
 *       : { m = (S m') } p3
 *       : { n = (S n') } n_eq
 *     end
 *   end
 * end.
 * 
 * The above proof uses unjoin twice. In both uses, it operates on a proof
 * of the formula { (eqnat n m) = tt }. The first use deduces that, because
 * { n = Z } and { (eqnat n m) = tt }, we must have { m = Z }. The second
 * use deduces facts regarding the situation where { n = (S n') }. In both 
 * uses, unjoin removes the need for us to case split on m, which greatly
 * simplifies our proof.
 * 
 * It's important to know that unjoin deductions are made by processing
 * the syntax for the term being normalized, (eqnat n m) in this case.
 * Referring to the source code for eqnat should help us understand why
 * unjoin made the deductions that it did.
 * 
 * Define eqnat : Fun(^ #owned n m:nat).bool :=
 * fun eqnat(^ #owned n m:nat):bool.
 *   match ! n with
 *     Z => match ! m with
 *            Z => tt
 *          | S m' => ff
 *          end
 *  | S n' => match ! m with
 *              Z => ff
 *            | S m' => (eqnat n' m')
 *            end
 *  end
 * 
 * The first use of unjoin is classified with the formula { n = Z } in the 
 * lemma set. Hence, any normalization path for (eqnat n m) must evaluate
 * to the first case of the match on n. Inside this case, m is scrutinized.
 * Since we have no formulas regarding m in our lemma set, either case
 * could be taken. However, the case where m = S m' evaluates to ff, which
 * does not match our target value tt. This leads unjoin to deduce that
 * the only possible value for m is Z.
 * 
 * Unjoin cannot be used under contradictory contexts. A special construct
 * is needed for this, which is implemented in UnjoinContra.java. 
 * 
 */
public class Unjoin extends Expr {

	// An expression which proves the scrutinee atom.
	public final Expr scrutineeProof;
	
	// A list containing forall proofs which quantify over the
	// deductions made in each unjoin path.
	public final Vector paths;
	
	public Unjoin(Expr scrutineeProof, Vector paths)
	{
		super(UNJOIN);
		
		assert(scrutineeProof != null);
		assert(paths != null);
		
		this.scrutineeProof = scrutineeProof;
		this.paths = paths;
	}
	
	// Expr override
	protected void do_print(PrintStream w, Context ctxt) {
		w.print("unjoin ");
		scrutineeProof.print(w, ctxt);
		w.print(" with\n");
		for (int i = 0; i < paths.size(); ++i) {
			Foralli path = (Foralli)paths.get(i);
			path.do_print(w, ctxt);
		}
		w.print("end");
	}
	
	public static boolean placeHolder(Expr e, Context ctxt)
	{
		if (e.construct == VAR)
			return true;
		
		if (e.construct == CONST && e.evalStep(ctxt) != e)
			return true;
		
		return false;
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
	
	// Checks that each parsed path (a forall proof) can eliminate the 
	// corresponding unjoined path (and exists proof), and that every such 
	// elimination proves the same formula. Guru terminates with an error 
	// if any of these checks fail.
	// 
	// Returns the formula which the eliminations prove. This formula
	// is the classifier for the unjoin construct.
	private Expr classifyPaths(Vector unjoinedPaths, Context ctxt)
	{
		Expr [] pathClassifiers = new Expr[paths.size()];
		for (int i = 0; i < paths.size(); ++i)
		{
			Foralli parsedPath = (Foralli)paths.get(i);
			Stack unjoinedPath = (Stack)unjoinedPaths.get(i);
			
			//convert unjoined path into a exists
			Var[] unjoinVars = new Var[unjoinedPath.size()-1];
			Expr[] unjoinTypes = new Expr[unjoinedPath.size()-1];
			for(int j = 0; j < unjoinedPath.size()-1; ++j)
			{
				unjoinVars[j] = ((UnjoinIntro)unjoinedPath.get(j)).introVar;
				unjoinTypes[j] = ((UnjoinIntro)unjoinedPath.get(j)).introVarType;
			}
			
			Expr body = ((UnjoinIntro)unjoinedPath.lastElement()).introVarType;
			assert(body.isFormula(ctxt));
			Exists unjoinedExists = new Exists(unjoinVars,unjoinTypes,body);
			Var existsVar = new Var("path " + Integer.toString(i));
			ctxt.setClassifier(existsVar, unjoinedExists);
			
			Existse eliminator = new Existse(existsVar, parsedPath);
			eliminator.pos = parsedPath.pos;
			pathClassifiers[i] = eliminator.classify(ctxt);
		}
		
		for(int i = 1; i < pathClassifiers.length; ++i) {
			if (!pathClassifiers[i].defEq(ctxt, pathClassifiers[0])) {
				handleError(ctxt, "unjoin path classifiers do not match");
			}
		}
		
		return pathClassifiers[0];
	}
	
	//Expr override
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
		
		UnjoinDeduction deduction = instantiated.Unjoin(
			scrutinee.Y2,
			0,
			ctxt,
			scrutinee.equality
		);
		
		Vector unjoinPaths = UnjoinDeduction.Flatten(deduction, ctxt);
		
		if (unjoinPaths.size() != paths.size()) {
			//TODO: spit out error message, remove assert
			DumpUnjoinPaths(unjoinPaths, ctxt);
			handleError(ctxt, "Unjoin paths do not match the computed paths" +
					" listed above.");
		}

		if (unjoinPaths.size() == 0)
			handleError(ctxt, "Unjoin has deduced a contradiction.");
		
		return classifyPaths(unjoinPaths, ctxt);
	}
	
    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars) { 
    	for (int i = 0; i < paths.size(); ++i)
    		((Foralli)paths.get(i)).checkTermination(ctxt,IH,arg,vars);
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
	public int numOcc(Expr e) {
		int ret = 0;
		ret += scrutineeProof.numOcc(e);
		for (int i = 0; i < paths.size(); ++i)
			ret += ((Foralli)paths.get(i)).numOcc(e);
		return ret;
	}

	// Expr override
	public Expr subst(Expr e, Expr x) {
		Vector retPaths = new Vector(paths.size());
		
		for (int i = 0; i < paths.size(); ++i)
			retPaths.set(i, ((Foralli)paths.get(i)).subst(e, x));
		
		return new Unjoin(scrutineeProof.subst(e,x), retPaths);
	}

	// Expr override
	public Expr dropAnnos(Context ctxt) {
		return new Bang();
	}

}
