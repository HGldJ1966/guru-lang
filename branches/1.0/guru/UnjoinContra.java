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
public class UnjoinContra extends UnjoinBase {
	
	// The formula, written by the programmer, which the contradiction
	// is being used to prove.
	public final Expr conclusion;
	
	public UnjoinContra(Expr scrutineeProof, Expr conclusion)
	{
		super(UNJOIN_CONTRA, scrutineeProof);
		
		assert(scrutineeProof != null);
		assert(conclusion != null);
		
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
		
		Expr instantiated = instantiate2(ctxt, scrutinee.Y1);
		instantiated = ctxt.lemmaSet.rewrite(instantiated);
		UnjoinContext uctxt = new UnjoinContext(ctxt.lemmaSet);
		
		UnjoinDeduction deduction = instantiated.Unjoin(
			scrutinee.Y2,
			uctxt,
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
