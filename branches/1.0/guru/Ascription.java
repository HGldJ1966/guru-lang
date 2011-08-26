package guru;

import java.io.PrintStream;

/* 
 * Ascriptions appear in source as ": C e", where C is a classifier and
 * e is an expression. ": C e" is classified as C under context G iff
 * e is classified as C under G. If e is not classified as C under
 * context G, then ": C e" is not well classified under G.
 * 
 * An ascription allows the writer of guru code to display the classifier of 
 * a certain expression in source code; this provides the reader of said code
 * a convenient summary of the ascribed expression.
 * 
 * For example, in a transitivity proof, you could ascribe each of the atoms 
 * involved. This allows the reader (or writer) of the proof to consider
 * (or state) the chain of transitivity before examining why each atom 
 * in the chain holds. In general, ascriptions allow guru programmers to
 * write proofs in a more top-down manner, separating the basic outline 
 * of the proof from the details.
 * 
 * An ascription can also be used to refer to a subproof by formula rather than
 * by programmer-given name. Instead of creating an abbreviation for a subproof, 
 * one can insert the subproof into the context using the lemma construct. 
 * The subproof can then be referred to inside the lemma body using an 
 * ascripted lemma mark.
 */
public class Ascription extends Expr {

	// The classifier being ascribed to the target.
	final Expr classifier;
	
	// The target of the ascription.
	final Expr target;
	
	public Ascription(Expr classifier, Expr target)
	{
		super(ASCRIPTION);
		
		assert(target != null);
		assert(classifier != null);
		assert(isFormula(classifier.construct) || isTypeOrKind(classifier.construct));
		
		this.target = target;
		this.classifier = classifier;
	}
	
	// overridden from Expr
	public Expr classify(Context ctxt)
	{
		if (target.construct == LEMMA_MARK)
		{
			LemmaMark lm = (LemmaMark)target;
			lm.formula = classifier;
		}
		
		Expr computed = target.classify(ctxt);
		
		if (!computed.defEq(ctxt,classifier))
		{
			handleError(ctxt,
					"Ascription classifier does not match the computed classifer" +
					" of the ascription target.\n" +
					"Computed Classifier: " + computed.toString(ctxt));
			
			return null;
		}
		
		return classifier;
	}
	
	// overridden from Expr
	protected void do_print(PrintStream w, Context ctxt) {
		w.print(": ");
		classifier.do_print(w,ctxt);
		w.print(" ");
		target.do_print(w,ctxt);
	}

	// overridden from Expr
	public int numOcc(Expr e) {
		
		return target.numOcc(e) + classifier.numOcc(e);
	}

	// overridden from Expr
	public Expr subst(Expr e, Expr x) {
		
		return new Ascription(target.subst(e,x), classifier.subst(e,x));
	}

	// overridden from Expr
	public Expr dropAnnos(Context ctxt) {
		return target.dropAnnos(ctxt);
	}
	
	public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars)
	{
		target.checkTermination(ctxt, IH, arg, vars);
	}
}
