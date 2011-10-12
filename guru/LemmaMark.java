package guru;

import java.io.PrintStream;

/* A construct, appearing in source as "##", which can be used to reference 
 * proofs of unnamed formulas that are contained in the current context's 
 * lemma set. (See LemmaSet.java.)
 *   
 * Before ## is classified, it inherits an expected formula from its parent
 * in the syntax tree. This is only possible if the lemma mark's parent
 * determines the classifier of the expression which must appear in the position
 * that the lemma mark occupies; this is the case when the mark's parent expression
 * is either an ascription or an application.
 * 
 * For example, in the expression
 * ": { (S (S n')) != Z } ##"
 * the lemma mark inherits the classifer { (S (S n')) != Z } from its 
 * parent node, which is an ascription.
 * 
 * In the expression
 * "[lt_implies_le b' a' ##]"
 * the lemma mark inherits a classifier from the application.
 * 
 * If the lemma mark's inherited classifer is a formula contained in the classifying 
 * context's lemma set, the lemma mark's classifier is its inherited classifier. 
 * Otherwise, the lemma mark is not considered well typed.
*/
public class LemmaMark extends Expr {

	// The formula type that this lemma mark must have in order to classify, 
	// inherited from the expression that this lemma mark is a direct subexpression 
	// of.
	public Expr formula;
	
	public LemmaMark()
	{
		super(LEMMA_MARK);
	}

	//Overridden from Expr
	protected void do_print(PrintStream w, Context ctxt) {
		w.print("##");
	}

	//Overridden from Expr
    public Expr classify(Context ctxt) {
    	assert(ctxt != null);
    	
    	if (formula == null)
    	{
    		handleError(pos,
    				"Lemma mark used in an illegal position.\n" +
    				"Unascribed lemma marks can only be used as proof arguments.\n");
    		
    		return null;
    	}
    	else if (!formula.isFormula(ctxt))
    	{	
    		handleError(pos,
    				"Lemma mark used in a position whose expected classifier is" +
    				" not a formula.\n" +
    				"1. expected classifier: " + formula.toString(ctxt));
    		
    		return null;
    	}
    	else if (!ctxt.lemmaSet.hasLemma(formula))
    	{
    		handleError(pos,
    			    "Lemma mark used without the expected lemma in context.\n"
    			    +"1. expected lemma: " + formula.toString(ctxt));    	
    		
    		return null;
    	}
    	else
    	{
    		return formula;
    	}
    }
    
	//Overridden from Expr
	public int numOcc(Expr e) {
		return (this == e) ? 1 : 0;
	}

	//Overridden from Expr
	public Expr subst(Expr e, Expr x) {
		return (this == x) ? e : this;
	}

	public Expr dropAnnos(Context ctxt) {
		return this;
	}
	
	// Overridden from Expr.
	//
	// It is assumed that the termination of the lemma proof has already been 
	// checked for in  lemma.checkTermination; this means that we don't have to 
	// do anything in this method. 
	public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars)
	{
	}
}
