package guru;

import java.io.PrintStream;

/* A syntactic construct which can be used in proof argument positions in order
 * to reference proofs of formulas which have been established earlier using
 * the lemma construct (see Lemma.java).
 *   
 * When an application is typechecked, an occurrence of ## in an argument 
 * position will be considered well-typed iff the formal parameter for that
 * position is a proof of some formula that is currently in the context as 
 * an unnamed lemma.
 * 
 * Occurrences of ## outside of applications are illegal.
*/
public class LemmaMark extends Expr {

	// The formula type that this lemma mark must have in order to typecheck, 
	// inherited from the application that this lemma mark occurs as an argument
	// in.
	public Expr formula;
	
	public LemmaMark()
	{
		super(LEMMA_MARK);
	}

	//Overridden from Expr
	protected void do_print(PrintStream w, Context ctxt) {
		w.print("lemma mark");
	}

	//Overridden from Expr
    public Expr classify(Context ctxt) {
    	assert(ctxt != null);
    	
    	if (formula == null)
    	{
    		handleError(pos,
    				"Lemma mark used in a position that is not a proof argument.");
    		
    		return null;
    	}
    	else if (!formula.isFormula(ctxt))
    	{	
    		handleError(pos,
    				"Lemma mark used in a position whose expected classifier is" +
    				" not a formula.\n");
    		
    		return null;
    	}
    	else if (!ctxt.lemmaSet.hasLemma(formula))
    	{
    		handleError(pos,
    			    "Lemma mark used without the expected lemma in context.\n"
    			    +"Missing lemma: " + formula.toString(ctxt));    	
    		
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
		//Lemma marks are specificational, so this shouldn't get called
		//Specificational constructs shouldn't have to implement this,
		//and they shouldn't have to implement the above two methods either.
		assert(false);
		return null;
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
