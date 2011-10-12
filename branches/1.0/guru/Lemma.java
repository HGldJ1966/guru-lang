package guru;

import java.io.PrintStream;

/* 
 * A proof construct which allows allows an unnamed lemma to be proven
 * and referenced later; such referencing is done by putting the lemma mark 
 * token, ##, in positions where proofs of the unnamed lemma are expected.
 * 
 * A lemma abstract syntax node has the form "lemma p in b", where p and b are 
 * proofs. Let F be the classifier of p under context C. If b has classifeir T 
 * under context C,F, then the lemma expression has classifier T under context 
 * C.
 * 
 * As an example, suppose we have a proof div_le, which proves the
 * formula "Forall(a b: nat)(u: { b != Z} ). { (le (div a b) a) = tt }". 
 * We could write a proof that "Forall(a: nat). { (le (div a two) a) = tt }"
 * using the following code: 
 * 
 * Define div2_le : Forall(a: nat). { (le (div2 a) a) = tt } := 
 *   foralli(a:nat).
 *   lemma
 *     clash two Z
 *   in
 *   [div_le a two ##].
 * 
 * In the above code, div_le is instantiated using ## as its third argument.
 * Since div_le expects a proof of the formula "{ two != Z }" in that position,
 * [div_le a two ##] will only be considered well typed if an unnamed proof
 * of formula { two != Z } is in the context that [div_le a two ##] is classified
 * under. Such a formula does exist in the context due to our use of the lemma
 * construct; hence, our proof is well classified.
 * 
 * Lemma is implemented as a derived form. In source code, it appears as
 * "lemma p+ in b", where p+ is a sequence of one or more proofs p1 ... pn
 * and b is also a proof.
 * 
 * An occurrence of "lemma p1 ... pn in b" elaborates to the following syntax:
 * lemma p1 in (lemma p2 in (... (lemma pn in b)...))
 * 
 * This derived form allows us--with only one occurrence of the "lemma" keyword
 * and one occurrence of the "in" keyword--to establish a sequence of unnamed 
 * lemmas, where the proof of each additional lemma can reference all of the 
 * previously defined lemmas using lemma marks.  
*/
public class Lemma extends Expr {
	
	// Proof of an unnamed lemma, to be referenced via formula.
	final private Expr lemmaProof;
	
	// A proof which may include implicit references to the unnamed lemma.
	final private Expr body;
	
	public Lemma(Expr lemma, Expr body) {
	  super(LEMMA);
	  
	  assert(lemma != null);
	  assert(body != null);
	  
	  this.lemmaProof = lemma;
	  this.body = body;
	}
	
	//Override form Expr
	public Expr classify(Context ctxt) {
		assert(ctxt != null);
		
		Expr formula = lemmaProof.classify(ctxt);
		
		if (!formula.isFormula(ctxt))
		{
			handleError(ctxt,
					"Classifier for lemma is not a formula.\n" +
					"1. computed classifier: " + formula.toString(ctxt));
			
			return null;
		}
		
		if (ctxt.lemmaSet.hasLemma(formula))
		{
			handleError(ctxt,
					"Lemma formula already contained in context.\n" +
					"1. formula: " + formula.toString(ctxt));
			
			return null;
		}
		
		ctxt.lemmaSet.addLemma(formula);
		
		Expr bodyClassifier = body.classify(ctxt);
		
		ctxt.lemmaSet.removeLemma(formula);
		
		return bodyClassifier;
	}
	
	//Override form Expr
	protected void do_print(PrintStream w, Context ctxt) {
	  w.print("lemma ");
	  lemmaProof.print(w, ctxt);
	  w.print(" in ");
	  Expr formula = lemmaProof.classify(ctxt);
	  ctxt.lemmaSet.addLemma(formula);
	  body.print(w,ctxt);
	  ctxt.lemmaSet.removeLemma(formula);
	}

	//Override from Expr
	public int numOcc(Expr e) {
		//Lemmas are specificational; hence, this will not get called.
		assert(false);
		return 0;
	}

	//Override from Expr
	public Expr subst(Expr e, Expr x) {
		//Lemmas are specificational; hence, this will not get called.
		return new Lemma(lemmaProof.subst(e,x), body.subst(e,x));
	}

	public Expr dropAnnos(Context ctxt) {
		return body.dropAnnos(ctxt);
	}
	
	// overridden from Expr.
	//
	// A lemma construct is considered to terminate if the lemmaProof
	// and the body both terminate. 
	//
	// The lemmaProof is required to terminate because we assume that
	// this lemma is referenced by at least one lemma mark inside
	// the body--an unreferenced lemma is pointless. Rather than
	// redundantly checking the termination of each lemmaMark, we 
	// handle that task only once in a call to this method.
	public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars)
	{
		lemmaProof.checkTermination(ctxt, IH, arg, vars);
		body.checkTermination(ctxt, IH, arg, vars);
	}
}
