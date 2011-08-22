package guru;

import java.util.ArrayList;
import java.util.ListIterator;

/*
 * A set of all unnamed formulas which have been established in the current
 * context. Unnamed formulas can be used as premises for proof instantiation
 * by using the ## token. They are introduced to the context using the lemma
 * construct (see Lemma.java). 
 *
 * NOTE: The java API's set classes are not suitable for defining a lemma set
 * due to their usage of the equals method to determine uniqueness. The equals
 * method is not parameterized by context whereas our notion of definitional equality is. 
*/
public class LemmaSet {

	// The context used to decide definitional equality
	final private Context ctxt;
	
	// A set of definitionally unique formulas currently contained in this lemma set.
	final private ArrayList formulas; 
	
	public LemmaSet(Context ctxt)
	{
		assert(ctxt != null);
		
		this.ctxt = ctxt;
		this.formulas = new ArrayList();
	}
	
	// Adds a lemma to the set. This lemma must be definitionally unequal
	// to each lemma currently in the set. (Use the HasLemma method to 
	// determine whether or not an equivalent lemma is already in the set.) 
	public void addLemma(Expr newLemma)
	{
		assert(newLemma != null);
		assert(newLemma.isFormula(ctxt));
		assert(!hasLemma(newLemma));
		
		formulas.add(newLemma);
	}
	
	// Removes a lemma from the set.
	public void removeLemma(Expr toRemove)
	{
		assert(toRemove != null);
		assert(toRemove.isFormula(ctxt));
		assert(hasLemma(toRemove));
		
		formulas.remove(toRemove);
	}
	
	// Returns true iff the given lemma is contained in this set.
	public boolean hasLemma(Expr lemma)
	{
		assert(lemma.isFormula(ctxt));
		assert(lemma != null);
		
		ListIterator i = formulas.listIterator();
		while(i.hasNext())
		{
			Expr curr = (Expr)i.next();
			
			if (curr.defEq(ctxt, lemma))
				return true;
		}
		return false;
	}
}
