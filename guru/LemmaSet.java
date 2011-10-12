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
	
	// The set of definitionally unique formulas currently contained in this lemma set.
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
		assert(newLemma.isFormula(ctxt));
		assert(!hasLemma(newLemma));
		
		formulas.add(newLemma);
	}
	
	// Removes a lemma from the set.
	public void removeLemma(Expr toRemove)
	{
		assert(toRemove.isFormula(ctxt));
		assert(hasLemma(toRemove));
		
		formulas.remove(toRemove);
	}
	
	// Returns true iff the given lemma is contained in this set.
	public boolean hasLemma(Expr lemma)
	{
		assert(lemma.isFormula(ctxt));
		
		ListIterator i = formulas.listIterator();
		while(i.hasNext())
		{
			Expr curr = (Expr)i.next();
			
			if (curr.defEq(ctxt, lemma))
				return true;
		}
		return false;
	}
	
	// Returns a new lemma set containing exactly the same set of formulas as
	// this one.
	public LemmaSet copy()
	{
		LemmaSet ret = new LemmaSet(ctxt);
		
		ListIterator i = formulas.listIterator();
		while(i.hasNext())
			ret.addLemma((Expr)i.next());
		
		return ret;
	}
	
	public Expr simplify(Expr e)
	{
		Expr e_ = null;
		
		while (e_ != e)
		{
			e_ = e;
			
			if (e.construct == Expr.MATCH)
			{
				Match m = (Match)e;
				Expr mt_ = simplify(m.t);
				if (mt_ != m.t) {
					e = new Match(
						simplify(m.t),
						m.x1,
						m.x2,
						m.T,
						m.C,
						m.consume_scrut
					);
				}
			}		
			
			e = e.evalStep(ctxt);
			e = rewrite(e);
		}
		
		return e;
	}
	
	private Expr rewrite(Expr e)
	{
		if (e.construct != Expr.VAR)
			return e;
		
		Var v = (Var)e;
		
		ListIterator i = formulas.listIterator();
		while(i.hasNext()) {
			Expr curr = (Expr)i.next();
			
			if (curr.construct != Expr.ATOM)
				continue;
			
			Atom a = (Atom)curr;
			
			if (a.equality == false)
				continue;
			
			if (a.Y1 == v) {
				if (a.Y2.construct == Expr.TERM_APP)
				{	
					TermApp ta = (TermApp)a.Y2;
					
					if (ta.head.construct == Expr.CONST && ctxt.isTermCtor((Const)ta.head))
						return ta;
				}
				else if(a.Y2.construct == Expr.CONST)
				{
					return a.Y2;
				}
			}
			
			if (a.Y2 == v && a.Y1.construct == Expr.TERM_APP) {
				if (a.Y1.construct == Expr.TERM_APP)
				{	
					TermApp ta = (TermApp)a.Y1;
					
					if (ta.head.construct == Expr.CONST && ctxt.isTermCtor((Const)ta.head))
						return ta;
				}
				else if(a.Y1.construct == Expr.CONST)
				{
					return a.Y1;
				}
			}
		}
		
		return v;
	}
}
