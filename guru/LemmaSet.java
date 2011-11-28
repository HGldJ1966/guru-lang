package guru;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.ListIterator;

/**
 * A set of all unnamed formulas which have been established in the current
 * context. Unnamed formulas can be used as premises for proof instantiation by
 * using the ## token. They are introduced to the context using the lemma
 * construct (see Lemma.java).
 * 
 * NOTE: The java API's set classes are not suitable for defining a lemma set
 * due to their usage of the equals method to determine uniqueness. The equals
 * method is not parameterized by context whereas our notion of definitional
 * equality is.
 */
public class LemmaSet {

	/** The context used to decide definitional equality */
	final private Context ctxt;

	/**
	 * The set of definitionally unique formulas currently contained in this
	 * lemma set.
	 */
	final private ArrayList formulas;

	public LemmaSet(Context ctxt) {
		assert (ctxt != null);

		this.ctxt = ctxt;
		this.formulas = new ArrayList();
	}

	/**
	 * Adds a lemma to the set. This lemma must be definitionally unequal to
	 * each lemma currently in the set. (Use the HasLemma method to determine
	 * whether or not an equivalent lemma is already in the set.)
	 */
	public void addLemma(Expr newLemma) {
		assert (newLemma.isFormula(ctxt));
		assert (!hasLemma(newLemma));

		formulas.add(newLemma);
	}

	/** Removes a lemma from the set. */
	public void removeLemma(Expr toRemove) {
		assert (toRemove.isFormula(ctxt));
		assert (hasLemma(toRemove));

		formulas.remove(toRemove);
	}

	/** Returns true iff the given lemma is contained in this set */
	public boolean hasLemma(Expr lemma) {
		assert (lemma.isFormula(ctxt));

		ListIterator i = formulas.listIterator();
		while (i.hasNext()) {
			Expr curr = (Expr) i.next();

			if (curr.defEq(ctxt, lemma))
				return true;
		}
		return false;
	}

	/**
	 * Returns a new lemma set containing exactly the same set of formulas as
	 * this one.
	 */
	public LemmaSet copy() {
		LemmaSet ret = new LemmaSet(ctxt);

		ListIterator i = formulas.listIterator();
		while (i.hasNext())
			ret.addLemma((Expr) i.next());

		return ret;
	}

	public Expr simplify(Expr e) {
		Expr e_ = null;

		while (e_ != e) {
			e_ = e;

			if (e.construct == Expr.TERM_APP) {
				TermApp ta = (TermApp) e;

				if (ta.head.construct == Expr.CONST) {
					Const c = (Const) ta.head;
					if (ctxt.isTermCtor(c))
						break;
				}
			}
			if (e.construct == Expr.MATCH) {
				Match m = (Match) e;
				Expr mt_ = simplify(m.t);
				if (mt_ != m.t) {
					e = new Match(simplify(m.t), m.x1, m.x2, m.T, m.C,
							m.consume_scrut);
				}
			}

			e = rewrite(e);
			e = e.evalStep(ctxt);
		}

		return e;
	}

	public Expr instantiate(Expr e) {
		Expr ret = e;

		ListIterator i = formulas.listIterator();
		while (i.hasNext()) {
			Expr curr = (Expr) i.next();

			if (curr.construct != Expr.ATOM)
				continue;

			Atom a = (Atom) curr;

			if (a.equality == false)
				continue;

			if (a.Y1.construct == Expr.VAR) {
				if (a.Y2.construct == Expr.TERM_APP) {
					TermApp ta = (TermApp) a.Y2;

					if (ta.head.construct == Expr.CONST
							&& ctxt.isTermCtor((Const) ta.head))
						ret = ret.subst(a.Y2, a.Y1);
				} else if (a.Y2.construct == Expr.CONST) {
					ret = ret.subst(a.Y2, a.Y1);
				}
			} else if (a.Y2.construct == Expr.VAR) {
				if (a.Y1.construct == Expr.TERM_APP) {
					TermApp ta = (TermApp) a.Y1;

					if (ta.head.construct == Expr.CONST
							&& ctxt.isTermCtor((Const) ta.head))
						ret = ret.subst(a.Y1, a.Y2);
				} else if (a.Y1.construct == Expr.CONST)
					ret = ret.subst(a.Y1, a.Y2);
			}
		}

		return ret;
	}

	public Expr rewrite(Expr e) {
		ListIterator i = formulas.listIterator();
		while (i.hasNext()) {
			Expr curr = (Expr) i.next();

			if (curr.construct != Expr.ATOM)
				continue;

			Atom a = (Atom) curr;

			if (a.equality == false)
				continue;

			// we may need to use both side of the equation to rebuild
			// annotations... for example, { l = nil }. nil needs a type
			// parameter, but the only way to deduce this is to look at
			// the type of nil.

			if (a.Y1.defEq(ctxt, e)) {
				Expr annY1 = UnjoinBase.RebuildAnnotations(a.Y1, ctxt);
				;

				// we use the type of the lhs to reconstruct specificational
				// arguments in the rhs. Is this sound? I think it is,
				// because we are using the rhs to replace the lhs, so we
				// really only care about the type of the lhs.
				Expr tyY1 = annY1.classify(ctxt);

				if (a.Y2.construct == Expr.TERM_APP) {
					TermApp ta = (TermApp) a.Y2;

					if (ta.head.construct == Expr.CONST
							&& ctxt.isTermCtor((Const) ta.head)) {
						Expr headTy = ta.head.classify(ctxt);

						return UnjoinBase.RebuildAnnotationsTargeted(a.Y2,
								tyY1, ctxt);
					}
				} else if (a.Y2.construct == Expr.CONST) {
					if (ctxt.isTermCtor((Const) a.Y2))
						return UnjoinBase.RebuildAnnotationsTargeted(a.Y2,
								tyY1, ctxt);
				}
			}

			if (a.Y2.defEq(ctxt, e) && a.Y1.construct == Expr.TERM_APP) {
				Expr annY2 = UnjoinBase.RebuildAnnotations(a.Y2, ctxt);

				// we use the type of the lhs to reconstruct specificational
				// arguments in the rhs. Is this sound? I think it is,
				// because we are using the rhs to replace the lhs, so we
				// really only care about the type of the lhs.
				Expr tyY2 = annY2.classify(ctxt);

				if (a.Y1.construct == Expr.TERM_APP) {
					TermApp ta = (TermApp) a.Y1;

					if (ta.head.construct == Expr.CONST
							&& ctxt.isTermCtor((Const) ta.head))
						return UnjoinBase.RebuildAnnotationsTargeted(ta, tyY2,
								ctxt);
				} else if (a.Y1.construct == Expr.CONST) {
					if (ctxt.isTermCtor((Const) a.Y1))
						return UnjoinBase.RebuildAnnotationsTargeted(a.Y1,
								tyY2, ctxt);
				}
			}
		}

		return e;
	}
}
