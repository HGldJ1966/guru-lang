package guru;

import java.util.*;
import java.io.*;

public abstract class Expr {

	public static final int INVALID = 0; // never a "construct" of an expr
	public static final int VAR = 1;
	public static final int CONST = 2;
	public static final int METAVAR = 3; // not supported right now
	public static final int STAR = 4; // a hole for contexts
	public static final int STARSTAR = 5; // another hole for contexts
	public static final int ABSTRACTION = 6; /*
											 * when the type is actually
											 * Abstraction (not a subclass)
											 */
	public static final int BANG = 7;

	// terms
	// public static final int INC = 9;
	// public static final int DEC = 10;

	public static final int FUN_TERM = 11;

	public static final int CAST = 12;
	public static final int TERM_APP = 13;
	public static final int ABORT = 14;
	public static final int LET = 15;
	public static final int MATCH = 16;
	public static final int CASE = 17; // only found in match-terms
	public static final int APP = 18; // for some intermediate App instances
	public static final int CUTOFF = 19;

	// types, type families, kinds, and the sole superkind
	public static final int FUN_TYPE = 20;
	public static final int TYPE_APP = 21;
	public static final int TYPE = 22;
	public static final int FORMULA = 23;
	public static final int TKIND = 24; // for kinds of types and type fams.
	public static final int FKIND = 25; // for kinds of formulas and predicates

	// proofs
	public static final int FORALLI = 30;
	public static final int PROOF_APP = 31;
	public static final int EXISTSI = 32;
	public static final int EXISTSE = 33;

	public static final int JOIN = 35;
	public static final int REFL = 36;
	public static final int SYMM = 37;
	public static final int TRANS = 38;
	public static final int CONG = 39;
	public static final int NCONG = 40;
	public static final int INJ = 41;
	public static final int CLASH = 42;
	public static final int ACLASH = 43;
	public static final int INV = 44;
	public static final int SUBST = 45;
	public static final int CONTRA = 46;
	public static final int INDUCTION = 47;
	public static final int HYPJOIN = 48;
	public static final int CIND = 49;
	public static final int LEMMA = 50;

	// formulas
	public static final int FORALL = 51;
	public static final int EXISTS = 52;
	public static final int ATOM = 53;

	public static final int ABBREV = 54;
	public static final int EABBREV = 55;
	public static final int CABBREV = 56; // Duckki: abbrev with classification

	public static final int TRUE = 57;

	// some extra items:

	public static final int TRUEI = 58;
	public static final int CASE_PROOF = 59; // proof
	public static final int EVAL = 60;// proof
	public static final int SHOW = 61; // proof
	public static final int ANDI = 62; // proof, like existsi
	public static final int EVALTO = 63; // proof
	public static final int DISEQI = 64; // proof

	public static final int TERMINATES = 70;// term
	public static final int IMPOSSIBLE = 71; // term
	public static final int STRING_EXPR = 73; // term
	public static final int EXISTSE_TERM = 74; // term
	public static final int SIZE = 75; // term

	public static final int PRED_APP = 80; // formula
	public static final int FALSE = 81; // formula

	public static final int VOID = 82; // type
	public static final int VOIDI = 83; // term
	public static final int DO = 84; // term
	public static final int TRANSS = 85; // proof
	public static final int COMPRESS = 86; // term

	public static final int CHAR_EXPR = 87; // term
	public static final int WORD_EXPR = 88; // term
	public static final int TERM_CASE = 89; // proof

	public static final int COMPILE_AS = 90; // term

	public static final int LEMMA_MARK = 91;
	public static final int ASCRIPTION = 92;
	public static final int UNJOIN = 93;
	public static final int UNJOIN_CONTRA = 94;

	public static final int LAST = 200;

	public int construct;
	boolean result; /*
					 * true iff we reached this Expr as the result of (partial)
					 * evaluation
					 */
	public Position pos;

	public Expr(int construct) {
		this.construct = construct;
		this.result = false;
		this.pos = null;
	}

	// subclasses for each construct must override to define printing
	// for that construct.
	abstract protected void do_print(java.io.PrintStream w, Context ctxt);

	final public void print(java.io.PrintStream w, Context ctxt) {
		// we used to handle a special case here, but no longer.
		do_print(w, ctxt);
	}

	protected void print_pos_comment_short(java.io.PrintStream w) {
		if (pos != null) {
			w.print("(* ");
			w.print(new Integer(pos.linenum).toString());
			w.print(" *)");
		}
	}

	protected void print_pos_comment_long(java.io.PrintStream w) {
		if (pos != null) {
			w.print("(* ");
			pos.print(w);
			w.print(" *)");
		}
	}

	public String debug(Context ctxt) {
		java.io.ByteArrayOutputStream s = new java.io.ByteArrayOutputStream();
		java.io.PrintStream w = new java.io.PrintStream(s);
		defExpandTop(ctxt).do_print(w, ctxt);
		return s.toString();
	}

	public String toString(Context ctxt) {
		java.io.ByteArrayOutputStream s = new java.io.ByteArrayOutputStream();
		java.io.PrintStream w = new java.io.PrintStream(s);
		print(w, ctxt);
		return s.toString();
	}

	// intended only for unannotated terms -- others may fail.
	public final int hashCode(Context ctxt) {
		ctxt.next_var_hash_code = 0;
		return hashCode_h(ctxt);
	}

	public int hashCode_h(Context ctxt) {
		handleError(ctxt,
				"Internal error: hashCode() function not implemented for"
						+ " construct " + (new Integer(construct)).toString()
						+ ".");
		return 0;
	}

	// count free occurrences of e.
	abstract public int numOcc(Expr e);

	public boolean isApp() { // overridden by App
		return false;
	}

	// substitute e for x in this Expr. We only support substituting
	// for Vars x and Holes x.
	abstract public Expr subst(Expr e, Expr x);

	// return the Const with name s in the ctxt, or return an error.
	protected Const _const(Context ctxt, String s) {
		Expr c = ctxt.lookup(s);
		if (c == null || c.construct != Expr.CONST)
			handleError(ctxt, "Cannot find special constant " + s + ".");
		return (Const) c;
	}

	public boolean containsVars(Stack boundVars) {
		boolean returnValue = false;

		Enumeration varsEnum = boundVars.elements();
		while (varsEnum.hasMoreElements()) {
			Var currentVar = (Var) varsEnum.nextElement();
			if (numOcc(currentVar) > 0) {
				returnValue = true;
			}
		}

		return returnValue;
	}

	// substitute e for x in this Expr. x may be an arbitrary ground
	// term, and any sub term of this which is definitionally equal
	// to x will be replaced with e.
	final public Expr rewrite(Context ctxt, Expr e, Expr x, Stack boundVars) {
		if (defEq(ctxt, x, NO_APPROX, true) && !x.containsVars(boundVars)
				&& !e.containsVars(boundVars)) {
			return e;
		} else {
			ctxt.resetNotDefEq();
			return do_rewrite(ctxt, e, x, boundVars);
		}
	}

	public Expr do_rewrite(Context ctxt, Expr e, Expr x, Stack boundVars) {
		handleError(ctxt,
				"Internal error: do_rewrite called on an inappropriate expression in: "
						+ this.getClass().toString());
		// throw new
		// RuntimeException("Internal error: do_rewrite called on an inappropriate expression in: "+this.getClass().toString());
		return this;
	}

	public Expr classify(Context ctxt, int approx, boolean spec) {
		if (approx > NO_APPROX) {
			System.out.println("Approximate classification for this construct "
					+ "unimplemented: " + (new Integer(construct)));
			System.exit(5);
		}
		return classify(ctxt);
	}

	/*
	 * subclasses should override one or the other classify method, or expect a
	 * stack overflow. We will treat this as specificational (use the other
	 * classify() method to specify non-specificational).
	 */
	public Expr classify(Context ctxt) {
		return classify(ctxt, NO_APPROX, true);
	}

	// is e definitionally equal to this expr in the given ctxt.
	protected boolean defEqNoAnno(Context ctxt, Expr e, boolean spec) {
		System.out.println("Definitional equality for this construct"
				+ " unimplemented: " + (new Integer(construct)));
		System.exit(5);
		return false;
	}

	protected boolean defEqNoAnnoApprox(Context ctxt, Expr e, boolean spec) {
		System.out.println("Approximate definitional equality for this"
				+ " construct unimplemented: " + (new Integer(construct)));
		System.exit(5);
		return false;
	}

	final public boolean defEq(Context ctxt, Expr e, boolean spec) {
		return defEq(ctxt, e, NO_APPROX, spec);
	}

	// specificational by default
	final public boolean defEq(Context ctxt, Expr e) {
		return defEq(ctxt, e, NO_APPROX, true);
	}

	/*
	 * approx level 2 means all types are considered equal; 1 means we drop
	 * indices; 0 means drop annotations from terms (no approximation).
	 */
	public static final int NO_APPROX = 0;
	public static final int APPROX_NO_INDICES = 1;
	public static final int APPROX_TRIVIAL = 2;

	final public boolean defEq(Context ctxt, Expr e, int approx, boolean spec) {
		if (approx == 2)
			return true;

		if (ctxt.getFlag("debug_def_eq")) {
			ctxt.w.println("--------------------------------------------------");
			ctxt.w.println("Testing definitional equality (spec = "
					+ (spec ? "true" : "false") + ") of:");
			ctxt.w.print("1. ");
			print(ctxt.w, ctxt);
			ctxt.w.print("\n2. ");
			e.print(ctxt.w, ctxt);
			ctxt.w.println("");
			ctxt.w.flush();
		}

		Expr e1 = dropAnnos(ctxt);
		Expr e2 = e.dropAnnos(ctxt);

		if (ctxt.getFlag("debug_def_eq")) {
			ctxt.w.println("With annotations dropped:");
			ctxt.w.print("1. ");
			e1.print(ctxt.w, ctxt);
			ctxt.w.print("\n2. ");
			e2.print(ctxt.w, ctxt);
			ctxt.w.println("");
			ctxt.w.flush();
		}
		if (approx == APPROX_NO_INDICES)
			return e1.defEqNoAnnoApprox(ctxt, e2, spec);
		return e1.defEqNoAnno(ctxt, e2, spec);
	}

	// do not drop annotations, treat as specificational
	//
	// type family abbrev's are not expanded.
	public Expr defExpandTop(Context ctxt) {
		return defExpandTop(ctxt, false, true);
	}

	public Expr defExpandTop(Context ctxt, boolean drop_annos, boolean spec) {
		Expr ret = defExpandOne(ctxt, drop_annos, spec);
		if (ret != this)
			return ret.defExpandTop(ctxt, drop_annos, spec);
		return ret;
	}

	public Expr defExpandOne(Context ctxt, boolean drop_annos, boolean spec) {
		if (construct == VAR) {
			Var v = (Var) this;
			if (ctxt.isMacroDefined(v))
				return ctxt.getDefBody(v);
		} else if (construct == CONST) {
			Const c = (Const) this;
			if (ctxt.isDefined(c) && (spec || !ctxt.isOpaque(c))
					&& !ctxt.isTypeFamilyAbbrev(c))
				/*
				 * if we are not in a spec expression, then we do not expand
				 * opaque definitions. Also, we do not expand type family
				 * abbreviations. That is done in TypeApp, so that we can do
				 * beta-reductions immediately with them.
				 */
				return (drop_annos ? ctxt.getDefBodyNoAnnos(c) : ctxt
						.getDefBody(c));
		} else if (construct == ABBREV)
			return ((Abbrev) this).subst();
		else if (construct == CUTOFF) {
			return ((Cutoff) this).get_nat_t(ctxt, spec);
		} else if (construct == PRED_APP)
			return ((PredApp) this).doBeta(ctxt, drop_annos, spec, true /*
																		 * expand
																		 * defs
																		 */);
		return this;
	}

	public static void handleError(Position p, String msg) {
		if (p != null) {
			p.print(System.out);
			System.out.print(": ");
		}
		System.out.println("");
		System.out.println(msg);
		System.exit(2);
	}

	public void handleError(Context ctxt, String msg) {
		handleError(ctxt, pos, msg);
	}

	public void handleError(Context ctxt, Position p, String msg) {
		if (p != null) {
			p.print(System.out);
			System.out.print(": ");
		}
		System.out.println("classification error.\n\n" + msg);
		ctxt.printDefEqErrorIf();
		System.exit(2);
	}

	// is this Expr either d or <d Xs>?
	boolean isdtype(Context ctxt, Const d) {
		if (this == d)
			return true;
		if ((construct == TYPE_APP)
				&& ((TypeApp) this).getHead(ctxt, false) == d)
			return true;
		if (construct == VAR && ctxt.isMacroDefined((Var) this))
			return ctxt.getDefBody((Var) this).isdtype(ctxt, d);
		return false;
	}

	// if this is a dtype, return its head (i.e., c if this is c or <c Y1 ...
	// Yn>);
	// otherwise return null.
	Const typeGetHead(Context ctxt, boolean spec) {
		if (construct == CONST) {
			Const c = (Const) this;
			boolean not_opaque_if = spec || !ctxt.isOpaque(c);
			if (ctxt.isDefined(c) && not_opaque_if) {
				if (ctxt.getFlag("debug_typeGetHead")) {
					ctxt.w.println("typeGetHead() called on: " + toString(ctxt)
							+ ", with spec=" + (new Boolean(spec)).toString()
							+ ", opaque="
							+ (new Boolean(ctxt.isOpaque(c))).toString());
					ctxt.w.flush();
				}
				/*
				 * if c is coming from a type of the form <d xs> where d is a
				 * type family abbrev and xs is an incomplete argument list,
				 * then we will get an infinite loop without the following
				 * check.
				 */
				Expr cc = c.defExpandTop(ctxt, false, true);
				if (cc == c)
					return null;
				return cc.typeGetHead(ctxt, spec);
			}
			if (ctxt.isTypeCtor((Const) this) && not_opaque_if)
				return (Const) this;
			return null;
		}
		if (construct != TYPE_APP)
			return null;
		return ((TypeApp) this).getHead(ctxt, spec).typeGetHead(ctxt, spec);
	}

	// we assume this is a type, and return true iff it is an inductive
	// type that is not opaque.
	boolean isdtype(Context ctxt, boolean spec) {
		Const head = typeGetHead(ctxt, spec);
		return (head != null);
	}

	/*
	 * assuming this is a type, is it one corresponding to tracked references?
	 * We assume this is not being called in a specificational position.
	 */
	public boolean isTrackedType(Context ctxt) {
		if (construct == CONST) {
			Const d = (Const) this;
			if (ctxt.isUntracked(d))
				return false;
			if (ctxt.isOpaque(d))
				return true;
		}

		Expr T = defExpandTop(ctxt, false, false);

		if (T.construct == FUN_TYPE || T.construct == TYPE)
			return false;
		if (T.construct == CONST) {
			Const d = (Const) T;
			return !ctxt.isFlat(d) && !ctxt.isUntracked(d);
		}
		if ((T.construct == TYPE_APP)) {
			Expr h = ((TypeApp) T).getHead(ctxt, false);
			return !ctxt.isFlat((Const) h);
		}
		return !isFormula(T.construct);
	}

	public static Expr[] varArrayToExprArray(Var[] v) {
		int iend = v.length;
		Expr[] e = new Expr[iend];
		for (int i = 0; i < iend; i++)
			e[i] = v[i];
		return e;
	}

	public boolean isFormula(Context ctxt) {
		Expr tmp = defExpandTop(ctxt);
		return isFormula(tmp.construct);
	}

	public static boolean isFormula(int construct) {
		switch (construct) {
		case FORALL:
		case EXISTS:
		case EABBREV:
		case CABBREV:
		case ABBREV:
		case ATOM:
		case PRED_APP:
		case TRUE:
		case FALSE:
			return true;
		}
		return false;
	}

	public static boolean isProof(int construct) {
		switch (construct) {
		case ASCRIPTION:
		case VAR:
		case BANG:
		case CONST:
		case FORALLI:
		case PROOF_APP:
		case CASE_PROOF:
		case EXISTSI:
		case ANDI:
		case EXISTSE:
		case EABBREV:
		case CABBREV:
		case ABBREV:
		case JOIN:
		case UNJOIN:
		case EVAL:
		case EVALTO:
		case HYPJOIN:
		case SHOW:
		case REFL:
		case SYMM:
		case LEMMA:
		case TRANS:
		case TRANSS:
		case CONG:
		case NCONG:
		case INJ:
		case CLASH:
		case ACLASH:
		case INV:
		case SUBST:
		case CONTRA:
		case INDUCTION:
		case TRUEI:
		case DISEQI:
		case CIND:
		case TERM_CASE:
			return true;
		}
		return false;
	}

	public static boolean isTerm(int construct) {
		switch (construct) {
		case ASCRIPTION:
		case VAR:
		case CONST:
		case VOIDI:
		case DO:
		case COMPRESS:
		case FUN_TERM:
		case CAST:
		case COMPILE_AS:
		case TERMINATES:
		case TERM_APP:
		case ABORT:
		case LET:
		case ABBREV:
		case EABBREV:
		case CABBREV:
		case MATCH:
		case CUTOFF:
		case IMPOSSIBLE:
		case SIZE:
		case EXISTSE_TERM:
			return true;
		}
		return false;
	}

	public static boolean isTypeOrKind(int construct) {
		switch (construct) {
		case VAR:
		case CONST:
		case VOID:
		case BANG:
		case ABBREV:
		case EABBREV:
		case CABBREV:
		case FUN_TYPE:
		case TYPE_APP:
		case TYPE:
			return true;
		}
		return false;
	}

	public boolean isTerm(Context ctxt) {
		Expr tmp = defExpandTop(ctxt);
		if (tmp.construct == VAR)
			return ctxt.getClassifier((Var) tmp).isTypeOrKind(ctxt);
		if (tmp.construct == ASCRIPTION)
			return ((Ascription)tmp).target.isTerm(ctxt);
		if (tmp.construct == CONST)
			return ctxt.isTermCtor((Const) tmp);

		return isTerm(tmp.construct);
	}

	public boolean isTypeOrKind(Context ctxt) {
		Expr tmp = defExpandTop(ctxt);

		if (tmp.construct == VAR) {
			Expr c = ctxt.getClassifier((Var) tmp);
			if (c == null)
				System.err.println("Internal error. Null classifier for: "
						+ tmp.toString(ctxt));
			return c.construct == TYPE;
		}
		if (tmp.construct == CONST)
			return ctxt.isTypeCtor((Const) tmp)
					|| ctxt.isTypeFamilyAbbrev((Const) tmp);

		return isTypeOrKind(tmp.construct);
	}

	public boolean isProof(Context ctxt) {
		Expr tmp = defExpandTop(ctxt);
		if (tmp.construct == VAR)
			return ctxt.isAssumption((Var) tmp);
		if (tmp.construct == ASCRIPTION)
			return ((Ascription)tmp).target.isProof(ctxt);
		if (tmp.construct == CONST)
			return false;

		return isProof(tmp.construct);
	}

	public boolean isY(Context ctxt) {
		return isTerm(ctxt) || isTypeOrKind(ctxt);
	}

	public boolean isB(Context ctxt) {
		return (construct == TYPE || isTypeOrKind(ctxt));
	}

	public boolean isI(Context ctxt) {
		Expr e = defExpandTop(ctxt);
		
		if (isTypeOrKind(e.construct) || isProof(e.construct)
				|| e.construct == Expr.CONST || e.construct == Expr.FUN_TERM)
			return true;
		if (e.construct == Expr.CAST)
			return ((Cast) e).t.isI(ctxt);
		if (e.construct == Expr.TERMINATES)
			return ((Terminates) e).t.isI(ctxt);
		return e.isIa(ctxt);
	}

	protected boolean isIa(Context ctxt) {
		if (construct == Expr.CONST)
			return !ctxt.isDefined((Const) this);
		if (construct == Expr.TERM_APP) {
			TermApp ee = (TermApp) this;
			if (!ee.head.isIa(ctxt))
				return false;
			for (int i = 0, iend = ee.X.length; i < iend; i++)
				if (!ee.X[i].isI(ctxt))
					return false;
			return true;
		}
		return false;
	}

	// drop all proofs, and all annotations in terms.
	abstract public Expr dropAnnos(Context ctxt);

	public boolean isAnnotation(Context ctxt) {
		return false;
	}

	// it is crucial that if this Expr is stuck or in normal form,
	// calling evalStep() on it will return exactly the same Expr
	// (or at worst, return its head-expanded form if that is different,
	// or else the same Expr). The outside world is depending on
	// being able to use Java "==" to check whether or not we are
	// done evaluating.
	public Expr evalStep(Context ctxt) {
		return this;
	}

	// used only by Inv.
	public boolean subtermDefEqNoAnno(Context ctxt, Expr e) {
		return this.defEqNoAnno(ctxt, e, true /* spec */);
	}

	public Expr eval(Context ctxt) {
		if (result)
			return this;
		Expr next = defExpandTop(ctxt).dropAnnos(ctxt), prev;
		boolean first = true, dbg = ctxt.getFlag("debug_eval");
		do {
			if (next.result)
				break;
			prev = next;
			next = prev.evalStep(ctxt);
			if (dbg) {
				if (first) {
					first = false;
					System.out.print("[ " + prev.toString(ctxt));
				}
				System.out.print(" -->\n  " + next.toString(ctxt));
			}
		} while (next != prev);
		if (dbg && !first)
			// we took at least one step (and we are debugging)
			System.out.println("]");
		next.result = true;
		return next;
	}

	public static class isInstC {
		public Expr val;
		public boolean is;

		public isInstC(Expr val) {
			this.val = val;
			this.is = true;
		}

		public isInstC() {
			this.val = null;
			this.is = false;
		}

		public isInstC(boolean is) {
			this.val = null;
			this.is = is;
		}
	}

	// If the given Expr is an instance of this Expr,
	// which is assumed to be a syntactically well-formed context,
	// return an isInstC with is-field true and val-field equal
	// to the value corresponding to a STAR (contexts should have
	// just one STAR, though multiple STARSTARs are allowed).
	//
	// By default, we just return whether the current expr is definitionally
	// equivalent to e. Note that this is the right thing to do for
	// proofs and formulas, which cannot be contexts (but can appear in
	// contexts).
	public isInstC isInstance(Context ctxt, Expr e) {
		return new isInstC(defEq(ctxt, e));
	}

	// for termination checking of proofs, allowing induction
	public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars) {
		if (isProof(construct))
			handleError(ctxt, "Internal error: termination checking for "
					+ "this construct unimplemented: "
					+ (new Integer(construct)));
	}

	// for termination checking of terms
	public void checkTermination(Context ctxt) {
		if (isTerm(ctxt))
			handleError(ctxt,
					"term termination judgment unimplemented for this construct: "
							+ construct);
	}

	/*
	 * Return the set of free variables that will appear in this code when it is
	 * compiled. This would be the same as if we dropped annotations, except
	 * that type variables are comptutationally relevant for our compilation.
	 */
	public void getFreeVarsComputational(Context ctxt, Collection vars) {
		handleError(ctxt, "Internal error: getFreeVars() is "
				+ " unimplemented for construct " + (new Integer(construct)));
	}

	public void checkSpec(Context ctxt, boolean in_type, Position p) {
		handleError(ctxt, "Internal error: checkSpec() is "
				+ "unimplemented for construct " + (new Integer(construct)));
	}

	// get all the constants in this Expr.
	public java.util.Set getDependences() {
		return new TreeSet();
	}
	
	// Given a target term, target, and a set of enclosing functions calls,
	// funCalls, returns an unjoin deduction representing all possible
	// evaluation paths for this term which could result in joining with
	// the target term. (If eq is false, then we instead return the set of 
	// all possible evaluation paths which do not join this term with the
	// target term.)
	public UnjoinDeduction Unjoin(
			Expr target, 
			UnjoinContext uctxt,
			Context baseCtxt,
			boolean eq
	)
	{
		//Unjoin has not been implemented for this construct.
		assert(false);
		
		return null;
	}

	/*
	 * get all the constants in this Expr or in any Expr reachable by a
	 * definition from it. public java.util.Set getAllDependences(ctxt) {
	 * 
	 * }
	 */

	// if dtype is true, compute the carraway datatype (aka runtime type),
	// if dtype is false, compute the carraway resource type.
	public guru.carraway.Expr toCarrawayType(Context ctxt, boolean dtype) {
		handleError(ctxt,
				"Internal error: toCarraway() or toCarrawayType() is "
						+ "unimplemented for construct "
						+ (new Integer(construct)));
		return null;
	}

	// by default, we assume this is a type
	public guru.carraway.Expr toCarraway(Context ctxt) {
		return toCarrawayType(ctxt, true);
	}
}
