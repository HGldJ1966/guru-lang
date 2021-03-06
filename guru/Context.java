package guru;
import java.util.*;
import java.io.*;


public class Context {

    protected HashMap flags;
    protected HashMap typeCtors;
    protected HashMap typeCtorsKind;
    protected HashMap typeCtorsTermCtors;
    protected HashSet typeFamAbbrev;
    protected HashSet preds;
    protected HashSet opaque;
    protected HashSet untracked;
    protected Vector typeCtorsVec;
    protected HashMap termCtors;
    protected HashMap termCtorsWhich;
    protected HashMap termCtorsType;
    protected HashMap termCtorsTypeCtor;
    protected HashMap totalityThms;
    protected HashMap defs;
    protected HashMap defsBody;
    protected HashMap defsBodyNoAnnos;
    protected HashMap defsClassifier;
    protected Vector defsVec;
    protected HashMap localVars;
    protected HashMap localVarsClassifier;
    protected HashSet trustedDefs;
    protected HashMap specData;

    public PrintStream w;

    public Expr star, starstar, type, tkind, fkind, formula, abort;
    public Var tmpvar;

    public boolean eval;

    public Expr noteq1, noteq2;

    public Context() {
	flags = new HashMap(256);
	typeCtors = new HashMap(256);
	typeCtorsKind = new HashMap(256);
	typeCtorsTermCtors = new HashMap(256);
	typeFamAbbrev = new HashSet(256);
	preds = new HashSet(256);
	opaque = new HashSet(256);
	untracked = new HashSet(256);
	typeCtorsVec = new Vector();
	termCtors = new HashMap(1024);
	termCtorsType = new HashMap(1024);
	termCtorsWhich = new HashMap(1024);
	termCtorsTypeCtor = new HashMap(1024);
	totalityThms = new HashMap(256);
	defs = new HashMap(2048);
	defsBody = new HashMap(2048);
	defsBodyNoAnnos = new HashMap(2048);
	defsClassifier = new HashMap(2048);
	defsVec = new Vector();
	localVars = new HashMap(2048);
	localVarsClassifier = new HashMap(2048);
	specData = new HashMap(256);
	trustedDefs = new HashSet();
	
	star = new Star();
	starstar = new StarStar();
	type = new Type();
	tkind = new Kind(Expr.TKIND);
	fkind = new Kind(Expr.FKIND);
	formula = new Formula();
	abort = new Abort(new Bang());
	tmpvar = new Var("tmp");
	w = new PrintStream(new BufferedOutputStream(System.out));
	
	eval = true;
    }

    // create a copy of the given context
    public Context(Context prev) {
	flags = prev.flags;
	w = prev.w;
	typeCtors = prev.typeCtors;
	typeCtorsKind = prev.typeCtorsKind;
	typeCtorsTermCtors = prev.typeCtorsTermCtors;
	typeFamAbbrev = prev.typeFamAbbrev;
	preds = prev.preds;
	opaque = prev.opaque;
	untracked = prev.untracked;
	typeCtorsVec = prev.typeCtorsVec;
	termCtors = prev.termCtors;
	termCtorsType = new HashMap(prev.termCtorsType);
	termCtorsWhich = prev.termCtorsWhich;
	termCtorsTypeCtor = prev.termCtorsTypeCtor;
	totalityThms = prev.totalityThms;
	star = prev.star;
	starstar = prev.starstar;
	type = prev.type;
	tkind = prev.tkind;
	fkind = prev.fkind;
	formula = prev.formula;
	tmpvar = prev.tmpvar;
	defs = new HashMap(prev.defs);
	defsBody = new HashMap(prev.defsBody);
	defsBodyNoAnnos = new HashMap(prev.defsBodyNoAnnos);
	defsClassifier = new HashMap(prev.defsClassifier);
	defsVec = new Vector(prev.defsVec);
	localVars = prev.localVars;
	specData = prev.specData;
	localVarsClassifier = new HashMap(prev.localVarsClassifier);
	eval = prev.eval;
	trustedDefs = prev.trustedDefs;
    }

    // clear global and local definitions
    public void clearDefs() {
	defs = new HashMap(2048);
	defsBody = new HashMap(2048);
	defsBodyNoAnnos = new HashMap(2048);
	defsClassifier = new HashMap(2048);
	defsVec = new Vector();
	specData = new HashMap(256);
	typeFamAbbrev = new HashSet(256);
	preds = new HashSet(256);
	/*localVars = new HashMap(2048);
	  localVarsClassifier = new HashMap(2048);*/
	trustedDefs = new HashSet();
    }

    public void clearCtors() {
	typeCtors = new HashMap(256);
	typeCtorsKind = new HashMap(256);
	typeCtorsTermCtors = new HashMap(256);
	typeCtorsVec = new Vector();
	termCtors = new HashMap(1024);
	termCtorsType = new HashMap(1024);
	termCtorsWhich = new HashMap(1024);
	termCtorsTypeCtor = new HashMap(1024);
    }

    public void notDefEq(Expr noteq1, Expr noteq2) {
	this.noteq1 = noteq1;
	this.noteq2 = noteq2;
    }

    public void resetNotDefEq() {
	this.noteq1 = null;
	this.noteq2 = null;
    }

    public boolean isTrusted(Const c) {
	return trustedDefs.contains(c);
    }

    public void markTrusted(Const c) {
	trustedDefs.add(c);
    }

    public void clearTrusted() {
	trustedDefs = new HashSet();
    }

    public void markTypeFamilyAbbrev(Const c) {
	typeFamAbbrev.add(c);
    }

    public boolean isTypeFamilyAbbrev(Const c) {
	return typeFamAbbrev.contains(c);
    }

    public void markPredicate(Const c) {
	preds.add(c);
    }

    public boolean isPredicate(Const c) {
	return preds.contains(c);
    }

    public void addTypeCtor(Const c, Expr kind) {
	typeCtors.put(c.name, c);
	typeCtorsKind.put(c, kind);
	typeCtorsTermCtors.put(c, new ArrayList());
	typeCtorsVec.add(c);
    }

    // record that a given type ctor is opaque (no matching allowed on it)
    public void makeOpaque(Const d) {
	opaque.add(d);
    }

    public boolean isOpaque(Const d) {
	return opaque.contains(d);
    }

    public void makeUntracked(Const d) {
	untracked.add(d);
    }

    /* tell whether or not d has been marked opaque.  (So if it has
       not been marked, the default is to say it is tracked.) */
    public boolean isUntracked(Const d) {
	return untracked.contains(d);
    }

    // we assume type ctor d is added (with addTypeCtor()) before
    // this is called.
    public void addTermCtor(Const c, Const d, Expr type) {
	termCtors.put(c.name, c);
	termCtorsType.put(c, type);
	termCtorsTypeCtor.put(c, d);
	List l = (List)typeCtorsTermCtors.get(d);
	termCtorsWhich.put(c, new Integer(l.size()));
	l.add(c);
    }

    // change the kind of a type ctor.  This is used only by the compiler.
    public void reclassifyTypeCtor(Const c, Expr kind) {
	typeCtorsKind.put(c,kind);
    }

    // change the kind of a type ctor.  This is used only by the compiler.
    public void reclassifyTermCtor(Const c, Expr tp) {
	termCtorsType.put(c,tp);
    }

    // assuming d is a type ctor already added, get all its term ctors.
    public Collection getTermCtors(Const d) {
	return (Collection)typeCtorsTermCtors.get(d);
    }

    public int numTermCtors(Const d) {
	return getTermCtors(d).size();
    }

    // datatype d is flat if none of its constructors require arguments.
    public boolean isFlat(Const d) {
	Collection C = getTermCtors(d);
	if (C == null)
	    return false;
	Iterator it = C.iterator();
	while (it.hasNext()) {
	    Const c = (Const)it.next();
	    Expr T = getClassifier(c);
	    if (T.defExpandTop(this).construct == Expr.FUN_TYPE)
		return false;
	}
	return true;
    }

    // return which term ctor this is, based on the order in which
    // the term ctors for c's datatype were added.
    public Integer getWhichTermCtor(Const c) {
	return (Integer)termCtorsWhich.get(c);
    }

    // we assume c is either a term or type constructor
    public int getArity(Const c) {
	Expr cl = getClassifier(c).defExpandTop(this);
	if (cl.construct == Expr.FUN_TYPE)
	    return ((FunType)cl).getArity();
	return 0;
    }	    

    // check that the term ctors in c are all and only those from a
    // single type constructor (empty array allowed).  Return -1 if no
    // problem, -2 if an extra constructor at the end, and the index
    // of the first differing ctor otherwise.
    public int checkTermCtors(Const[] c) 
    {
	int clen = c.length;
	List l = (List)typeCtorsTermCtors.get(getTypeCtor(c[0]));
	int iend = clen;
	int llen = l.size();
	if (iend > llen)
	    iend = llen;
	for (int i = 0; i < iend; i++) 
	    if (l.get(i) != c[i])
		return i;
	if (clen > llen)
	    return -2;
	if (llen > clen)
	    return clen;
	return -1;
    }

    // like define(Const,...), except that we create a new Const with a 
    // name like basename but not shared by any other Const.  We return
    // the new Const.
    public Const define(String basename,
			Expr classifier, Expr body, Expr bodyNoAnnos) {
	String name = basename;
	int tick = 2;
	
	while (defs.containsKey(name))
	    name = basename+(new Integer(tick++)).toString();
	Const c = new Const(name);
	define(c, classifier, body, bodyNoAnnos);
	return c;
    }

    public void define(Const c, Expr classifier, Expr body, Expr bodyNoAnnos) {
	defs.put(c.name, c);
	defsBody.put(c, body);
	defsBodyNoAnnos.put(c, bodyNoAnnos);
	defsClassifier.put(c, classifier);
	defsVec.add(c);
    }

    public void macroDefine(Var v, Expr body) {
	defsBody.put(v, body);
    }

    public Expr getDefBody(Const c) {
	return (Expr)defsBody.get(c);
    }
    
    public Expr getDefBodyNoAnnos(Const c) {
	return (Expr)defsBodyNoAnnos.get(c);
    }

    public Expr getDefBody(Var v) {
	return (Expr)defsBody.get(v);
    }

    // return the type constructor for the given term constructor (or
    // null if there is none).
    public Const getTypeCtor(Const c) {
	return (Const)termCtorsTypeCtor.get(c);
    }

    /* register a constant as a total function.  This assumes that 
       the given formula is a Forall-Exists equation with lhs a TermApp. */
    public void registerTotal(Const c, Forall thm) {
	LinkedList l = (LinkedList)totalityThms.get(c);
	if (l == null) {
	    l = new LinkedList();
	    totalityThms.put(c,l);
	}
	l.add(thm);
    }

    public boolean isTotal(Const c) {
	return totalityThms.containsKey(c);
    }

    public Collection getTotalityTheorems(Const c) {
	return (Collection)totalityThms.get(c);
    }

    public boolean isTermCtor(Const c) {
	return (termCtors.get(c.name) != null);
    }

    public boolean isTypeCtor(Const c) {
	return (typeCtors.get(c.name) != null);
    }

    public boolean isDefined(Const c) {
	return (defs.get(c.name) != null);
    }

    public boolean isMacroDefined(Var v) {
	return (defsBody.get(v) != null);
    }

    public boolean isCtor(Const c) {
	return isTermCtor(c) || isTypeCtor(c);
    }

    // map the name of v to v.
    public void pushVar(Var v) {
	String varname = v.name;
	Stack s = (Stack)localVars.get(varname);
	if (s == null) {
	    s = new Stack();
	    localVars.put(varname, s);
	}
	s.push(v);
    }

    // map v to classifier
    public void setClassifier(Var v, Expr classifier) {
	localVarsClassifier.put(v,classifier);

	if (getFlag("debug_context_set_classifier")) {
	    w.print("Setting ");
	    v.print(w, this);
	    w.print(" : ");
	    classifier.print(w, this);
	    w.println("");
	    w.flush(); 
	}
    }

    public Expr getClassifier(Var v) {
	return (Expr)localVarsClassifier.get(v);
    }

    /* classifiers of consts should usually be set by calling define().
       This method is used during compilation to set a type temporarily
       for a Const, without actually defining it. */
    public void setClassifier(Const c, Expr classifier) {
	defsClassifier.put(c,classifier);
    }

    public Expr getClassifier(Const x) {
	Object c = typeCtorsKind.get(x);
	if (c != null)
	    return (Expr)c;
	c = termCtorsType.get(x);
	if (c != null)
	    return (Expr)c;
	return (Expr)defsClassifier.get(x);
    }

    public void popVar(Var v) {
	((Stack)localVars.get(v.name)).pop();
    }

    public boolean multiple_bindings(Var v) {
	String name = v.name;
	Stack s = (Stack)localVars.get(name);
	return ((s != null && s.size() > 1) || 
		(defs.get(name) != null) ||
		(termCtors.get(name) != null) ||
		(typeCtors.get(name) != null));
    }

    public void printDefEqErrorIf() {
	if (noteq1 != null) {
	    w.println("\n"
                               +"These terms are not definitionally equal (causing the error above):\n"
			       +"1. "+noteq1.toString(this)+"\n"
			       +"2. "+noteq2.toString(this));
            if (noteq1 != noteq1.dropAnnos(this) || noteq2 != noteq2.dropAnnos(this))
                w.println("\n"
                                   +"Without annotations:\n"
                                   +"1. "+noteq1.dropAnnos(this).toString(this)+"\n"
                                   +"2. "+noteq2.dropAnnos(this).toString(this));
	    w.flush();
        }
    }

    // try to find an identifier with the given name
    public Expr lookup(String name) {
	Stack s = (Stack)localVars.get(name);
	if (s != null && !s.empty())
	    return (Var)s.peek();

	Expr d = (Expr)defs.get(name);
	if (d != null)
	    return d;

	d = (Const)typeCtors.get(name);
	if (d != null)
	    return d;

	d = (Const)termCtors.get(name);
	if (d != null)
	    return d;

	return null; // can't find this identifier
    }

    public void markSpec(Expr e){
	/*System.out.print("marked as spec:");
	e.do_print(System.out,this);
	System.out.println(" (* " + e + " *)");*/
	specData.put(e, null);
    }
    public boolean isSpec(Expr e){
	return specData.containsKey(e);
    }

    // we assume v has a declared classifier
    public boolean isAssumption(Var v) {
	Expr c = getClassifier(v);
	if (c == null)
	    v.handleError(this,
			  "Internal error: cannot find classifier for this "
			  +"variable: "+v.toString(this));
	return c.isFormula(this);
    }

    // we assume c has a declared classifier
    public boolean provesTheorem(Const c) {
	Expr cc = getClassifier(c);
	if (cc == null)
	    c.handleError(this,
			  "Internal error: cannot find classifier for this "
			  +"constant: "+c.toString(this));
	return cc.isFormula(this);
    }

    public void setFlag(String flag) {
	flags.put(flag, new Boolean(true));
    }

    public void unsetFlag(String flag) {
	flags.put(flag, new Boolean(false));
    }

    public boolean getFlag(String flag) {
	Boolean b = (Boolean)flags.get(flag);
	if (b == null)
	    return false;
	return b.booleanValue();
    }

    // get all the Consts for type ctors, in the order they were added
    public Collection getTypeCtors() {
	return typeCtorsVec;
    }

    // get all the defined Consts, in the order defined.
    public Collection getDefinedConsts() {
	return defsVec;
    }

    public Collection getTrustedDefs() {
	return trustedDefs;
    }
}
