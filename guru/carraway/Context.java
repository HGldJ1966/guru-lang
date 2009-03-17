package guru.carraway;
import guru.Position;
import java.util.Collection;
import java.util.Iterator;
import java.util.Vector;
import java.util.HashSet;
import java.util.HashMap;
import java.util.Stack;
import java.io.PrintStream;
import java.io.BufferedOutputStream;
import java.io.FileOutputStream;
import java.io.FileNotFoundException;

public class Context extends guru.FlagManager {
    protected HashMap consts; // indexed by name
    protected HashMap vars; // indexed by name
    protected HashMap subst;
    protected HashMap tpctors;
    protected HashMap ctors;
    protected HashMap types;
    protected HashMap rttypes;
    protected HashMap funcs;
    protected HashMap globals;
    protected HashSet attrs;
    protected HashMap pinning;
    protected HashMap pinnedby;
    protected HashMap primitives;
    protected HashMap inits;
    protected HashMap dels;

    protected HashMap refs;
    protected HashMap checkpoint_refs;
    protected Vector changed_refs;
    protected int refnum;

    protected int varnum;

    protected String cur_file;
    public PrintStream cw;
    public String file_suffix;

    public Context(String file_suffix) {
	this.file_suffix = file_suffix;
	consts = new HashMap(256);
	vars = new HashMap(256);
	globals = new HashMap(256);
	subst = new HashMap(256);
	tpctors = new HashMap(256);
	ctors = new HashMap(256);
	funcs = new HashMap(256);
	types = new HashMap(256);
	rttypes = new HashMap(256);
	attrs = new HashSet(256);
	primitives = new HashMap(256);
	pinning = new HashMap(256);
	pinnedby = new HashMap(256);
	inits = new HashMap(256);
	dels = new HashMap(256);

	refs = new HashMap(256);
	checkpoint_refs = null;
	changed_refs = new Vector();
	refnum = 0;
	varnum = 0;
    }

    // return an error message if there was a problem opening the compiler output file determined by f.
    public String setCurrentFile(String f) {
	if (cw != null) {
	    cw.flush();
	    cw.close();
	}
	cur_file = f;
	if (f == null)
	    return null;
	if (f.length() < 3)
	    return new String("The included file name is too short.");
	String suf = f.substring(f.length() - 2, f.length());
	if (!suf.equals(file_suffix))
	    return new String("The included file does not end with the expected suffix."
			      +"\n\n1. the expected suffix: "+file_suffix
			      +"\n\n2. the file name: "+f);
	
	String n = f.substring(0, f.length() - 2) + ".c";
	
	try {
	    cw = new PrintStream(new BufferedOutputStream(new FileOutputStream(n)));
	}
	catch(FileNotFoundException e) {
	    return new String("Could not open the included file.");
	}

	cw.println("// produced by carraway\n");

	return null;
    }

    public String getCurrentFile() {
	return cur_file;
    }

    protected void declareConst(Sym s) {
	consts.put(s.name,s);	
    }

    public void addAttribute(Sym s) {
	declareConst(s);
	setType(s,new Type());
	attrs.add(s);
    }

    public boolean isAttribute(Sym s) {
	return attrs.contains(s);
    }

    public Sym lookup(String name) {
	if (consts.containsKey(name))
	    return (Sym)consts.get(name);
	if (vars.containsKey(name)) {
	    Stack S = (Stack)vars.get(name);
	    if (S == null || S.empty())
		return null;
	    return (Sym)S.peek();
	}
	return null;
    }

    public void pushVar(Sym s) {
	String varname = s.name;
	Stack S = (Stack)vars.get(varname);
	if (S == null) {
	    S = new Stack();
	    vars.put(varname, S);
	}
	S.push(s);
    }

    public void setType(Sym s, Expr T) {
	types.put(s,T);
    }

    public void popVar(Sym s) {
	((Stack)vars.get(s.name)).pop();
    }

    public boolean isVar(Sym s) {
	return (!isPrimitive(s) && !isDatatype(s) &&
		!isGlobal(s) && !isAttribute(s) && !isFunction(s));
    }

    public boolean isPrimitive(Sym s) {
	return primitives.containsKey(s);
    }

    public String getPrimitivesCode(Sym s) {
	return (String)primitives.get(s);
    }

    public void addPrimitive(Sym s, Expr T, String code) {
	types.put(s,T);
	primitives.put(s,code);
    }

    public Sym getDeleteFunction(Sym s) {
	return (Sym)dels.get(s);
    }

    public void addDatatype(Sym tp, Sym del) {
	declareConst(tp);
	dels.put(tp,del);
    }

    public void addDatatype(Sym tp, Sym[] cs, Expr[] ctypes, Expr[] rtypes) {
	for (int i = 0, iend = cs.length; i < iend; i++) {
	    declareConst(cs[i]);
	    ctors.put(cs[i],tp);
	    types.put(cs[i],ctypes[i]);
	    rttypes.put(cs[i],rtypes[i]);
	}
	declareConst(tp);
	tpctors.put(tp,cs);
	types.put(tp,new Type());
    }

    public Expr getCtorRuntimeType(Sym tp) {
	return (Expr)rttypes.get(tp);
    }
    
    // is c a (term) ctor.
    public boolean isCtor(Sym c) {
	return ctors.containsKey(c);
    }

    // if c is a (term) ctor
    public Sym getDatatype(Sym c) {
	return (Sym)ctors.get(c);
    }

    public boolean isDatatype(Sym tp) {
	return tpctors.containsKey(tp) || dels.containsKey(tp);
    }

    public Sym[] getCtors(Sym tp) {
	return (Sym[])tpctors.get(tp);
    }

    public void addGlobal(Sym s, Expr T, Expr t) {
	declareConst(s);
	types.put(s,T);
	globals.put(s,t);
    }

    public boolean isGlobal(Sym s) {
	return globals.containsKey(s);
    }

    // get what the global is defined to be
    public Expr getDefinition(Sym s) {
	return (Expr)globals.get(s);
    }

    public void declareFunction(Sym s) {
	declareConst(s);
    }

    // only valid after defineFunction() called.
    public boolean isFunction(Sym s) {
	return funcs.containsKey(s);
    }

    public void defineFunction(Sym f, Expr T, Expr t) {
	funcs.put(f,t);
	types.put(f,T);
    }

    public Expr getType(Sym s) {
	return (Expr)types.get(s);
    }
 
    public void setSubst(Sym s1, Sym s2) {
	if (s1 == s2)
	    return;
	subst.put(s1,s2);
    }

    public Sym getSubst(Sym s) {
	return (Sym)subst.get(s);
    }

    public static class InitH {
	public Sym init;
	public FunType F;
	public String code;
	public InitH(Sym init, FunType F, String code) {
	    this.init = init;
	    this.F = F;
	    this.code = code;
	}
    }

    protected String name(String n) {
	int iend = n.length() + 1;
	char[] buf = new char[iend];
	buf[0] = 'g';
	for (int i = 1; i < iend; i++) {
	    char c = n.charAt(i-1);
	    if (c <= 47) 
		c += 65;
	    else if (c >= 58 && c <= 64)
		c += 97-58;
	    if ((c >= 91 && c <= 94) || c == 96)
		c += 104-91;
	    else if (c >= 123)
		c -= 4;
	    buf[i] = c;
	}
	return new String(buf);
    }

    /* return the pos of a previously added FunType iff we already had one
       registered for this pair of scrut_tp, pat_var_tp. */
    public Position addInit(Sym init, Sym scrut_tp, Sym pat_var_tp, FunType F, String code) {
	boolean ret = false;
	HashMap m = (HashMap)inits.get(scrut_tp);
	if (m == null) {
	    m = new HashMap(256);
	    inits.put(scrut_tp,m);
	}
	InitH h = (InitH)m.get(pat_var_tp);
	if (h != null)
	    return h.F.pos;
	
	h = new InitH(init,F,code);
	m.put(pat_var_tp,h);
	return null;
    }

    public InitH getInit(Sym scrut_tp, Sym pat_var_tp) {
	HashMap m = (HashMap)inits.get(scrut_tp);
	if (m == null) 
	    return null;
	return (InitH)m.get(pat_var_tp);
    }

    public static class RefStat {
	public Sym ref;
	public boolean created; // if false, it means the ref was dropped
	public Position pos; // if dropped, where
	public RefStat(Sym ref, boolean created, Position pos) {
	    this.ref = ref;
	    this.created = created;
	    this.pos = pos;
	}
    }

    public void checkpointRefs() {
	checkpoint_refs = new HashMap(refs);
	changed_refs = new Vector();
    }

    // return a Collection of RefStats for refs whose status changed since last checkpoint or restore operation.
    public Collection restoreRefs() {
	Vector cur_stat = new Vector();
	HashSet included = new HashSet(256);
	Iterator it = changed_refs.iterator();
	while (it.hasNext()) {
	    Sym r = (Sym)it.next();
	    if (included.contains(r))
		continue;
	    included.add(r);
	    cur_stat.add(refs.get(r));
	}

	changed_refs = new Vector();
	refs = checkpoint_refs;

	return cur_stat;
    }

    /* create a new reference and add it to the refs data structure(s).
       The position is the one to associate with the new reference. */
    public Sym newRef(Position p) {
	String name = "reference-"+(new Integer(refnum++)).toString();
	Sym r = new Sym(name);
	r.pos = p;
	RefStat s = new RefStat(r,true,null);
	refs.put(r, s);
	changed_refs.add(r);
	return r;
    }

    public Sym newVar(Position p) {
	String name = "tmp-"+(new Integer(varnum++)).toString();
	Sym r = new Sym(name);
	r.pos = p;
	return r;
    }

    // x is pinning y1 ... yn.  We updated both the pinning and pinnedby data structures.
    public void pin(Sym x, Sym[] y) {
	HashSet v = (HashSet)pinning.get(x);
	if (v == null) {
	    v = new HashSet();
	    pinning.put(x,v);
	}
	for (int i = 0, iend = y.length; i < iend; i++) {
	    v.add(y[i]);
	    HashSet u = (HashSet)pinnedby.get(y[i]);
	    if (u == null) {
		u = new HashSet();
		pinnedby.put(y[i],u);
	    }
	    u.add(x);
	}
    }

    public boolean isPinning(Sym r) {
	HashSet v = (HashSet)pinning.get(x);
	if (v == null) 
	    return false;
	return (v.size() > 0);
    }

    public Position wasDropped(Sym r) {
	RefStat s = (RefStat)refs.get(r);
	if (s == null)
	    return null;
	return s.pos;
    }

    /* drop the given reference, returning a Collection of references
       that r is currently by.  Any references that r is pinning will
       no longer be pinned by r after this method returns. 

       The given position states where in the code r is being dropped.

       This function does not check to see if r was already dropped.
    */
    public Collection dropRef(Sym r, Position p) {
	HashSet v = (HashSet)pinnedby.get(r);
	HashSet u = (HashSet)pinning.get(r);
	if (u != null) {
	    // r was pinning some references, so we should update pinnedby for them.
	    Iterator it = u.iterator();
	    while(it.hasNext()) {
		HashSet q = (HashSet)pinnedby.get((Sym)it.next());
		q.remove(r);
	    }
	}
	RefStat s = new RefStat(r,false,p);
	refs.put(r,s);
	changed_refs.add(r);
	return v;
    }
    
}