package guru.carraway;
import guru.Position;
import java.util.Collection;
import java.util.Iterator;
import java.util.HashSet;
import java.util.HashMap;
import java.util.Stack;

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
    protected HashSet refs;
    protected HashMap dropped;

    protected int refnum;

    public Context() {
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
	refs = new HashSet(256);
	dropped = new HashMap(256);
	
	refnum = 0;
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
	return tpctors.containsKey(tp);
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

    /* create a new reference and add it to the refs data structure.
       The position is the one to associate with the new reference. */
    public Sym newRef(Position p) {
	String name = "reference-"+(new Integer(refnum++)).toString();
	Sym r = new Sym(name);
	r.pos = p;
	refs.add(r);
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

    public Position wasDropped(Sym r) {
	return (Position)dropped.get(r);
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
	dropped.put(r,p);
	return v;
    }
    
}