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
    protected HashMap attrs;
    protected HashMap primitives;
    protected HashMap inits;
    protected HashMap dels;
    protected HashSet not_consumed;

    protected HashMap refs;
    protected Vector changed_refs;
    protected Stack refs_stack;
    protected Stack changed_refs_stack;
    protected int refnum;

    protected int varnum;

    protected String cur_file;
    public PrintStream cw;
    public String file_suffix;

    Sym voidref;

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
	attrs = new HashMap(256);
	primitives = new HashMap(256);
	inits = new HashMap(256);
	dels = new HashMap(256);
	not_consumed = new HashSet(256);

	refs = new HashMap(256);
	changed_refs = new Vector();
	refs_stack = new Stack();
	changed_refs_stack = new Stack();
	refnum = 0;
	varnum = 0;

	voidref = new Sym("voidref");
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

    public void addAttribute(Sym s, Sym drop) {
	declareConst(s);
	setType(s,new Type());
	attrs.put(s,drop);
    }

    public boolean isNotConsumed(Sym x) {
	return not_consumed.contains(x);
    }

    public void setNotConsumed(Sym x) {
	not_consumed.add(x);
    }

    public boolean isAttribute(Sym s) {
	return attrs.containsKey(s);
    }

    public Sym getDropFunction(Sym s) {
	return (Sym)attrs.get(s);
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
	if (getFlag("debug_primitives")) {
	    w.println("adding primitive "+s.toString(this));
	    w.flush();
	}
	declareConst(s);
	types.put(s,T);
	primitives.put(s,code);
    }

    public void addDatatype(Sym tp, Sym del) {
	declareConst(tp);
	dels.put(tp,del);
    }

    public Sym getDeleteFunction(Sym s) {
	return (Sym)dels.get(s);
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
	if (getFlag("debug_subst")) {
	    w.println(s1.toString(this) + " |--> " + (s2 == null ? "null" : s2.toString(this)));
	    w.flush();
	}
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

    public Sym newVar(Position p) {
	String name = "tmp_"+(new Integer(varnum++)).toString();
	Sym r = new Sym(name);
	r.pos = p;
	return r;
    }

    public static class RefStat {
	public Sym ref;
	public boolean created; // if false, it means the ref was dropped
	public Position pos; // if dropped, where
	public boolean non_ret;
	public boolean consume;
	public HashSet pinning;
	public HashSet pinnedby;
	public RefStat(RefStat u) {
	    ref = u.ref;
	    created = u.created;
	    pos = u.pos;
	    non_ret = u.non_ret;
	    consume = u.consume;
	    pinning = new HashSet(u.pinning);
	    pinnedby = new HashSet(u.pinnedby);
	}
	public RefStat(Sym ref, boolean created, Position pos, boolean non_ret, boolean consume) {
	    this.ref = ref;
	    this.created = created;
	    this.pos = pos;
	    this.non_ret = non_ret;
	    this.consume = consume;
	    pinning = new HashSet(256);
	    pinnedby = new HashSet(256);
	}
	public RefStat(Sym ref, boolean created, Position pos) {
	    this.ref = ref;
	    this.created = created;
	    this.pos = pos;
	    this.non_ret = false;
	    this.consume = true;
	    pinning = new HashSet(256);
	    pinnedby = new HashSet(256);
	}
	public void print(java.io.PrintStream w, Context ctxt) {
	    w.println("  -- "+ref.toString(ctxt));
	    w.println("     created at "+ref.posToString());
	    if (non_ret)
		w.println("     not to be returned.");
	    else
		w.println("     can be returned.");
	    w.println("     current status: "+(created ? "created" : "dropped at "+pos.toString()));
	    Iterator it = pinning.iterator();
	    w.print("     pinning:");
	    while(it.hasNext()) {
		Sym r = (Sym)it.next();
		w.print(" ");
		r.print(w,ctxt);
	    }
	    w.println("");

	    w.print("     pinned by:");
	    it = pinnedby.iterator();
	    while(it.hasNext()) {
		Sym r = (Sym)it.next();
		w.print(" ");
		r.print(w,ctxt);
	    }
	    w.println("");
	    
	    w.flush();
	}
	public String toString(Context ctxt) {
	    java.io.ByteArrayOutputStream s = new java.io.ByteArrayOutputStream();
	    java.io.PrintStream w = new java.io.PrintStream(s);
	    print(w,ctxt);
	    return s.toString();
	}
    }

    protected HashMap clone_refs(HashMap c) {
	HashMap h = new HashMap(256);
	Iterator it = c.keySet().iterator();
	while (it.hasNext()) {
	    Sym r = (Sym)it.next();
	    h.put(r,new RefStat((RefStat)c.get(r)));
	}
	return h;
    }

    public void checkpointRefs() {
	if (getFlag("debug_refs")) {
	    w.println("checkpointing references (");
	    w.flush();
	}
	refs_stack.push(clone_refs(refs));
	changed_refs_stack.push(new Vector(changed_refs));
	changed_refs = new Vector();
    }

    // return a Collection of RefStats for refs whose status changed since last checkpoint operation.
    public Collection restoreRefs() {
	if (getFlag("debug_refs")) {
	    w.println(") restoring references.  Changed references are:");
	    w.flush();
	}
	Vector cur_stat = new Vector();
	HashSet included = new HashSet(256);
	Iterator it = changed_refs.iterator();
	while (it.hasNext()) {
	    Sym r = (Sym)it.next();
	    if (included.contains(r))
		continue;
	    included.add(r);
	    RefStat u = (RefStat)refs.get(r);
	    if (getFlag("debug_refs")) 
		u.print(w,this);
	    cur_stat.add(u);
	}

	changed_refs = (Vector)changed_refs_stack.pop();
	refs = (HashMap)refs_stack.pop();

	return cur_stat;
    }

    protected Sym new_ref(Position p) {
	String name = "reference_"+(new Integer(refnum++)).toString();
	Sym r = new Sym(name);
	r.pos = p;
	return r;
    }

    /* create a new reference and add it to the refs data structure(s).
       The position is the one to associate with the new reference. */
    public Sym newRef(Position p, boolean non_ret, boolean consume) {
	Sym r = new_ref(p);
	RefStat s = new RefStat(r,true,null,non_ret,consume);
	refs.put(r, s);
	changed_refs.add(r);
	if (getFlag("debug_refs")) 
	    s.print(w,this);
	return r;
    }

    public Sym newRef(Position p) {
	return newRef(p,false,true);
    }

    public Sym newRef(Position p, RefStat data) {
	Sym r = new_ref(p);
	RefStat s = new RefStat(r,true,null,data.non_ret,data.consume);
	s.pinning = new HashSet(data.pinning);
	s.pinnedby = new HashSet(data.pinnedby);
	refs.put(r, s);
	changed_refs.add(r);
	if (getFlag("debug_refs")) 
	    s.print(w,this);
	return r;
    }

    // x is pinning y1 ... yn.  We updated both the pinning and pinnedby data structures.
    public void pin(Sym x, Sym[] y) {
	RefStat v = (RefStat)refs.get(x);
	if (v == null) 
	    x.simulateError(this, "Internal error: trying to pin by a non-existent reference: "+x.refString(this));
	for (int i = 0, iend = y.length; i < iend; i++) {
	    v.pinning.add(y[i]);
	    RefStat u = (RefStat)refs.get(y[i]);
	    if (u == null) 
		y[i].simulateError(this, "Internal error: trying to pin a non-existent reference: "+y[i].refString(this)
				   +"\n\n1. pinning by: "+x.refString(this));
	    u.pinnedby.add(x);
	}
    }

    public boolean isPinning(Sym r) {
	RefStat v = (RefStat)refs.get(r);
	if (v == null) 
	    return false;
	return (v.pinning.size() > 0);
    }

    public Position wasDropped(Sym r) {
	RefStat s = (RefStat)refs.get(r);
	if (s == null)
	    return null;
	return s.pos;
    }

    public RefStat refStatus(Sym r) {
	return (RefStat)refs.get(r);
    }

    /* drop the given reference, returning a Collection of references
       that r is currently pinned by.  Any references that r is
       pinning will no longer be pinned by r after this method
       returns.

       The given position states where in the code r is being dropped.

       This function does not check to see if r was already dropped.
    */
    public Collection dropRef(Sym r, Position p) {
	if (r == voidref)
	    return null;
	if (getFlag("debug_refs")) {
	    w.println("Dropping "+r.toString(this));
	    w.println("  1. created at: "+r.posToString());
	    w.println("  2. dropped at: "+p.toString()+"\n");
	    w.flush();
	}
	RefStat uu = (RefStat)refs.get(r);
	if (uu == null)
	    r.simulateError(this,"Internal error: attempting to drop a non-existent reference: "+r.toString(this));

	// r was pinning some references, so we should update pinnedby for them.
	Iterator it = uu.pinning.iterator();
	while(it.hasNext()) {
	    Sym r1 = (Sym)it.next();
	    RefStat vv = (RefStat)refs.get(r1);
	    if (vv == null)
		r1.simulateError(this,"Internal error: attempting to unpin a non-existent reference: "+r1.toString(this));
	    vv.pinnedby.remove(r);
	}

	uu.created = false;
	uu.pos = p;

	changed_refs.add(r);
	return uu.pinnedby;
    }
    
}