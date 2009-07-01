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
    protected HashMap typeDefs;
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

    public PrintStream cw;
    public String file_suffix;
    public Stack open_files;

    Sym voidref;
    Sym returnf;
    Sym zerof;    

    protected HashMap name_tbl;

    protected Vector global_inits;
    public int stage;
    public int type_num;
    public boolean alloc_committed;

    protected Vector new_typedefs;

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
	typeDefs = new HashMap(256);
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

	voidref = newInternal("done");
	declareConst(voidref);
	setType(voidref,new Void());

	returnf = newInternal("return");
	zerof = newInternal("0");

	name_tbl = new HashMap(2048);

	global_inits = new Vector();

	cw = null;
	open_files = new Stack();

	stage = 0;
	type_num = 1; // we assume elsewhere that this is 1

	alloc_committed = false;

	new_typedefs = new Vector();
    }

    // set the file for emitted code.  Do not mix with pushFile().
    public String setFile(java.io.File f) {
	try {
	    cw = new PrintStream(new BufferedOutputStream(new FileOutputStream(f)));
	}
	catch(FileNotFoundException e) {
	    return new String("Could not open the included file.");
	}
	if (getFlag("output_ocaml"))
	    cw.println("(* produced by carraway *)\n");
	else {
	    cw.println("// produced by carraway\n");
	    cw.println("#include <stdio.h>\n");
	    cw.println("#include <stdlib.h>\n");
	}
	return null;
    }


    // return an error message if there was a problem opening the compiler output file determined by f.
    public String pushFile(String f) {
	if (f.length() < 3)
	    return new String("The included file name is too short.");
	String suf = f.substring(f.length() - 2, f.length());
	if (!suf.equals(file_suffix))
	    return new String("The included file does not end with the expected suffix."
			      +"\n\n1. the expected suffix: "+file_suffix
			      +"\n\n2. the file name: "+f);
	
	String new_suf = (getFlag("output_ocaml") ? ".ml" : ".c");
	String n = f.substring(0, f.length() - 2) + new_suf;
	
	if (cw != null) {
	    if (getFlag("output_ocaml"))
		cw.println("(* Including "+n+" *)");
	    else
		cw.println("#include \""+n+"\"");
	    cw.flush();
	}
	if (!getFlag("output_ocaml") || cw == null) {
	    open_files.push(cw);
	    try {
		cw = new PrintStream(new BufferedOutputStream(new FileOutputStream(n)));
	    }
	    catch(FileNotFoundException e) {
		return new String("Could not open the included file.");
	    }
	    if (getFlag("output_ocaml"))
		cw.println("(* produced by carraway *)\n");
	    else {
		cw.println("// produced by carraway\n");
		cw.println("#include <stdio.h>\n");
		cw.println("#include <stdlib.h>\n");
	    }
	}

	return null;
    }

    public void popFile() {
	if (!getFlag("output_ocaml")) {
	    cw.close();
	    cw = (PrintStream)open_files.pop();
	}
    }

    public void commentBox(String s) {
	if (getFlag("output_ocaml"))
	    cw.print("(");
	else
	    cw.print("/");
	cw.println("*********************************************************");
	cw.println(" * "+s);
	cw.print(" *********************************************************");
	if (getFlag("output_ocaml"))
	    cw.print(")");
	else
	    cw.print("/");	
	cw.println("");
    }

    public void addGlobalInit(String init_func_name) {
	global_inits.add(init_func_name);
    }

    public Collection getGlobalInits() {
	return global_inits;
    }

    public void declareConst(Sym s) {
	if (getFlag("debug_symbols")) {
	    w.println("Carraway context: declaring constant: "+s.toString(this));
	    w.flush();
	}

	String n = s.name;
	consts.put(n,s);	
    }

    public void addResourceType(Sym s, Sym drop) {
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

    public boolean isResourceType(Sym s) {
	return attrs.containsKey(s);
    }

    public Sym getDropFunction(Sym s) {
	return (Sym)attrs.get(s);
    }

    public Sym lookup(String name) {
	if (vars.containsKey(name)) {
	    Stack S = (Stack)vars.get(name);
	    if (S != null && !S.empty())
		return (Sym)S.peek();
	}
	if (consts.containsKey(name))
	    return (Sym)consts.get(name);
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
		!isGlobal(s) && !isResourceType(s) && !isFunction(s));
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

    // return opaque datatypes
    public Collection getDatatypes1() {
	return dels.keySet();
    }

    // return datatypes with ctors
    public Collection getDatatypes2() {
	return tpctors.keySet();
    }

    public void addDatatype(Sym tp, Sym del) {
	declareConst(tp);
	dels.put(tp,del);
	types.put(tp,new Type());
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

    public void addTypeDef(Sym s, Expr T) {
	declareConst(s);
	typeDefs.put(s,T);
    }

    public boolean isTypeDef(Sym s) {
	return typeDefs.containsKey(s);
    }

    public Expr getTypeDefBody(Sym s) {
	return (Expr)typeDefs.get(s);
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
	boolean must_consume_scrut;
	public InitH(Sym init, FunType F, boolean must_consume_scrut, String code) {
	    this.init = init;
	    this.F = F;
	    this.code = code;
	    this.must_consume_scrut = must_consume_scrut;
	}
    }

    public String name(Sym s) {
	return name(s.name);
    }

    public String name(String n) {
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

    protected String unique(String name) {
	//	System.out.print(name+" uniquifies to ");
	Integer I = (Integer)name_tbl.get(name);
	if (I == null) {
	    // haven't added this name before
	    
	    name_tbl.put(name,new Integer(1));
	}
	else {
	    String suffix;
	    int i = I.intValue();
	    if (i == 0)
		// this means we already made this unique
		return name;
	    do {
		suffix = "_"+(new Integer(i++)).toString();
	    }		
	    while (name_tbl.containsKey(name+suffix));

	    name_tbl.put(name,new Integer(i));
	    name = name+suffix;
	    name_tbl.put(name,new Integer(0));
	}
	
	//	System.out.println(name);

	return name;
    }

    // for symbols from the input.
    public Sym newSym(String n, Position p) {
	String un = unique(name(n));

	if (getFlag("debug_symbols")) {
	    w.println("Carraway context: creating symbol \""+n+"\", with output name \""+un+"\".");
	    w.flush();
	}

	Sym r = new Sym(n, un);
	r.pos = p;
	return r;
    }	

    public Sym newSym(String n) {
	return newSym(n,null);
    }

    public Sym newInternal(String n) {
	Sym s = new Sym(n,n);
	return s;
    }

    public Sym newVar(Position p) {
	return newSym("carraway_tmp",p);
    }


    /* return the pos of a previously added FunType iff we already had one
       registered for this pair of scrut_tp, pat_var_tp. */
    public Position addInit(Sym init, Sym scrut_tp, Sym pat_var_tp, FunType F, 
			    boolean must_consume_scrut, String code) {
	boolean ret = false;
	HashMap m = (HashMap)inits.get(scrut_tp);
	if (m == null) {
	    m = new HashMap(256);
	    inits.put(scrut_tp,m);
	}
	InitH h = (InitH)m.get(pat_var_tp);
	if (h != null)
	    return h.F.pos;
	
	h = new InitH(init,F,must_consume_scrut,code);
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
	public boolean non_ret;
	public boolean consume;
	public HashSet pinning;
	public HashSet pinnedby;
	public Position creating_pos; // in case creating_expr is a Sym.
	public Expr creating_expr;
	public Expr dropping_expr;
	public Position dropping_pos;
	protected RefStat(RefStat u) {
	    ref = u.ref;
	    non_ret = u.non_ret;
	    consume = u.consume;
	    pinning = new HashSet(u.pinning);
	    pinnedby = new HashSet(u.pinnedby);
	    creating_pos = u.creating_pos;
	    creating_expr = u.creating_expr;
	    dropping_expr = u.dropping_expr;
	    dropping_pos = u.dropping_pos;
	}
	protected RefStat(Sym ref, Position creating_pos, Expr creating_expr, 
			  Position dropping_pos, Expr dropping_expr, 
			  boolean non_ret, boolean consume) {
	    this.ref = ref;
	    this.non_ret = non_ret;
	    this.consume = consume;
	    this.creating_pos = creating_pos;
	    this.creating_expr = creating_expr;
	    this.dropping_expr = dropping_expr;
	    this.dropping_pos = dropping_pos;
	    pinning = new HashSet(256);
	    pinnedby = new HashSet(256);
	}
	public void print(java.io.PrintStream w, Context ctxt) {
	    w.println("  -- "+ref.toString(ctxt));
	    w.println("     created by "+creating_expr.toString(ctxt)+" at "+creating_pos.toString());
	    if (non_ret)
		w.println("     not to be returned.");
	    else
		w.println("     can be returned.");
	    if (dropping_expr == null)
		w.println("     not dropped yet.");
	    else {
		w.println("     dropped by "+dropping_expr.toString(ctxt));
		if (dropping_pos != null)
		    w.println(" at "+dropping_pos.toString());
	    }

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
	return newSym("reference",p);
    }

    /* create a new reference and add it to the refs data structure(s).
       The position is the one to associate with the new reference. */
    public Sym newRef(Expr e, Position p, boolean non_ret, boolean consume) {
	Sym r = new_ref(p);
	RefStat s = new RefStat(r,p,e,null,null,non_ret,consume);
	refs.put(r, s);
	changed_refs.add(r);
	if (getFlag("debug_refs")) 
	    s.print(w,this);
	return r;
    }

    public Sym newRef(Expr e) {
	return newRef(e,e.pos,false,true);
    }

    public Sym newRef(Expr e, Position p) {
	return newRef(e,p,false,true);
    }

    public Sym newRef(Position p, RefStat data) {
	Sym r = new_ref(p);
	RefStat s = new RefStat(r,p,data.creating_expr,data.dropping_pos,
				data.dropping_expr,data.non_ret,data.consume);
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
	if (s == null || s.dropping_expr == null)
	    return null;
	return s.dropping_expr.pos;
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
    public Collection dropRef(Sym r, Expr e, Position p) {
	if (r == voidref)
	    return null;
	if (getFlag("debug_refs")) {
	    w.println("Dropping "+r.refString(this));
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

	uu.dropping_expr = e;
	uu.dropping_pos = p;

	changed_refs.add(r);
	return uu.pinnedby;
    }
 
}