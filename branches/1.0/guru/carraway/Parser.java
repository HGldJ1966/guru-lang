package guru.carraway;
import guru.Position;
import java.io.*;
import java.util.*;

/** The main method is readCommand().  You need to open a file and
    set a Context before reading commands. */
public class Parser extends guru.ParserBase {
    
    Context ctxt;

    public Parser(boolean trusted) {
	super();
	ctxt = null;
    }
    
    public void Reset() {
	super.Reset();
	ctxt = null;
    }	

    public void setContext(Context ctxt)
    {
       this.ctxt = ctxt;
    }

    public Command readCommand() throws IOException
    {
	if (!eat_ws())
	    return null;
	Position pos = getPos();
	Command c = null;
	if (tryToEat("ResourceType")) 
	    c = readAttribute();
	else if (tryToEat("Primitive")) 
	    c = readPrimitive();
	else if (tryToEat("Datatype"))
	    c = readDatatype();
	else if (tryToEat("Init"))
	    c = readInit();
	else if (tryToEat("Global"))
	    c = readGlobal();
	else if (tryToEat("Function"))
	    c = readFunction();
        else if (tryToEat("Set"))
            c = readSet();
        else if (tryToEat("Unset"))
            c = readUnset();
	else if (tryToEat("Include"))
	    c = readInclude();
	else
	    handleError("Unexpected start of a command.");
	c.pos = pos;
	return c;
    }

    protected Attribute readAttribute() throws IOException {
	Attribute a = new Attribute();
	a.s = readIdentifier(true);
	
	ctxt.declareConst(a.s);

	eat("with", "ResourceType");
	a.drop = readPrimitive();
	
	return a;
    }

    protected Primitive readPrimitive() throws IOException {
	Primitive a = new Primitive();
	a.s = readIdentifier(true);
	eat(":","Primitive");
	a.T = readType();
	eat("<<","Primitive");
	a.delim = readID();
	a.code = read_until_newline_delim(a.delim);
	return a;
    }

    protected Init readInit() throws IOException {
	Init a = new Init();
	a.init = readPrimitive();
	return a;
    }

    protected Global readGlobal() throws IOException {
	Global a = new Global();
	a.c = readIdentifier(true);
	eat(":=", "Global");
	a.t = readTerm();
	eat(".","Global");
	return a;
    }

    protected Datatype readDatatype() throws IOException {
	Datatype c = new Datatype();
	c.tp = readIdentifier(true);
	ctxt.declareConst(c.tp); // for benefit of run-time types
	eat_ws();

	if (tryToEat("with")) 
	    c.del = readPrimitive();
	else {
	    eat(":=","Datatype");
	    boolean first = true;
	    int cur = 0;
	    ArrayList ctors = new ArrayList();
	    ArrayList types = new ArrayList();
	    while (true) {
		eat_ws();
		if (tryToEat("."))
		break;
		if (first)
		    first = false;
		else
		    eat("|","Datatype");
		ctors.add(readIdentifier(true));
		eat(":","Datatype");
		
		types.add(readCtorType());
	    }
	    
	    int iend = ctors.size();
	    c.ctors = new Sym[iend];
	    c.types = new Expr[iend];
	    c.rttypes = new Expr[iend];
	    for (int i = 0; i < iend; i++) {
		c.ctors[i] = (Sym)ctors.get(i);
		CtorType d = (CtorType)types.get(i);
		c.types[i] = d.T;
		c.rttypes[i] = d.R;
	    }
	}
	return c;
    }

    protected Set readSet() throws IOException
    {
	Set s = new Set();
	if (!eat_ws())
	    handleError("Unexpected end of input reading a Set-command.");

	s.flag = readString();

	eat(".", "Set");

	return s;
    }

    protected Unset readUnset() throws IOException
    {
	Unset s = new Unset();
	if (!eat_ws())
	    handleError("Unexpected end of input reading an Unset-command.");

	s.flag = readString();

	eat(".", "Unset");

	return s;
    }
    
    protected Include readInclude() throws IOException
    {
	if (!eat_ws())
	    handleError("Unexpected end of input parsing a Include.");
	Include cmd = new Include(new File(readString()), root);
	eat(".", "Include");
	return cmd;
    }

    static public Sym[] toSymArray(ArrayList a) {
	int iend = a.size();
	Sym[] v = new Sym[iend];
	for (int i = 0; i < iend; i++)
	    v[i] = (Sym)a.get(i);
	return v;
    }

    static public Expr[] toExprArray(ArrayList a) {
	int iend = a.size();
	Expr[] v = new Expr[iend];
	for (int i = 0; i < iend; i++)
	    v[i] = (Expr)a.get(i);
	return v;
    }

    /*
    static public Case[] toCaseArray(ArrayList a) {
	int iend = a.size();
	Case[] v = new Case[iend];
	for (int i = 0; i < iend; i++)
	    v[i] = (Case)a.get(i);
	return v;
    }
    */

    protected Sym readIdentifier (boolean binding_occurrence) 
	throws IOException
    {
        Position pos = getPos();
	
	if (!eat_ws())
	    handleError("Expected an identifier");

        String name = readID();

	Sym v = ctxt.lookup(name);	
	if (!binding_occurrence) {
	    if (v != null)
		return v;
	    handleError(pos, "Undeclared symbol \""+name+"\"");
	}

	v = ctxt.newSym(name,pos);
	return v;
    }

    protected Expr readPin() throws IOException 
    {
	Pin p = new Pin();
	p.s = readIdentifier(false);
	ArrayList a = new ArrayList();
	while(true) {
	    eat_ws();
	    if (tryToEat(">"))
		break;
	    a.add(readIdentifier(false));
	}
	int iend = a.size();

	p.pinned = new Sym[iend];
	for (int i = 0; i < iend; i++) 
	    p.pinned[i] = (Sym)a.get(i);

	return p;
    }

    static public class CtorType {
	public Expr T,R;
	public CtorType(Expr T, Expr R) {
	    this.T = T;
	    this.R = R;
	}
    }

    public CtorType readCtorType() throws IOException {
	int construct = eatKeyword();
	Expr T = null;
	Expr R = null;
	Position pos = getPos();
	switch(construct)
            {
	    case Expr.SYM: 
		T = readIdentifier(false);
		R = T;
		break;
	    case Expr.UNTRACKED: 
		T = new Untracked();
		R = T;
		break;
	    case Expr.FUN_TYPE: {
		CtorType c = readCtorFunType();
		T = c.T;
		R = c.R;
		break;
	    }
	    default:
		handleError("Expected a type for a constructor.");
            }
	if (T.pos == null)
	    T.pos = pos;
	if (R.pos == null)
	    R.pos = pos;
	return new CtorType(T,R);
    }

    public Expr readType() throws IOException {
	int construct = eatKeyword();
	Expr e = null;
	Position pos = getPos();
	switch(construct)
            {
	    case Expr.SYM:
		e = readIdentifier(false);
		break;
	    case Expr.PIN:
		e = readPin();
		break; 
	    case Expr.FUN_TYPE:
		e = readFunType();
		break;
	    case Expr.UNTRACKED:
		e = new Untracked();
		break;
	    case Expr.TYPE:
		e = new Type();
		break;
	    case Expr.VOID:
		e = new Void();
		break;
	    default:
		handleError("Expected a type.");
            }
	if (e.pos == null)
	    e.pos = pos;
	return e;
    }

    public Expr readTerm() throws IOException {
	int construct = eatKeyword();
	Expr e = null;
	Position pos = getPos();
	switch(construct)
            {
	    case Expr.SYM:
		e = readIdentifier(false);
		break;
	    case Expr.CAST:
		e = readCast();
		break;
	    case Expr.APP:
		e = readApp();
		break;
	    case Expr.ABORT:
		e = new Abort();
		break;
	    case Expr.LET:
		e = readLet();
		break;
	    case Expr.MATCH:
		e = readMatch();
		break; 
	    case Expr.DO:
		e = readDo();
		break; 
	    case Expr.COMPRESS:
		e = readCompress();
		break; 
	    default:
		handleError("Expected a type.");
            }
	if (e.pos == null)
	    e.pos = pos;
	return e;
    }

    protected Compress readCompress() throws IOException {
	Compress c = new Compress();
	c.t = readTerm();
	return c;
    }

    protected Do readDo() throws IOException {
	ArrayList a = new ArrayList();
	Do e = new Do();
	while(true) {
	    eat_ws();
	    if (tryToEat("end"))
		break;
	    a.add(readTerm());
	}
	
	int iend = a.size();
	if (iend < 2)
	    handleError("A do-term has fewer than two subterms.");
	Expr[] ts = new Expr[iend];
	for (int i = 0; i < iend; i++) 
	    ts[i] = (Expr)a.get(i);
	e.ts = ts;
	return e;
    }

    protected Cast readCast() throws IOException {
	Cast c = new Cast();
	c.T = readType();
	c.t = readTerm();
	return c;
    }

    protected App readApp() throws IOException {
	App a = new App();
	a.head = readIdentifier(false);
	ArrayList args = new ArrayList();

	while(true) {
	    eat_ws();
	    if (tryToEat(")"))
		break;
	    args.add(readTerm());
	}
	int iend = args.size();
	a.args = new Expr[iend];
	for (int i = 0; i < iend; i++)
	    a.args[i] = (Expr)args.get(i);
	return a;
    }

    protected Let readLet() throws IOException {
	Let c = new Let();
	c.x = readIdentifier(true);
	ctxt.pushVar(c.x);
	eat("=","let-term");
	c.t1 = readTerm();
	eat("in","let-term");
	c.t2 = readTerm();
	ctxt.popVar(c.x);
	return c;
    }

    protected void readInputs(ArrayList vars, ArrayList types, ArrayList rttypes, ArrayList consumps,
			      String where, boolean ctortype) 
	throws IOException 
    {
	while(true) {
	    eat_ws();
	    if (tryToEat("."))
		break;
	    eat("(",where);

	    eat_ws();
	    if (ctortype) 
		consumps.add(new Integer(FunBase.CONSUMED_RET_OK));
	    else {
		if (tryToEat("!")) 
		    consumps.add(new Integer(FunBase.NOT_CONSUMED));
		else if (tryToEat("^")) 
		    consumps.add(new Integer(FunBase.CONSUMED_NO_RET));
		else 
		    consumps.add(new Integer(FunBase.CONSUMED_RET_OK));
	    }   
	    
	    Sym s = readIdentifier(true);
	    ctxt.pushVar(s);
	    vars.add(s);
	    
	    eat(":",where);

	    Expr T = readType();
	    types.add(T);

	    if (ctortype) {
		if (T.construct != Expr.FUN_TYPE && T.construct != Expr.TYPE && T.construct != Expr.UNTRACKED) {
		    eat("&",where);
		    rttypes.add(readIdentifier(false));
		}
		else 
		    rttypes.add(new Untracked());
	    }

	    eat(")",where);
	}
    }

    protected FunType readFunType() throws IOException
    {
        FunType e = new FunType();
	ArrayList vars = new ArrayList();
	ArrayList types = new ArrayList();
	ArrayList consumps = new ArrayList();

	readInputs(vars,types,null,consumps,"Fun-type",false);

        e.rettype = readType();

	int iend = vars.size();

	e.vars = new Sym[iend];
	e.types = new Expr[iend];
	e.consumps = new int[iend];

	Sym v;
	for (int i = 0; i < iend; i++) {
	    v = e.vars[i] = (Sym)vars.get(i);
	    e.types[i] = (Expr)types.get(i);
	    e.consumps[i] = ((Integer)consumps.get(i)).intValue();
	    ctxt.popVar(v);
	}

        return e;
    }

    protected CtorType readCtorFunType() throws IOException
    {
        FunType e1 = new FunType();
        FunType e2 = new FunType();
	ArrayList vars = new ArrayList();
	ArrayList types = new ArrayList();
	ArrayList rttypes = new ArrayList();
	ArrayList consumps = new ArrayList();

	readInputs(vars,types,rttypes,consumps,"Fun-type",true);

        e1.rettype = e2.rettype = readIdentifier(false);

	int iend = vars.size();

	Sym[] _vars = e1.vars = e2.vars = new Sym[iend];
	Expr[] _types = e1.types = new Expr[iend];
	Expr[] _rttypes = e2.types = new Expr[iend];
	int[] _consumps = e1.consumps = e2.consumps = new int[iend];

	Sym v;
	for (int i = 0; i < iend; i++) {
	    v = _vars[i] = (Sym)vars.get(i);
	    _types[i] = (Expr)types.get(i);
	    _rttypes[i] = (Expr)rttypes.get(i);
	    _consumps[i] = ((Integer)consumps.get(i)).intValue();
	    ctxt.popVar(v);
	}

        return new CtorType(e1,e2);
    }

    protected Case readCase() throws IOException
    {
	Case e = new Case();
	Position p = getPos();
	e.c = readIdentifier(false);
	if (!ctxt.isCtor(e.c))
	    handleError("The head of a pattern in a match-case is not a constructor.\n\n"
			+"1. the head: "+e.c.toString(ctxt));
	ArrayList vars = new ArrayList();
	while(true) {
	    eat_ws();
	    if (tryToEat("=>"))
		break;
	    Sym v = readIdentifier(true);
	    vars.add(v);
	    ctxt.pushVar(v);
	}
	e.body = readTerm();

	int iend = vars.size();

	e.vars = new Sym[iend];

	Sym v;
	for (int i = 0; i < iend; i++) {
	    v = e.vars[i] = (Sym)vars.get(i);
	    ctxt.popVar(v);
	}
	e.pos = p;
	e.lastpos = getPos();
        return e;
    }

    protected Match readMatch() throws IOException
    {
	Match e = new Match();
	eat_ws();
	e.consume_first = tryToEat("$");
	e.t = readTerm();
	eat("with","match-term");
	ArrayList cases = new ArrayList();
	boolean first = true;
	while(true) {
	    eat_ws();
	    if (tryToEat("end"))
		break;
	    if (first)
		first = false;
	    else
		eat("|","match-term");
	    cases.add(readCase());
	}

	int iend = cases.size();

	if (iend == 0)
	    handleError("A match-term has no cases.");

	e.C = new Case[iend];

	for (int i = 0; i < iend; i++) 
	    e.C[i] = (Case)cases.get(i);

        return e;
    }

    protected Function readFunction() throws IOException
    {
        Function e = new Function();
	ArrayList vars = new ArrayList();
	ArrayList types = new ArrayList();
	ArrayList consumps = new ArrayList();

	e.t = new FunTerm();
	e.t.pos = getPos();
	e.t.f = readIdentifier(true);
	ctxt.declareFunction(e.t.f);
	readInputs(vars,types,null,consumps,"Function",false);

        e.t.rettype = readType();

	eat(":=","Function");

	e.t.body = readTerm();

	eat(".","Function");

	int iend = vars.size();

	e.t.vars = new Sym[iend];
	e.t.types = new Expr[iend];
	e.t.consumps = new int[iend];

	Sym v;
	for (int i = 0; i < iend; i++) {
	    v = e.t.vars[i] = (Sym)vars.get(i);
	    e.t.types[i] = (Expr)types.get(i);
	    e.t.consumps[i] = ((Integer)consumps.get(i)).intValue();
	    ctxt.popVar(v);
	}

        return e;
    }



    protected int eatKeyword() throws IOException
    {
        if (!eat_ws())
	    return Expr.INVALID;

	if (tryToEat("cast"))
	    return Expr.CAST;
	if (tryToEat("("))
	    return Expr.APP;
	if (tryToEat("abort"))
	    return Expr.ABORT;
	if (tryToEat("let")) 
	    return Expr.LET;
	if (tryToEat("match"))
	    return Expr.MATCH;
	if (tryToEat("Fun"))
	    return Expr.FUN_TYPE;
	if (tryToEat("untracked"))
	    return Expr.UNTRACKED;
	if (tryToEat("void"))
	    return Expr.VOID;
	if (tryToEat("do"))
	    return Expr.DO;
	if (tryToEat("type"))
	    return Expr.TYPE;
	if (tryToEat("<"))
	    return Expr.PIN;
	if (tryToEat("@"))
	    return Expr.COMPRESS;

	if (tryToEat(")"))
	    handleError("Unexpected punctuation.");

	return Expr.SYM;
    }
}

