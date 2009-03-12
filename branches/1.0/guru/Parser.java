package guru;
import java.io.*;
import java.util.*;

/** The main method is readCommand().  You need to open a file and
    set a Context before reading commands. */
public class Parser extends ParserBase {
    
    Context ctxt;
    boolean trusted;

    protected final static int STRING = 1;

    boolean allow_stars, allow_type_fam_abbrev, allow_predicate, spec;

    protected static final boolean using_metavars = false;

    public Parser(boolean trusted) {
	super();
	ctxt = null;
	allow_stars = false;
	allow_type_fam_abbrev = false;
	this.trusted = trusted;
    }
    
    public void Reset() {
	super.Reset();
	allow_stars = false;
	ctxt = null;
	allow_type_fam_abbrev = false;
    }	

    protected boolean isTerm(int construct) {
	switch(construct) {
	case Expr.STAR:
	case Expr.STARSTAR:
	    if (!allow_stars)
		handleError("A star is being used outside a context");
	    return true;
	case Expr.TYPE_APP:
	    if (allow_type_fam_abbrev) {
		allow_type_fam_abbrev = false;
		return true;
	    }
	    return false;
	case Expr.LAST+STRING:
	    return true;
	}

	if (Expr.isFormula(construct) && allow_predicate) {
	    allow_predicate = false;
	    return true;
	}

	return Expr.isTerm(construct);
    }

    protected boolean isTypeOrKind(int construct) {
	switch(construct) {
	case Expr.STAR:
	case Expr.STARSTAR:
	    if (!allow_stars)
		handleError("A star is being used outside a context");
	    return true;
	}
	return Expr.isTypeOrKind(construct);
    }

    protected boolean isProof(int construct) {
	switch(construct) {
	case Expr.STAR:
	case Expr.STARSTAR:
	    if (!allow_stars)
		handleError("A star is being used outside a context");
	    return true;
	}
	return Expr.isProof(construct);
    }

    protected boolean isFormula(int construct) {
	switch(construct) {
	case Expr.STAR:
	case Expr.STARSTAR:
	    if (!allow_stars)
		handleError("A star is being used outside a context.");
	    return true;
	}
	return Expr.isFormula(construct);
    }

    protected boolean isX(int construct) {
	return (isProof(construct) ||
		isTerm(construct) || isTypeOrKind(construct));
    }

    protected boolean isY(int construct) {
	return (isTypeOrKind(construct) || isTerm(construct));
    }

    protected boolean isA(int construct) {
	return ((construct == Expr.TYPE) || 
		isTypeOrKind(construct) || 
		isFormula(construct));
    }

    public void setContext(Context ctxt)
    {
       this.ctxt = ctxt;
    }

    public Expr readAny() throws IOException {
	return readAny(eatKeyword());
    }

    // call with value from eatKeyword() 
    public Expr readAny(int construct) throws IOException {
	Expr e = null;
	Position pos = getPos();
	switch(construct)
            {
	    case Expr.VAR:
		e = readIdentifier(false);
		break;
	    case Expr.BANG:
		e = new Bang();
		break;
	    case Expr.STAR:
		e = ctxt.star;
		break;
	    case Expr.STARSTAR:
		e = ctxt.starstar;
		break;
	    case Expr.FUN_TERM:
		e = readFunTerm();
		break;
	    case Expr.CAST:
		e = readCast();
		break;
	    case Expr.TERMINATES:
		e = readTerminates();
		break;
	    case Expr.TERM_APP:
		e = readTermApp();
		break;
	    case Expr.ABORT:
		e = readAbort();
		break;
	    case Expr.LET:
		e = readLet();
		break;
	    case Expr.ABBREV:
	    case Expr.EABBREV:
	    	e = readAbbrev(construct == Expr.EABBREV);
 		break;
	    case Expr.MATCH:
		e = readMatch();
		break;
	    case Expr.FUN_TYPE:
		e = readFunType();
		break;
	    case Expr.INC:
		e = readInc();
		break;
	    case Expr.DEC:
		e = readDec();
		break;
	    case Expr.TYPE:
		e = ctxt.type;
		break;
	    case Expr.TYPE_APP:
		e = readTypeApp();
		break;
	    case Expr.PRED_APP:
		e = readPredApp();
		break;
	    case Expr.FORALLI:
		e = readForalli();
		break;
	    case Expr.PROOF_APP:
		e = readProofApp();
		break;
	    case Expr.CASE_PROOF:
		e = readCaseProof();
		break;
	    case Expr.EXISTSI:
		e = readExistsi();
		break;
	    case Expr.ANDI:
		e = readAndi();
		break;
	    case Expr.EXISTSE_TERM:
		e = readExistseTerm();
		break;
	    case Expr.EXISTSE:
		e = readExistse();
		break;
	    case Expr.JOIN:
		e = readJoin();
		break;
	    case Expr.EVAL:
		e = readEval();
		break;
	    case Expr.EVALTO:
		e = readEvalto();
		break;
	    case Expr.HYPJOIN:
		e = readHypJoin();
		break;
	    case Expr.REFL:
	    	e = readRefl();
		break;
	    case Expr.SYMM:
		e = readSymm();
		break;
	    case Expr.TRANS:
		e = readTrans();
		break;
	    case Expr.CONG:
		e = readCong();
		break;
	    case Expr.NCONG:
		e = readNcong();
		break;
	    case Expr.INJ:
		e = readInj();
		break;
	    case Expr.CLASH:
		e = readClash();
		break;
	    case Expr.ACLASH:
		e = readAclash();
		break;
	    case Expr.INV:
		e = readInv();
		break;
	    case Expr.SUBST:
		e = readSubst();
		break;
	    case Expr.CONTRA:
		e = readContra();
		break;
	    case Expr.INDUCTION:
		e = readInduction();
		break;
	    case Expr.SHOW:
		e = readShow();
		break;
	    case Expr.FORALL:
		e = readForall();
		break;
	    case Expr.EXISTS:
		e = readExists();
		break;
	    case Expr.ATOM:
		e = readAtom();
		break;
	    case Expr.METAVAR:
		e = readMetaVar();
		break;
	    case Expr.TRUE:
	    	e = readTrue();
		break;
	    case Expr.FALSE:
	    	e = readFalse();
		break;
	    case Expr.TRUEI:
	    	e = readTruei();
		break;
	    case Expr.DISEQI:
	    	e = readDiseqi();
		break;
	    case Expr.CUTOFF:
		e = readCutoff();
		break;
	    case Expr.CIND:
		e = readCind();
		break;
	    case Expr.IMPOSSIBLE:
		e = readImpossible();
		break;
	    case Expr.SIZE:
		e = readSize();
		break;
	    case Expr.LAST+STRING:
		e = readStringExpr();
		break;
	    default:
		handleError("Internal error: missing case for construct");
            }
	if (e.pos == null)
	    e.pos = pos;
	return e;
    }

    // return either a Command or null if we are at the end of the file
    public Command readCommand() throws IOException
    {
	allow_stars = false;
	if (!eat_ws())
	    return null;
	Position pos = getPos(); 
	Command c = null;
	if (tryToEat("Define")) 
	    c = readDefine();
	else if (tryToEat("CheckTrusted")) 
	    c = new CheckTrusted();
	else if (tryToEat("Inductive"))
	    c = readInductive();
	else if (tryToEat("Set"))
	    c = readSet();
	else if (tryToEat("Unset"))
	    c = readUnset();
	else if (tryToEat("Include"))
	    c = readInclude();
	else if (tryToEat("Compile"))
	    c = readCompile();
	else if (tryToEat("Interpret")) 
	    c = readInterpret();
	else if (tryToEat("Classify")) 
	    c = readClassifyCmd();
	else if (tryToEat("Untracked")) 
	    c = readUntracked();
        else if (tryToEat("DumpDependence"))
            c = readDumpDependence();
        else if (tryToEat("Total"))
            c = readTotal();
        else if (tryToEat("Echo"))
            c = readEcho();
	else
	    handleError("Unexpected start of a command.");
	c.pos = pos;
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

    protected Total readTotal() throws IOException
    {
	Total s = new Total();
	if (!eat_ws())
	    handleError("Unexpected end of input reading a Total-command.");

	s.c = readConst();

	if (!eat_ws())
	    handleError("Unexpected end of input reading a Total-command.");
	s.P = readProof();

	eat(".", "Total");

	return s;
    }

    protected True readTrue() throws IOException
    {
    	True t = new True();
	return t;
	
    }
    
    protected False readFalse() throws IOException
    {
    	False t = new False();
	return t;
	
    }
    
    protected Truei readTruei() throws IOException
    {
    	Truei t = new Truei();
	return t;
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
    
    

    protected Define readDefine() throws IOException
    {
	Define cmd = new Define();
	
	if (!eat_ws())
	    handleError("Unexpected end of input parsing a Define.");

	cmd.spec = false;
	cmd.trusted = trusted;
	cmd.type_family_abbrev = false;
	cmd.predicate = false;
	cmd.abbrev = false;

	// read the various flags that can be given to Define.
	while (true) {
	    
	    if (tryToEat("spec")) {
		cmd.spec = true;
		spec = true;
	    }
	    else if (tryToEat("trusted"))
		cmd.trusted = true;
	    else if (tryToEat("type_family_abbrev")) {
		cmd.type_family_abbrev = true;
		allow_type_fam_abbrev = true;
	    }
	    else if (tryToEat("predicate")) {
		cmd.predicate = true;
		allow_predicate = true;
	    }
	    else if (tryToEat("abbrev")) {
		cmd.abbrev = true;
	    }
	    else
		break; // out of while loop
	    
	    if (!eat_ws())
		handleError("Unexpected end of input parsing a Define.");
	}

	cmd.c = readBindingConst();
	
	if (!tryToEat(":="))
	{
	    eat(":", "Define");
	    if (!eat_ws())
		handleError("Unexpected end of input parsing a Define.");
	    cmd.A = readA();
	    eat(":=", "Define"); 
	}
	
	if (!eat_ws())
	    handleError("Unexpected end of input parsing a Define.");

	if (allow_type_fam_abbrev && allow_predicate) 
	    handleError("A defined constant cannot be both a type family\n"
			+"abbreviation and a predicate.");

	cmd.G = readAny();

	allow_type_fam_abbrev = false;
	allow_predicate = false;
	spec = false;

	eat(".", "Define");

	return cmd;
    }

    
    protected Interpret readInterpret() throws IOException
    {
    	Interpret cmd = new Interpret();
	if (!eat_ws())
	    handleError("Unexpected end of input parsing an Interpret.");
	cmd.t = readTerm();
	eat(".", "Interpret");
    	return cmd;
    }

    protected ClassifyCmd readClassifyCmd() throws IOException
    {
    	ClassifyCmd cmd = new ClassifyCmd();
	if (!eat_ws())
	    handleError("Unexpected end of input parsing an Interpret.");
	cmd.G = readAny();
	eat(".", "Type");
    	return cmd;
    }

    protected Untracked readUntracked() throws IOException
    {
    	Untracked cmd = new Untracked();
	if (!eat_ws())
	    handleError("Unexpected end of input parsing an Untracked.");
	cmd.d = readConst();
	eat(".", "Untracked");
    	return cmd;
    }
    protected DumpDependence readDumpDependence() throws IOException
    {
        DumpDependence cmd = new DumpDependence();
        if (!eat_ws() || !tryToEat("to") || !eat_ws())
	    handleError("Unexpected end of input parsing a DumpDependence.");
        cmd.outfile = readString();
        if (!eat_ws())
	    handleError("Unexpected end of input parsing a DumpDependence.");
        if (tryToEat("track")) {
            if (!eat_ws())
                handleError("Unexpected end of input parsing a DumpDependence.");
            do {
                int c;
                if ((c = getc()) == -1)
                    handleError("Unexpected end of input parsing a DumpDependence `track' clause.");
                ungetc(c);
                if (c == '"') {
                    cmd.trackFile(root, readString());
                } else {
                    cmd.trackID(readID());
                }
                if (!eat_ws())
                    handleError("Unexpected end of input parsing a DumpDependence `track' clause.");
            } while(!tryToEat("end"));
            if (!eat_ws())
                handleError("Unexpected end of input parsing a DumpDependence.");
        }
        if (tryToEat("limit")) {
            if (!eat_ws() || !tryToEat("to") || !eat_ws())
                handleError("Unexpected end of input parsing a DumpDependence `limit' clause.");
            do {
                int c;
                if ((c = getc()) == -1)
                    handleError("Unexpected end of input parsing a DumpDependence `limit' clause.");
                ungetc(c);
                if (c == '"') {
                    cmd.limitFile(root, readString());
                } else {
                    cmd.limitID(readID());
                }
                if (!eat_ws())
                    handleError("Unexpected end of input parsing a DumpDependence `limit' clause.");
            } while(!tryToEat("end"));
            if (!eat_ws())
                handleError("Unexpected end of input parsing a DumpDependence.");
        }
        eat(".", "DumpDependence");
        return cmd;
    }
    protected Compile readCompile() throws IOException
    {
    	Compile c = new Compile();
	
	if (!eat_ws())
		 handleError("Unexpected end of input reading an Compile-command.");
    	
	c.cmain = readConst();
	eat("to ","Compile");
	c.f = new File(readString());
	c.root = root;
	eat(".", "Compile");
	return c;
    
    }
   
    protected Expr readStringExpr() throws IOException {
	ungetc('\"');
	return new StringExpr(readString());
    }
 
    protected Include readInclude() throws IOException
    {
	boolean t = trusted;
	if (!eat_ws())
	    handleError("Unexpected end of input parsing a Include.");
	if (tryToEat("trusted")) {
	    t = true;
	    if (!eat_ws())
		handleError("Unexpected end of input parsing a Include.");
	}
	Include cmd = new Include(new File(readString()), root);
	cmd.trusted = t;
	eat(".", "Include");
	return cmd;
    }

    protected Echo readEcho() throws IOException
    {
	Echo cmd = new Echo();
	if (!eat_ws())
	    handleError("Unexpected end of input parsing a Include.");
	cmd.s = readString();
	eat(".", "Echo");
	return cmd;
    }
    
    protected Inductive readInductive()
	throws IOException
    {
	Inductive cmd = new Inductive();
	if (!eat_ws())
	    handleError("Unexpected end of input parsing an Inductive.");
	cmd.d = readBindingConst();

	eat(":", "Inductive");
	Position p = getPos();
	cmd.K = readKind();
	cmd.K.pos = p;
	ctxt.addTypeCtor(cmd.d, cmd.K);
	eat(":=", "Inductive");
	if (!eat_ws())
	    handleError("Unexpected end of input parsing an Inductive");
	int c = getc();
	ArrayList cs = new ArrayList();
	ArrayList Ds = new ArrayList();
	while ((char)c != '.') {
	    ungetc(c);
            Const cst = readBindingConst();
	    cs.add(cst);
	    eat(":", "Inductive");
	    p = getPos();
	    Expr D = readD(cmd.d);
	    D.pos = p;
	    Ds.add(D);
	    if (!eat_ws())
		handleError("Unexpected end of input parsing an Inductive");
	    if (!tryToEat("|")) {
		eat(".", "Inductive");
		break; // out of while 
	    }
	    if (!eat_ws())
		handleError("Unexpected end of input parsing an Inductive");
	    c = getc();
	}

	cmd.c = toConstArray(cs);
	cmd.D = toExprArray(Ds);

	return cmd;
    }

    // read a D expression, whose return type should be a d-type.
    protected Expr readD(Const d) throws IOException 
    {
	Expr ee = readType();
	
	Expr ret = null;
	if (ee.construct == Expr.FUN_TYPE) {
	    FunType e = (FunType)ee;

	    for (int i = 0, iend = e.vars.length; i < iend; i++) {
		Expr T = e.types[i];
		if (!isAminus(T))
		    handleError("Expected an A- expression in the type of a "
				+"term constructor");
		if (e.owned[i].status == Ownership.OWNEDBY)
		    handleError("A term constructor is being declared with"
				+" a type\nusing an \"owned\" annotation.\n"
				+"1. the type: "+e.toString(ctxt));

		if (T.isdtype(ctxt,true))
		    continue;

		if (T.numOcc(d) > 0)
		    handleError("An input type for a term constructor uses"
				+" the corresponding type constructor in a"
				+" disallowed way:"
				+"\n1. the type: "+T.toString(ctxt));
	    }
	    ret = e.body;
	}
	else
	    ret = ee;
	if (!isdtypeRestricted(ret,d))
	    handleError("The return type of a term constructor is not a \""+
			d.name+"\"-type.");
        return ee;
    }

    protected boolean isdtypeRestricted(Expr e, Const d) {
	return e.numOcc(d) == 1 && e.isdtype(ctxt, d);
    }

    protected boolean isAminus(Expr e) {
	int construct = e.construct;
	if (construct == Expr.TYPE || isTypeOrKind(construct)
	    || Expr.isFormula(construct)) 
	    return true;
	return false;
    }

    protected boolean isB(int construct) {
	return (construct == Expr.TYPE || isTypeOrKind(construct));
    }

    protected Expr readX() throws IOException
    {
	int construct = eatKeyword();
	if (!isX(construct))
	    handleError("Expected a term, type, or proof.");
        return readAny(construct);
    }
    
    protected Expr readY() throws IOException
    {
	int construct = eatKeyword();
	if (!isY(construct))
	    handleError("Expected a term, type, or proof.");
        return readAny(construct);
    }
    
    protected Expr readI() throws IOException
    {
        Expr e = readX();
	if (!e.isI(ctxt))
	    handleError("Expected an injective expression.");
        return e;
    }

    protected Expr readEstar() throws IOException
    {
	allow_stars = true;

	Expr e = readX();

	allow_stars = false;

	if (!isE(e, true /* permissive */, true /* disallow_starstar */)
	    && !isEhat(e, true /* disallow_starstar */))
	    handleError("A context is neither an extended evaluation context"
			+" nor a permissive one.");

        return e;
    }

    protected boolean isE(Expr e, boolean permissive, 
			  boolean disallow_starstar) {
	int num_starstar = e.numOcc(ctxt.starstar);
	if (disallow_starstar && num_starstar > 0)
	    return false;

	boolean tmp;
	if (permissive)
	    tmp = (e.numOcc(ctxt.star) + num_starstar >= 1);
	else
	    tmp = (e.numOcc(ctxt.star) + num_starstar == 1);
	
	return tmp && isEHelper(e,permissive);
    }

    // return true iff we find a star or starstar, looking according to
    // either evaluation order or permissive evaluation order.  
    protected boolean isEHelper(Expr ee, boolean permissive) {
	int construct = ee.construct;
	switch(construct) {
	case Expr.STAR:
	case Expr.STARSTAR:
	    return true;
	case Expr.TERM_APP: {
	    App e = (App) ee;
	    if (isEHelper(e.head, permissive))
		return true;
	    if (!permissive && !e.head.isI(ctxt))
		return false;
	    for (int i = 0, iend = e.X.length; i < iend; i++) {
		if (isEHelper(e.X[i], permissive))
		    return true;
		if (!permissive && !e.X[i].isI(ctxt))
		    return false;
	    }
	    return false;
	}
	case Expr.LET: {
	    Let e = (Let) ee;
	    return isEHelper(e.t1, permissive);
	}
	case Expr.ABBREV: {
	    Abbrev e = (Abbrev) ee;
	    return isEHelper(e.subst, permissive);
	}
	case Expr.MATCH: {
	    Match e = (Match)ee;
	    return isEHelper(e.t, permissive);
	}
	}
	return false;
    }

    protected boolean isEhatHelper(Expr ee) {
	int construct = ee.construct;
	switch(construct) {
	case Expr.STAR:
	case Expr.STARSTAR:
	case Expr.VAR:
	    return true;
	case Expr.TYPE_APP: {
	    App e = (App) ee;
	    if (!isEhatHelper(e.head))
		return false;
	    for (int i = 0, iend = e.X.length; i < iend; i++) 
		if (!isEhatHelper(e.X[i]))
		    return false;
	    return true;
	}
	case Expr.TYPE:
	    return true;
	case Expr.FUN_TYPE: {
	    FunType e = (FunType)ee;
	    for (int i = 0, iend = e.vars.length; i < iend; i++)
		if (!isEhatHelper(e.types[i]))
		    return false;
	    return isEhatHelper(e.body);
	}	  
	}

	boolean nostars = (ee.numOcc(ctxt.star) == 0
			   && ee.numOcc(ctxt.starstar) == 0);
	if (isFormula(construct))
	    return nostars;

	if (isTerm(construct))
	    return nostars || isE(ee,true /* permissive */, 
				  false /* disallow starstar */);

	return false;
    }

    protected boolean isEhat(Expr e, boolean disallow_starstar) {
	if (disallow_starstar && e.numOcc(ctxt.starstar) > 0)
	    return false;
	    
	return e.numOcc(ctxt.star) == 1 && isEhatHelper(e);
    }

    // return true iff e satisfies the condition needed to be an
    // injective extended evaluation context, assuming it is an
    // extended evaluation context.
    protected boolean alsoIhat(Expr ee) {
	int construct = ee.construct;
	switch(construct) {
	case Expr.STAR:
	case Expr.STARSTAR:
	case Expr.VAR:
	    return true;
	case Expr.TYPE_APP: {
	    App e = (App) ee;
	    if (!alsoIhat(e.head))
		return false;
	    for (int i = 0, iend = e.X.length; i < iend; i++) 
		if (!alsoIhat(e.X[i]))
		    return false;
	    return true;
	}
	case Expr.TYPE:
	    return true;
	case Expr.FUN_TYPE: {
	    FunType e = (FunType)ee;
	    for (int i = 0, iend = e.vars.length; i < iend; i++)
		if (!alsoIhat(e.types[i]))
		    return false;
	    return alsoIhat(e.body);
	}	  
	}
 
	if (isFormula(construct))
	    return true; // already checked nostars in isEhatHelper()

	if (isTerm(construct)) {
            ee = ee.subst(ctxt.tmpvar,ctxt.starstar);
            ee = ee.subst(ctxt.tmpvar,ctxt.star);
            return ee.isI(ctxt);
        }

	return false;
    }

    protected Expr readIhat(boolean single_hole) throws IOException
    {
	allow_stars = true;

	Expr e = readX();

	allow_stars = false;

	if (!isEhat(e, single_hole /* disallow_starstar */))
	    handleError("An extended evaluation context is not well-formed");

	if (!alsoIhat(e))
	    handleError("An extended evaluation context is not injective.");

        return e;
    }
    
    protected Expr readA() throws IOException
    {
        int construct = eatKeyword();
	if (!isA(construct))
	    handleError("Expected a type, formula, or \"type\"");
	return readAny(construct);
    }

    protected Expr readFormula() throws IOException
    {
        int construct = eatKeyword();
	boolean isvar = construct == Expr.VAR;
	if (!isFormula(construct) && !isvar)
	    handleError("Expected a formula");
	Expr ret = readAny(construct);
	if (isvar)
	    // need to watch out for macro-defined vars here.
	    if (!ret.isFormula(ctxt))
		handleError("Expected a formula");
	return ret;
    }
        
    protected Expr readFhat() throws IOException
    {
	allow_stars = true;
        Expr e = readFormula();
	allow_stars = false;
	
	if (e.numOcc(ctxt.starstar) > 0)
	    handleError("\"**\" is disallowed in a formula context");

	return e;
    }
        
    protected Expr readTerm() throws IOException
    {
	int construct = eatKeyword();
	if (!isTerm(construct))
	    handleError("Expected a term");
	return readAny(construct);
    }
    
    protected Expr readProof() throws IOException
    {
	int construct = eatKeyword();
	if (!isProof(construct))
	    handleError("Expected a proof");
	return readAny(construct);
    }

    protected Expr readType() throws IOException
    {
	int construct = eatKeyword();
	if (!isTypeOrKind(construct))
	    handleError("Expected a type");
	return readAny(construct);
    
    }

    protected Expr readKind() throws IOException
    {
	int construct = eatKeyword();
	if (construct == Expr.TYPE)
	    return ctxt.type;
	if (construct != Expr.FUN_TYPE)
	    handleError("Expected a kind");

        FunType e = new FunType();

	readVarListExpr(e, false);
	int iend = e.vars.length;
	e.owned = new Ownership[e.vars.length];
	for (int i = 0; i < iend; i++)
	    e.owned[i] = new Ownership(Ownership.NOT_TRACKED);
        eat(".", "kind");
        e.body = readKind();
	e.ret_stat = new Ownership(Ownership.NOT_TRACKED);
	popVars(e);

	for (int i = 0; i < iend; i++)
	    if (!isB(e.types[i].construct))
		handleError("The kind of a type constructor has an input which"
			    +" is not a B expression");

        return e;
    }

    static public Var[] toVarArray(ArrayList a) {
	int iend = a.size();
	Var[] v = new Var[iend];
	for (int i = 0; i < iend; i++)
	    v[i] = (Var)a.get(i);
	return v;
    }

    static public Const[] toConstArray(ArrayList a) {
	int iend = a.size();
	Const[] v = new Const[iend];
	for (int i = 0; i < iend; i++)
	    v[i] = (Const)a.get(i);
	return v;
    }

    static public Expr[] toExprArray(ArrayList a) {
	int iend = a.size();
	Expr[] v = new Expr[iend];
	for (int i = 0; i < iend; i++)
	    v[i] = (Expr)a.get(i);
	return v;
    }

    static public Case[] toCaseArray(ArrayList a) {
	int iend = a.size();
	Case[] v = new Case[iend];
	for (int i = 0; i < iend; i++)
	    v[i] = (Case)a.get(i);
	return v;
    }

    static public Ownership[] toOwnershipArray(ArrayList a) {
	int iend = a.size();
	Ownership[] v = new Ownership[iend];
	for (int i = 0; i < iend; i++)
	    v[i] = (Ownership)a.get(i);
	return v;
    }

    protected Case readCase(boolean in_match) throws IOException
    {
        Case e = new Case();
	e.pos = getPos();
        
	String errm = ("Pattern in case does not begin with a"
		       +" known constant.");
	try {
	    e.c = readConst();
	    if (!ctxt.isTermCtor(e.c)) {
		handleError(errm);
	    }
	}
	catch (ClassCastException ee) {
	    handleError(errm);
	}

        if (!eat_ws())
	    handleError("Unexpected end of input parsing a case.");
        
	ArrayList vars = new ArrayList();
	while (!tryToEat("=>")) {
	    vars.add(readBindingVar());
	    if (!eat_ws())
		handleError("Unexpected end of input parsing a case.");
	}
	    
	if (!eat_ws())
	    handleError("Unexpected end of input parsing a case.");

	e.x = toVarArray(vars);
	int iend = e.x.length;

	for (int i = 0; i < iend; i++)
	    ctxt.pushVar(e.x[i]);

	if (in_match)
	    e.body = readTerm();
	else
	    // we are in an induction proof
	    e.body = readProof();
        
	for (int i = 0; i < iend; i++)
	    ctxt.popVar(e.x[i]);

        return e;
    }
    

    protected ProofApp readProofApp () throws IOException
    {
        ProofApp e = new ProofApp();
        ArrayList theT = new ArrayList();
        
        e.head = readProof();

        theT.add(readX());
        
	if (!eat_ws())
	    handleError("Unexpected end of input parsing a case in a proof"
			+" application.");
        
        while(!tryToEat("]"))
        {
            theT.add(readX());
        
	    if (!eat_ws())
		handleError("Unexpected end of input parsing a proof"
			    +" application.");
        }
        
        e.X = toExprArray(theT);
        
        return e;
    }
    
    protected TypeApp readTypeApp () throws IOException
    {
        TypeApp e = new TypeApp();
        ArrayList xList = new ArrayList();
        
	e.head = readType();

	if (!eat_ws())
	    handleError("Unexpected end of input parsing a type"
			+" application.");
        
        while(!tryToEat(">"))
        {
	    if (!eat_ws())
		handleError("Unexpected end of input parsing a type"
			    +" application.");
        
            xList.add(readX());
        
	    if (!eat_ws())
		handleError("Unexpected end of input parsing a type"
			    +" application.");
        }
        
        e.X = toExprArray(xList);
        
        return e;
    }

    protected PredApp readPredApp () throws IOException
    {
        PredApp e = new PredApp();
        ArrayList xList = new ArrayList();
        
	e.head = readConst();

	if (!eat_ws())
	    handleError("Unexpected end of input parsing a predicate"
			+" application.");
        
        while(!tryToEat(">"))
        {
	    if (!eat_ws())
		handleError("Unexpected end of input parsing a predicate"
			    +" application.");
        
            xList.add(readX());
        
	    if (!eat_ws())
		handleError("Unexpected end of input parsing a predicate"
			    +" application.");
        }
        
        e.X = toExprArray(xList);
        
        return e;
    }
    
    protected TermApp readTermApp () throws IOException
    {
        ArrayList xList = new ArrayList();
        ArrayList sList = new ArrayList();

        Expr head = readTerm();

	if (!eat_ws())
	    handleError("Unexpected end of input parsing a term"
			+" application.");
        
        while(!tryToEat(")"))
        {
	    if (!eat_ws())
		handleError("Unexpected end of input parsing a term"
			    +" application.");
            
	    boolean spec = false;
	    if (tryToEat("spec")) {
		spec = true;
		if (!eat_ws())
		    handleError("Unexpected end of input parsing a term"
				+" application.");
            }

	    xList.add(readX());
	    sList.add(new Boolean(spec));

	    if (!eat_ws())
		handleError("Unexpected end of input parsing a term"
			    +" application.");
        }
        return new TermApp(head, toExprArray(xList), toBooleanArray(sList));
    }
    
    protected Atom readAtom () throws IOException
    {
        Atom e = new Atom();
        
	e.Y1 = readY();
        
	if (!eat_ws())
	    handleError("Unexpected end of input parsing an atomic formula");

	if (tryToEat("="))
	    e.equality = true;
	else if (tryToEat("!="))
	    e.equality = false;
	else
	    handleError("Expecting \"=\" or \"!=\" in an atomic formula");

	e.Y2 = readY();
        
	eat("}", "atomic formula");

        return e;
    }

    protected Match readMatch() throws IOException
    {
        Match e = new Match();

        e.t = readTerm();
        
	readAssumpVars(e);

	if (tryToEat("return"))
	{
	    if (!eat_ws())
		handleError("Unexpected end of input parsing a match term.");
	    
	    e.T = readType();
	}
	
	if (e.x1 != null) {
	    ctxt.pushVar(e.x1);
	    ctxt.pushVar(e.x2);
	}

        e.C = readCases(true);
	
	if (e.x1 != null) {
	    ctxt.popVar(e.x1);
	    ctxt.popVar(e.x2);
	}

        return e;
    }
    
    // but not for induction-proofs.
    protected void readAssumpVars(CasesExpr e) throws IOException {
	e.x1 = null;
	e.x2 = null;

	String errstr = "Unexpected end of input parsing assumption vars.";

	if (!eat_ws())
	    handleError(errstr);

	if (tryToEat("by")) {
	    if (!eat_ws())
		handleError("Unexpected end of input parsing a match term.");
	    
	    Position p = getPos();
	    e.x1 = readBindingVar();
	    e.x1.pos = p;
	    
	    if (!eat_ws())
		handleError("Unexpected end of input parsing a match term.");
	    
	    p = getPos();
	    e.x2 = readBindingVar();
	    e.x1.pos = p;

	    if (!eat_ws())
		handleError("Unexpected end of input parsing a match term.");
	}
	else {
	    if (e.t.construct == Expr.VAR || e.t.construct == Expr.CONST) {
		String n = 
		    (e.t.construct == Expr.VAR ? ((Var)e.t).name
		     : ((Const)e.t).name);
		e.x1 = new Var(n+"_eq");
		e.x2 = new Var(n+"_Eq");
		Position p = getPos();
		e.x1.pos = p;
		e.x2.pos = p;
	    }
	}
    }
	

    protected CaseProof readCaseProof() throws IOException
    {
        CaseProof e = new CaseProof();

        e.t = readTerm();
        
	readAssumpVars(e);

	if (e.x1 == null) 
	    handleError("A case-proof lacks a \"by\" clause, and we"
			+" cannot automatically declare\n"
			+"its variables, since the scrutinee is not"
			+" a variable.");

	ctxt.pushVar(e.x1);
	ctxt.pushVar(e.x2);

        e.C = readCases(false);
	
	ctxt.popVar(e.x1);
	ctxt.popVar(e.x2);

        return e;
    }
    
    protected Induction readInduction() throws IOException
    {
        Induction e = new Induction();
        
	e.vl = new VarListExpr(Expr.INDUCTION); 

        readVarListExpr(e.vl, false);
        
	String errstr = "Unexpected end of input parsing an induction proof.";

	if (!eat_ws())
	    handleError(errstr);

	if (tryToEat("by")) {
	    
	    if (!eat_ws())
		handleError(errstr);

	    e.x1 = readBindingVar();
	    
	    if (!eat_ws())
		handleError(errstr);
        
	    e.x2 = readBindingVar();
	    
	    if (!eat_ws())
		handleError(errstr);

	    e.x3 = readBindingVar();
	}
	else {
	    String ind_var = e.vl.vars[e.vl.vars.length-1].name;
	    e.x1 = new Var(ind_var + "_eq");
	    e.x2 = new Var(ind_var + "_Eq");
	    e.x3 = new Var(ind_var + "_IH");
	}

	eat("return", "induction proof");

	if (!eat_ws())
	    handleError("Unexpected end of input parsing a match term.");
	
	e.F = readFormula();
	
	ctxt.pushVar(e.x1);
	ctxt.pushVar(e.x2);
	ctxt.pushVar(e.x3);

        e.C = readCases(false);

	ctxt.popVar(e.x1);
	ctxt.popVar(e.x2);
	ctxt.popVar(e.x3);

        popVars(e.vl);

	return e;
    }
    
    // read a list of cases, and check that the constructors are
    // the ones for a single datatype, in that order.
    protected Case[] readCases(boolean in_match) throws IOException {
        ArrayList cList = new ArrayList();
	String where = in_match ? "match term" : "induction or case proof";

	eat("with", where);
        
	if (!eat_ws())
	    handleError("Unexpected end of input parsing "+where+".");

	Expr adefault = null;
	Const tp = null;
	
	boolean first = true;
	if (tryToEat("default")) {
	    /* special case construct where we have a default value
	       for all cases not given subsequently */
	    
	    if (!eat_ws())
		handleError("Unexpected end of input parsing "+where+".");
	    
	    if (!tryToEat("=>")) {
		// read the type, so we know which constructors should be used.
		tp = readConst();
		if (!ctxt.isTypeCtor(tp)) 
		    handleError("A default clause in a "+where+" lists an expression"
				+"\nfor a type or type family, which is not actually such.\n"
				+"1. The expression: "+tp.toString(ctxt));
		if (!eat_ws())
		    handleError("Unexpected end of input parsing "+where+".");

		eat("=>", where);
	    }

	    if (in_match)
		adefault = readTerm();
	    else
		adefault = readProof();

	    if (!eat_ws())
		handleError("Unexpected end of input parsing "+where+".");

	    first = false;
	}

	// now read any other cases given

        while(!tryToEat("end"))
        {
	    if (first)
		first = false;
	    else {
		if (!tryToEat("|"))
		    handleError("Expected '|' parsing "+where+".");
		if (!eat_ws())
		    handleError("Unexpected end of input parsing "+where+".");
	    }

            cList.add(readCase(in_match));
            
	    if (!eat_ws())
		handleError("Unexpected end of input parsing "+where+".");
        }

	if (tp == null) {
	    if (cList.size() == 0) 
		handleError("A "+where+" has no cases, and the default does not list"
			    +"\na type or type family.  Use the syntax \"default <tp> =>\".");
	    Case fst_case = (Case)cList.get(0);
	    tp = (Const)ctxt.getTypeCtor(fst_case.c);
	}

	/* fill in the array "cases" with cases, using adefault if we
	   are missing a case.  Cases must be given in order by ctor. */

	Collection ctors = ctxt.getTermCtors(tp);
	Iterator it = ctors.iterator();

	int num_ctors = ctors.size();
	int num_actual = cList.size();
	Case[] cases = new Case[num_ctors];
	int j = 0;
	for (int i = 0; i < num_ctors; i++) {
	    Const expected_ctor = (Const)it.next();

	    if (j < num_actual) {
		Case actual_case = (Case)cList.get(j);
		
		if (expected_ctor == actual_case.c) {
		    cases[i] = actual_case;
		    j++;
		    continue; // around for loop
		}
	    }

	    /* either we are out of actual cases or the current actual
	       case has a different ctor than expected (in which case
	       we must insert the default). */ 

	    if (j >= num_ctors)
		handleError("A "+where+" appears not to be listing the constructors for"
			    +"\ndatatype \""+tp.toString(ctxt)+"\" in order.");
	    if (adefault == null)
		handleError("A "+where+" appears not to be listing the constructors for"
			    +"\ndatatype \""+tp.toString(ctxt)+"\" in order, or else"
			    +"\na default clause should be used.");
	    Expr ctor_tp = ctxt.getClassifier(expected_ctor);
	    Var[] v = null;
	    if (ctor_tp.construct == Expr.CONST
		|| ctor_tp.construct == Expr.TYPE_APP)
		v = new Var[0];
	    else {
		FunType f = (FunType)ctor_tp;
		v = f.vars;
	    }
	    
	    cases[i] = new Case(expected_ctor, v, adefault, 
				false /* default for impossible */);
	}

	/*
	String msg = ("A "+where+" does not list all the constructors, in"
		      +" the order in which they\nare declared in their"
		      +" datatype, as the patterns of the cases.\n");
	int s = ctxt.checkTermCtors(cs);
	if (s == -2) 
	    handleError(msg + "\nThere is an extra constructor after the "
			+"ones declared for the datatype.");
	else if (s == cs.length)
	    handleError(msg + "\nThe match is apparently missing a case.\n"
			+ "\n1. The actual number of cases: "
			+(new Integer(cs.length)).toString()
			+ "\n2. The expected number: " +
			(new Integer(((List)ctxt.typeCtorsTermCtors.get
				      (ctxt.getTypeCtor(cs[0]))).size())).
			toString());
	else if (s != -1)
	    handleError(msg + "\nThe constructor at position "
			+ (new Integer(s))
			+ " in the list of cases is different\nfrom the "
			+ "declared one at that position."
			+ "\n1. The constructor for the case: "
			+cs[s].toString(ctxt) 
			+ "\n2. The declared constructor: " +
			((Expr)((List)ctxt.typeCtorsTermCtors.get
				(ctxt.getTypeCtor(cs[0]))).get(s))
			.toString(ctxt));
	*/

	return cases;
    }

    protected Let readLet () throws IOException
    {
    	Let e = new Let();
        
	if (!eat_ws())
	    handleError("Unexpected end of input parsing a let term.");

	e.x1_stat = readAnno(false /* we do not allow owned here, for
				      soundness */);

	if (!eat_ws())
	    handleError("Unexpected end of input parsing a let term.");

	e.x1 = readBindingVar();

	eat("=", "let term");
	    
	e.t1 = readTerm();
        
	if (!eat_ws())
	    handleError("Unexpected end of input parsing a let term.");

	if (tryToEat("by")) {
        
	    if (!eat_ws())
		handleError("Unexpected end of input parsing a let term.");

	    e.x2 = readBindingVar();
        }
	else {
	    e.x2 = new Var(e.x1.name+"_eq");
	    e.x2.pos = getPos();
	}

	ctxt.pushVar(e.x2);

	eat("in", "let term");
        
	ctxt.pushVar(e.x1);

        e.t2 = readTerm();

	ctxt.popVar(e.x1);

	ctxt.popVar(e.x2);

        return e;
    }

    protected Abbrev readAbbrev (boolean eabbrev) throws IOException
    {
	Var x;
	Expr U, G;
        Position pos = getPos();

	if (!eat_ws())
	    handleError("Unexpected end of input parsing a abbrev term.");

	x = readBindingVar();

	eat("=", "abbrev term");
	    
	U = readAny();
        
	eat("in", "abbrev term");
        
	ctxt.pushVar(x);
	
	ctxt.macroDefine(x,U); /* we do this now for the benefit
				  of readFormula() */

        G = readAny();
	
	ctxt.popVar(x);
	
        Abbrev ret = new Abbrev(eabbrev, x,U,G);
	ret.pos = pos;
	return ret;
    }
    
    protected Const readBindingConst () throws IOException
    {
	Var v = (Var)readIdentifier(true);
	if (ctxt.lookup(v.name) != null) 
	    handleError("A previous definition or "
			+"declaration is being shadowed.");
	Const c = new Const(v.name);

	c.pos = v.pos;
	return c;
    }

    protected Const readConst () throws IOException
    {
	return (Const)readIdentifier(false);
    }

    /** this is expecting it can definitely read a metavar at this 
	point.  Otherwise, it will throw a class cast exception. */
    protected MetaVar readMetaVar () throws IOException
    {
	return (MetaVar)readIdentifier(false);
    }
    
    protected Var readVar () throws IOException
    {
	return (Var)readIdentifier(false);
    }

    protected Var readBindingVar () throws IOException
    {
	return (Var)readIdentifier(true);
    }

    /** reads an identifier.  */
    protected Expr readIdentifier (boolean binding_occurrence) 
	throws IOException
    {
        Position pos = getPos();
        String theVarName = readID();

	if (theVarName.charAt(0) == '_' && using_metavars) 
	    return new MetaVar(theVarName);

	Expr e = ctxt.lookup(theVarName);	
	if (!binding_occurrence) {
	    if (e != null)
		return e;
	    handleError(pos, "Undeclared variable \""+theVarName+"\"");
	}

	Var v = new Var(theVarName);
	v.pos = pos;
	return v;
    }
     
    protected class VarList {
	public Ownership anno;
	public Var[] vars;
	public Expr type;
    }

    protected Ownership readAnno(boolean allow_owned) throws IOException {
	if (allow_owned && tryToEat("owned"))
	    return new Ownership(Ownership.OWNEDBY);
	if (tryToEat("owned_by"))
	    return new Ownership(Ownership.OWNEDBY,readVar());
	if (allow_owned && tryToEat("unique_owned"))
	    return new Ownership(Ownership.UNIQUE_OWNEDBY);
	if (tryToEat("unique_owned_by"))
	    return new Ownership(Ownership.UNIQUE_OWNEDBY,readVar());
	if (tryToEat("unique"))
	    return new Ownership(Ownership.UNIQUE);
	if (tryToEat("new"))
	    return new Ownership(Ownership.NEW);
	if (tryToEat("spec"))
	    return new Ownership(Ownership.SPEC);
	return new Ownership(Ownership.UNOWNED);
    }

    // if allow_annos is true, we allow certain types of annotations
    // to qualify the vars.
    protected VarList readVarList(boolean allow_annos) throws IOException
    {
        ArrayList varList = new ArrayList();
        Expr type = null;

        eat("(", "variable list");
            
	if (!eat_ws())
	    handleError("Unexpected end of input reading a variable list.");
	Ownership anno = new Ownership(Ownership.UNOWNED);
	if (allow_annos) {
	    anno = readAnno(true /* allow_owned */);
	    if (!eat_ws())
		handleError("Unexpected end of input reading a variable"
			    +" list.");
	}
		
        do
        {        
            varList.add(readBindingVar());

            if (!eat_ws())
		handleError("Unexpected end of input reading a variable"
			    +" list.");
	    if (tryToEat(")")) {
		/* the only way the expr we are reading will type check
		   is if it is a fun-term in an untyped aread -- there
		   is no type given for the variables. */
		type = new Bang();
		break;
	    }
	}
	while(!tryToEat(":"));

	if (!eat_ws())
	    handleError("Unexpected end of input reading a variable list.");

	if (type == null) {
	    type = readA();

	    if (!eat_ws() || !tryToEat(")"))
		handleError("Unexpected end of input reading a variable list.");
	}

	VarList vl = new VarList();
        vl.vars = toVarArray(varList);
	vl.type = type;
	vl.anno = anno;
	
	for (int i = 0, iend = vl.vars.length; i < iend; i++)
	    ctxt.pushVar(vl.vars[i]);

        return vl;
    }
    
    // read var lists until we hit '.' (construct we consume) or '=' (construct
    // we push back).  If allow_annos is true, we allow certain types of
    // annotations to qualify the variables, and we assume e is a 
    // FunAbstraction.
    protected void readVarListExpr(VarListExpr e, boolean allow_annos) 
	throws java.io.IOException 
    {
        ArrayList varList = new ArrayList();
        ArrayList uList = new ArrayList();
        ArrayList annoList = new ArrayList();

        int c;
        char ch;
        
	if (!eat_ws())
	    handleError("Unexpected end of input parsing a variable list.");
        
        c = getc();
        ch = (char) c;
        
        while(ch == '(')
        {
	    ungetc(c);
            VarList vl = readVarList(allow_annos);
            for(int i=0; i<vl.vars.length;i++)
                varList.add(vl.vars[i]);
            for(int i=0; i<vl.vars.length;i++)
                uList.add(vl.type);
	    if (allow_annos)
		for(int i=0; i<vl.vars.length;i++)
		    annoList.add(vl.anno);
        
	    if (!eat_ws())
		handleError("Unexpected end of input parsing a variable"
			    +" list.");
            
            c=getc();
            ch = (char) c;
        }
	ungetc(c);

        e.vars = toVarArray(varList);
        e.types = toExprArray(uList);
	if (allow_annos) {
	    FunAbstraction a = (FunAbstraction)e;
	    a.owned = toOwnershipArray(annoList);
	}
    }

    protected void popVars(VarListExpr e) {
	Var[] vars = e.vars;
	for (int i = 0, iend = vars.length; i < iend; i++) {
	    ctxt.popVar(vars[i]);
	}
    }

    protected FunTerm readFunTerm() throws IOException
    {
        FunTerm e = new FunTerm();

	if (!eat_ws())
	    handleError("Unexpected end of input parsing a fun term.");
        
	int c = getc();
	ungetc(c);
	if (c != '(') {
	    e.r = readBindingVar();
	}

	if (!eat_ws())
	    handleError("Unexpected end of input parsing a fun term.");

	readVarListExpr(e, true);

	if (tryToEat(":")) {
	    // need to read the return type of the recursive function
	    if (!eat_ws())
		handleError("Unexpected end of input parsing a fun term.");
	    e.ret_stat = readAnno(false /* allow_owned */);
	    e.T = readType();
	}
	else {
	    e.ret_stat = new Ownership(Ownership.UNOWNED);
	    e.T = null;
	}

	eat(".", "fun term");

	if (e.r != null)
	    ctxt.pushVar(e.r);

        e.body = readTerm();

	if (e.r != null)
	    ctxt.popVar(e.r);
	popVars(e);

        return e;
    }

    protected FunType readFunType() throws IOException
    {
        FunType e = new FunType();

	readVarListExpr(e,true);
	eat(".", "Fun type");
	if (!eat_ws())
	    handleError("Unexpected end of input parsing a Fun-type.");
	e.ret_stat = readAnno(false /* allow_owned */);
        e.body = readType();
                
	popVars(e);

        return e;
    }

    protected Forall readForall() throws IOException
    {
	Forall e = new Forall();

	readVarListExpr(e,false);
	eat(".", "Forall formula");
        e.body = readFormula();
                
	popVars(e);

        return e;
    }

    protected Exists readExists() throws IOException
    {
	Exists e = new Exists();

	readVarListExpr(e,false);
	eat(".", "Exists formula");
        e.body = readFormula();
                
	popVars(e);

	for (int i = 0, iend = e.vars.length; i < iend; i++)
	    if (!(isB(e.types[i].construct) 
		  || e.types[i].isFormula(ctxt)))
		handleError("An Exists-formula declares a variable to have"
			    +"a classifier which is not a B expression\n");

        return e;
    }

    protected Foralli readForalli() throws IOException
    {
	Foralli e = new Foralli();
        
	readVarListExpr(e,false);
	eat(".", "foralli proof");
        e.body = readProof();
                
	popVars(e);

        return e;
    }

    protected Join readJoin() throws IOException
    {              
        Join e = new Join();
        
        e.t1 = readTerm();
        
	if (!eat_ws())
	    handleError("Unexpected end of input parsing a join proof.");

        e.t2 = readTerm();

        return e;
    }
    
    protected Eval readEval() throws IOException
    {              
        Eval e = new Eval();
        
        e.t1 = readTerm();
        
        return e;
    }

    protected Evalto readEvalto() throws IOException
    {              
        Evalto e = new Evalto();
        
        e.t1 = readTerm();
        
	if (!eat_ws())
	    handleError("Unexpected end of input parsing an evalto proof.");

        e.t2 = readTerm();

        return e;
    }
    
    protected HypJoin readHypJoin() throws IOException
    {              
    	HypJoin e = new HypJoin();
      
    	if (!eat_ws())
    	    handleError("Unexpected end of input parsing a hypjoin proof.");

        e.t1 = readTerm();
        
	if (!eat_ws())
	    handleError("Unexpected end of input parsing a hypjoin proof.");

        e.t2 = readTerm();
        
        if (!eat_ws())
	    handleError("Unexpected end of input parsing a hypjoin proof.");
        
        eat("by", "hypjoin"); 
        
        if (!eat_ws())
    	    handleError("Unexpected end of input parsing a hypjoin proof.");
            
        
        if(tryToEat("by"))
        {
        	e.mark = true;
        }
        
        if (!eat_ws())
    	    handleError("Unexpected end of input parsing a hypjoin proof.");
            
        
        ArrayList proofs = new ArrayList();
        
        while(true)
        {
            if (!eat_ws())
                handleError("Unexpected end of input parsing a hypjoin proof.");
            
            if(tryToEat("end"))
            {
                break;
            }
            proofs.add(readProof());
        }
        e.Ps = toExprArray(proofs);

        return e;
    }
    
    protected Show readShow() throws IOException
    {              
    	Show e = new Show();
        
        ArrayList proofs = new ArrayList();

	while (!tryToEat("end")) {
	    proofs.add(readAny());
	    
	    if (!eat_ws())
		handleError("Unexpected end of input parsing a show proof.");
	}

        e.P = toExprArray(proofs);

        return e;
    }
    
    protected Refl readRefl() throws IOException
    {              
        Refl e = new Refl();
        
        e.Y = readY();
        
        return e;
    }
    
    protected Symm readSymm() throws IOException
    {              
        Symm e = new Symm();
        
        e.P = readProof();
        
        return e;
    }

    protected Trans readTrans() throws IOException
    {              
        Trans e = new Trans();
        
        e.P1 = readProof();
        
	if (!eat_ws())
	    handleError("Unexpected end of input parsing a trans proof.");

        e.P2 = readProof();
        
        return e;
    }
    
    protected ExistseTerm readExistseTerm() throws IOException
    {              
        ExistseTerm e = new ExistseTerm();
        
        e.P = readProof();
        
	if (!eat_ws())
	    handleError("Unexpected end of input parsing an existse_term.");

        e.t = readTerm();
        
        return e;
    }

    protected Existse readExistse() throws IOException
    {              
        Existse e = new Existse();
        
        e.P1 = readProof();
        
	if (!eat_ws())
	    handleError("Unexpected end of input parsing a existse proof.");

        e.P2 = readProof();
        
        return e;
    }

    protected Existsi readExistsi() throws IOException
    {              
        Existsi e = new Existsi();
        
        e.I = readX();
        
	if (!eat_ws())
	    handleError("Unexpected end of input parsing a existsi proof.");

        e.Fhat = readFhat();

	if (!eat_ws())
	    handleError("Unexpected end of input parsing a existsi proof.");

        e.P = readProof();
        
        return e;
    }

    protected Andi readAndi() throws IOException
    {              
        Andi e = new Andi();
        
        e.P1 = readProof();
        
	if (!eat_ws())
	    handleError("Unexpected end of input parsing a existsi proof.");

        e.P2 = readProof();
        
        return e;
    }

    protected Expr readEplus() throws IOException 
    {
	allow_stars = true;

	Expr e = readX();

	if (!(isTerm(e.construct) || isTypeOrKind(e.construct)))
	    handleError("An E+ context is not a term or a type.");

	allow_stars = false;

	if (e.numOcc(ctxt.star) == 0)
	    handleError("An E+ context does not have a star (\"*\") in it.");

	return e;
    }

    protected Cong readCong() throws IOException
    {              
        Cong e = new Cong();
        
        e.Estar = readEplus();
        
	if (!eat_ws())
	    handleError("Unexpected end of input parsing a cong proof.");

        e.P = readProof();
        
        return e;
    }

    protected Ncong readNcong() throws IOException
    {              
        Ncong e = new Ncong();
        
        e.Ihat = readIhat(false /* single hole */);
        
	if (!eat_ws())
	    handleError("Unexpected end of input parsing a ncong proof.");

	e.I1 = readX();

	if (!eat_ws())
	    handleError("Unexpected end of input parsing a ncong proof.");

	e.I2 = readX();

	if (!eat_ws())
	    handleError("Unexpected end of input parsing a ncong proof.");

        e.P = readProof();
        
        return e;
    }

    protected Inj readInj() throws IOException
    {              
        Inj e = new Inj();
        
        e.Ihat = readIhat(false /* single hole */);
        
	if (!eat_ws())
	    handleError("Unexpected end of input parsing a inj proof.");

        e.P = readProof();
        
        return e;
    }

    protected Diseqi readDiseqi() throws IOException
    {              
        Diseqi e = new Diseqi();
        
        e.P = readProof();
        
        return e;
    }
    
    protected Clash readClash() throws IOException
    {              
        Clash e = new Clash();
        
        e.t1 = readX();
        
	if (!eat_ws())
	    handleError("Unexpected end of input parsing a clash proof.");

        e.t2 = readX();
        
        return e;
    }
    
    protected Aclash readAclash() throws IOException
    {              
        Aclash e = new Aclash();
        
        e.t = readX();
        
        return e;
    }
    
    protected Inv readInv() throws IOException
    {              
        Inv e = new Inv();
        
	if (!eat_ws())
	    handleError("Unexpected end of input parsing an inv proof.");

        e.t = readTerm();

	if (!eat_ws())
	    handleError("Unexpected end of input parsing an inv proof.");

        e.P = readProof();
        
        return e;
    }

    protected Subst readSubst() throws IOException
    {              
        Subst e = new Subst();
        
        e.I = readI();
        
	if (!eat_ws())
	    handleError("Unexpected end of input parsing a subst proof.");

        e.P = readProof();
        
        return e;
    }

    protected Contra readContra() throws IOException
    {              
        Contra e = new Contra();
        
        e.P = readProof();
        
	if (!eat_ws())
	    handleError("Unexpected end of input parsing a contra proof.");

        e.F = readFormula();
        
        return e;
    }

    protected Abort readAbort() throws IOException
    {              
        Abort e = new Abort();
        
        e.T = readType();
        
        return e;
    }
    
    protected Impossible readImpossible() throws IOException
    {              
        Impossible e = new Impossible();
        
        e.P = readProof();

	if (!eat_ws())
	    handleError("Unexpected end of input parsing an impossible-term.");

        e.T = readType();
        
        return e;
    }
    
    protected Size readSize() throws IOException
    {              
        Size e = new Size();
        
        e.t = readTerm();
        
        return e;
    }
    
    protected Cast readCast() throws IOException
    {
        Cast e = new Cast();

        e.t = readTerm();

        eat("by", "cast term");

        e.P = readProof();
        return e;
    }

    protected Cutoff readCutoff() throws IOException
    {
        Cutoff e = new Cutoff();
        
        e.t = readTerm();
        return e;
    }

    protected Cind readCind() throws IOException
    {
	Cind e = new Cind();

	e.P = readProof();
	return e;
    }

    protected Terminates readTerminates() throws IOException
    {
        Terminates e = new Terminates();

        e.t = readTerm();

        eat("by", "terminates-casting term");

        e.P = readProof();
        return e;
    }
    
    protected Inc readInc() throws IOException
    {
        Inc e = new Inc();
        
        e.t = readTerm();
        
        return e;
    }
    
    protected Dec readDec() throws IOException
    {
        Dec e = new Dec();
        
        e.I = readI();

	if (!eat_ws())
	    handleError("Unexpected end of input parsing a dec-term.");

        e.t = readTerm();
        
        return e;
    }

    protected int eatKeyword() throws IOException
    {
        if (!eat_ws())
	    return Expr.INVALID;
        
	if (tryToEat("**"))
	    return Expr.STARSTAR;
	if (tryToEat("*"))
	    return Expr.STAR;
	if (tryToEat("fun"))
	    return Expr.FUN_TERM;
	if (tryToEat("cast"))
	    return Expr.CAST;
	if (tryToEat("terminates"))
	    return Expr.TERMINATES;
	if (tryToEat("("))
	    return Expr.TERM_APP;
	if (tryToEat("abort"))
	    return Expr.ABORT;
	if (tryToEat("let")) 
	    return Expr.LET;
	if (tryToEat("abbrev"))
	    return Expr.ABBREV;
	if (tryToEat("eabbrev"))
	    return Expr.EABBREV;
	if (tryToEat("match"))
	    return Expr.MATCH;
	if (tryToEat("Fun"))
	    return Expr.FUN_TYPE;
	if (tryToEat("type"))
	    return Expr.TYPE;
	if (tryToEat("<"))
	    return Expr.TYPE_APP;
	if (tryToEat("@<"))
	    return Expr.PRED_APP;
	if (tryToEat("dec"))
	    return Expr.DEC;
	if (tryToEat("inc"))
	    return Expr.INC;
	if (tryToEat("foralli"))
	    return Expr.FORALLI;
	if (tryToEat("["))
	    return Expr.PROOF_APP;
	if (tryToEat("case"))
	    return Expr.CASE_PROOF;
	if (tryToEat("!"))
	    return Expr.BANG;
	if (tryToEat("existsi"))
	    return Expr.EXISTSI;
	if (tryToEat("andi"))
	    return Expr.ANDI;
	if (tryToEat("existse_term"))
	    return Expr.EXISTSE_TERM;
	if (tryToEat("existse"))
	    return Expr.EXISTSE;
	if (tryToEat("truei"))
	    return Expr.TRUEI;
	if (tryToEat("diseqi"))
	    return Expr.DISEQI;
	if (tryToEat("True"))
	    return Expr.TRUE;
	if (tryToEat("False"))
	    return Expr.FALSE;
	if (tryToEat("join"))
	    return Expr.JOIN;
	if (tryToEat("evalto"))
	    return Expr.EVALTO;
	if (tryToEat("eval"))
	    return Expr.EVAL;
	if (tryToEat("hypjoin"))
	    return Expr.HYPJOIN;
	if (tryToEat("refl"))
	    return Expr.REFL;
	if (tryToEat("symm"))
	    return Expr.SYMM;
	if (tryToEat("trans"))
	    return Expr.TRANS;
	if (tryToEat("cong"))
	    return Expr.CONG;
	if (tryToEat("ncong"))
	    return Expr.NCONG;
	if (tryToEat("inj"))
	    return Expr.INJ;
	if (tryToEat("clash"))
	    return Expr.CLASH;
	if (tryToEat("aclash"))
	    return Expr.ACLASH;
	if (tryToEat("cinv"))
	    return Expr.INV;
	if (tryToEat("subst"))
	    return Expr.SUBST;
	if (tryToEat("show"))
	    return Expr.SHOW;
	if (tryToEat("contra"))
	    return Expr.CONTRA;
	if (tryToEat("induction"))
	    return Expr.INDUCTION;
	if (tryToEat("Forall"))
	    return Expr.FORALL;
	if (tryToEat("Exists"))
	    return Expr.EXISTS;
	if (tryToEat("{"))
	    return Expr.ATOM;
	if (tryToEat("cutoff"))
	    return Expr.CUTOFF;
	if (tryToEat("cind"))
	    return Expr.CIND;
	if (tryToEat("impossible"))
	    return Expr.IMPOSSIBLE;
	if (tryToEat("size"))
	    return Expr.SIZE;
	if (tryToEat("\""))
	    return Expr.LAST + STRING;
                    
	if (tryToEat(")") ||
	    tryToEat("]") ||
	    tryToEat(">") ||
	    tryToEat(".") ||
	    tryToEat("=") ||
	    tryToEat("|"))
	    handleError("Unexpected punctuation.");

        return Expr.VAR;
    }

}

