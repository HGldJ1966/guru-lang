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

    public static int num_proofs = 0;
    public static int num_trusted = 0;

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
	case Expr.WORD_EXPR:
	    return true;
	case Expr.CHAR_EXPR:
	    return true;
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
    int construct = eatKeyword();
    if (construct == Expr.INVALID)
    	handleError("Unexpected end of file.");
	return readAny(construct);
    }

    // call with value from eatKeyword() 
    public Expr readAny(int construct) throws IOException {
	Expr e = null;
	Position pos = getPos();
	switch(construct)
            {
        case Expr.ASCRIPTION:
		e = readAscription();
		break;
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
	    case Expr.DO:
		e = readDo();
		break;
	    case Expr.CAST:
		e = readCast();
		break;
	    case Expr.COMPILE_AS:
		e = readCompileAs();
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
	    	e = readAbbrev( Abbrev.fAbbrevNone );
	    	break;
	    case Expr.EABBREV:
	    	e = readAbbrev( Abbrev.fAbbrevEvaluate);
	    	break;
	    case Expr.CABBREV:
	    	e = readAbbrev( Abbrev.fAbbrevClassify);
	    	break;
	    case Expr.LEMMA:
	    	e = readLemma();
	    	break;
	    case Expr.LEMMA_MARK:
	    	e = readLemmaMark();
	    	break;
	    case Expr.MATCH:
		e = readMatch();
		break;
	    case Expr.FUN_TYPE:
		e = readFunType();
		break;
	    case Expr.TYPE:
		e = ctxt.type;
		break;
		/*	    case Expr.FORMULA:
		e = ctxt.formula;
		break; */
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
	    case Expr.TERM_CASE:		
		e = readTerminatesCase();
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
            case Expr.TRANSS:
                e = readTranss();
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
	    case Expr.TRUE:
	    	e = readTrue();
		break;
	    case Expr.FALSE:
	    	e = readFalse();
		break;
	    case Expr.VOID:
	    	e = new Void();
		break;
	    case Expr.VOIDI:
	    	e = new Voidi();
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
	    case Expr.COMPRESS:
		e = readCompress();
		break;
	    case Expr.CHAR_EXPR:
		e = readCharExpr();
		break;
	    case Expr.WORD_EXPR:
		e = readWordExpr();
		break;
	    case Expr.LAST+STRING:
		e = readStringExpr();
		break;
	    default:
		handleError("Internal error: Parser is missing case for construct");
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
	else if (tryToEat("ResourceType")) 
	    c = readResourceType();
	else if (tryToEat("Init"))
	    c = readInit();
	else
	    handleError("Unexpected start of a command.");
	c.pos = pos;
	return c;
    }

    protected ResourceType readResourceType() throws IOException {
	ResourceType a = new ResourceType();
	if (!eat_ws())
	    handleError("Unexpected end of input reading a ResourceType-command.");

	a.s = readBindingConst();
	
	ctxt.addResourceType(a.s);
	
	eat_ws();

	if (tryToEat("affine")) {
	    a.drop = null;
	    eatDelim(".", "ResourceType");
	}
	else {
	    eat("with", "ResourceType");
	    if (!eat_ws())
		handleError("Unexpected end of input reading a ResourceType-command.");
	    eat("Define", "ResourceType");
	    a.drop = readDefine();
	}
	return a;
    }

    protected Init readInit() throws IOException {
	Init a = new Init();
	while(true) {
	    eat_ws();
	    if (tryToEat("must_consume_scrutinee")) 
		a.must_consume_scrut = true;
	    else if (tryToEat("take_pointer")) 
		a.take_pointer = true;
	    else 
		break;
	}

	a.s = readBindingConst();

	eat("(","Init");
	eat("#","Init");
	a.T1 = new Ownership(Ownership.RESOURCE, readConst());
	eat_ws();
	a.v1 = (Var)readIdentifier(true);
	eat(")","Init");
	ctxt.pushVar(a.v1);

	eat("(","Init");
	eat("#","Init");
	a.T2 = new Ownership(Ownership.RESOURCE, readConst());
	eat_ws();
	a.v2 = (Var)readIdentifier(true);
	eat(")","Init");
	eat(".","Init");
	ctxt.pushVar(a.v2);

	a.T3 = readAnno();
	ctxt.popVar(a.v1);
	ctxt.popVar(a.v2);

	eat("<<","Init");
	a.delim = readID();
	a.code = read_until_newline_delim(a.delim);
	eatDelim(".","Init");
	return a;
    }


    protected Set readSet() throws IOException
    {
	Set s = new Set();
	if (!eat_ws())
	    handleError("Unexpected end of input reading a Set-command.");

	s.flag = readString();

	eatDelim(".", "Set");

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

	eatDelim(".", "Total");

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

	eatDelim(".", "Unset");

	return s;
    }
    
    

    protected Define readDefine() throws IOException
    {
	Define cmd = new Define();
	
	if (!eat_ws())
	    handleError("Unexpected end of input parsing a Define.");

	cmd.spec = false;
	cmd.primitive = false;
	cmd.trusted = trusted && !ctxt.getFlag("ignore_trusted_flag_for_includes");
	cmd.type_family_abbrev = false;
	cmd.predicate = false;
	cmd.abbrev = false;


	boolean cmd_trusted = false;

	// read the various flags that can be given to Define.
	while (true) {
	    
	    if (tryToEat("spec")) {
		cmd.spec = true;
		spec = true;
	    }
	    else if (tryToEat("primitive")) {
		cmd.primitive = true;
		spec = true;
	    }
	    else if (tryToEat("trusted"))
		cmd.trusted = cmd_trusted = true;
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

	if (allow_type_fam_abbrev && allow_predicate) 
	    handleError("A defined constant cannot be both a type family\n"
			+"abbreviation and a predicate.");

	cmd.c = readBindingConst();

	if (!eat_ws())
	    handleError("Unexpected end of input parsing a Define.");

	while(true) {
	    if (tryToEat(":=")) {
		cmd.G = readAny();
		break;
	    }
	    else {
		if (tryToEat(":")) {
		    if (cmd.A != null)
			handleError("Multiple types declared (following \":\") in a Define.");
		    if (cmd.primitive) {
			eat_ws();
			cmd.o = readAnno();
			eat_ws();
		    }
		    cmd.A = readA();
		    eat_ws();
		}
		else
		    break;
	    }
	}

	if (cmd.o == null)
	    cmd.o = new Ownership(Ownership.DEFAULT);

	if (cmd.primitive) {
	    eat("<<","Primitive");
	    if (cmd.G == null) {
		// this is a primitive without a functional model
		if (cmd.A == null) 
		    handleError("A primitive definition without a functional model is given without a type.");
		if (!cmd.A.isTypeOrKind(ctxt))
		    handleError("A primitive definition without a functional model is given with a classifier\n"
				+"which is not a type or a kind.\n\n");

		Var v = new Var(cmd.c.name);
		cmd.G = v;
		ctxt.setClassifier(v,cmd.A);
	    }
	    
	    cmd.delim = readID();
	    cmd.code = read_until_newline_delim(cmd.delim);
	}

	allow_type_fam_abbrev = false;
	allow_predicate = false;
	spec = false;

	eatDelim(".", "Define");

	if (ctxt.getFlag("count_proofs") && cmd.G.isProof(ctxt)) {
	    num_proofs++;
	    if (cmd_trusted)
		num_trusted++;
	}

	return cmd;
    }

    
    protected Interpret readInterpret() throws IOException
    {
    	Interpret cmd = new Interpret();
	if (!eat_ws())
	    handleError("Unexpected end of input parsing an Interpret.");
	cmd.t = readTerm();
	eatDelim(".", "Interpret");
    	return cmd;
    }

    protected ClassifyCmd readClassifyCmd() throws IOException
    {
    	ClassifyCmd cmd = new ClassifyCmd();
	if (!eat_ws())
	    handleError("Unexpected end of input parsing an Interpret.");
	cmd.G = readAny();
	eatDelim(".", "Classify");
    	return cmd;
    }

    protected Untracked readUntracked() throws IOException
    {
    	Untracked cmd = new Untracked();
	if (!eat_ws())
	    handleError("Unexpected end of input parsing an Untracked.");
	cmd.d = readConst();
	eatDelim(".", "Untracked");
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
                    cmd.trackID(readConst());
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
        eatDelim(".", "DumpDependence");
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
	eatDelim(".", "Compile");
	return c;
    
    }
   
    protected Expr readStringExpr() throws IOException {
	ungetc('\"');
	return new StringExpr(readString());
    }

    protected Expr readCharExpr() throws IOException {
	ungetc('\'');
	return new CharExpr(readString(new Character('\'')));
    }

    protected Expr readWordExpr() throws IOException {
	return new WordExpr(readHex());
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
	eatDelim(".", "Include");
	return cmd;
    }

    protected Echo readEcho() throws IOException
    {
	Echo cmd = new Echo();
	if (!eat_ws())
	    handleError("Unexpected end of input parsing a Include.");
	cmd.s = readString();
	eatDelim(".", "Echo");
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

	ArrayList cs = new ArrayList();
	ArrayList Ds = new ArrayList();
	Ownership ret_stat = null;
	tryToEat("|");	// Duckki: first bar is now optional (like Coq)
	while (true) {
	    if (!eat_ws())
			handleError("Unexpected end of input parsing an Inductive");
            Const cst = readBindingConst();
	    cs.add(cst);
	    eat(":", "Inductive");
	    Ownership ret_stat_cur = readAnno();
	    p = getPos();
	    Expr D = readD(cmd.d);
	    D.pos = p;
	    if (D.construct == Expr.FUN_TYPE) 
		ret_stat_cur = ((FunType)D).ret_stat;
	    if (ret_stat == null)
		ret_stat = ret_stat_cur;
	    else
		if (!ret_stat_cur.equalOwnership(ret_stat))
		    handleError("The return type for a term constructor has a different resource type specification"
				+"\nthan that of the previous term constructors."
				+"\n\n1. the term constructor: "+cst.toString(ctxt)
				+"\n\n2. its resource type: "+ret_stat_cur.toString(ctxt)
				+"\n\n3. the previous constructors' resource type: "+ret_stat.toString(ctxt));
	    Ds.add(D);
	    if (!eat_ws())
		break;
	    if (!tryToEat("|"))
		break; // out of while 
	}
	eatDelim(".", "Inductive");

	cmd.ret_stat = ret_stat;
	cmd.c = toConstArray(cs);
	cmd.D = toExprArray(Ds);

	return cmd;
    }

    // read a D expression, whose return type should be a d-type.
    protected Expr readD(Const d) throws IOException 
    {
	Expr ee = readType();
	
	Expr ran = null;
	if (ee.construct == Expr.FUN_TYPE) {
	    FunType e = (FunType)ee;

	    for (int i = 0, iend = e.vars.length; i < iend; i++) {
		Expr T = e.types[i];
		if (!isAminus(T))
		    handleError("Expected an A- expression in the type of a "
				+"term constructor");
		if (T.isdtype(ctxt,true))
		    continue;

		if (T.numOcc(d) > 0)
		    handleError("An input type for a term constructor uses"
				+" the corresponding type constructor in a"
				+" disallowed way:"
				+"\n1. the type: "+T.toString(ctxt));
	    }
	    ran = e.body;
	}
	else
	    ran = ee;
	if (!isdtypeRestricted(ran,d))
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
	    handleError("Expected a term, type, kind, or proof.");
        return readAny(construct);
    }
    
    protected Expr readArg() throws IOException
    {
    	int construct = eatKeyword();
    	if(!isX(construct) && construct != Expr.LEMMA_MARK)
    		handleError("Expected a term, type, kind, proof, or lemma mark.");
    	return readAny(construct);
    }
    
    protected Expr readY() throws IOException
    {
	int construct = eatKeyword();
	if (!isY(construct))
	    handleError("Expected a type, kind, or term.");
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
	e.consumps = new int[e.vars.length];
	for (int i = 0; i < iend; i++) {
	    e.owned[i] = new Ownership(Ownership.DEFAULT);
	    e.consumps[i] = FunAbstraction.NOT_CONSUMED;
	}
        eat(".", "kind");
        e.body = readKind();
	e.ret_stat = new Ownership(Ownership.DEFAULT);
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
            theT.add(readArg());
        
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
        
	if (e.X.length == 0) {
	    String headstr = e.head.toString(ctxt);
	    handleError("A type application is used without any arguments to the head \""
			+headstr+"\".\n\nThe correct notation is just \""+headstr+"\", not \"<"+headstr+">\".");
	}

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

	eat_ws();
	e.consume_scrut = !tryToEat("!");

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

protected TerminatesCase readTerminatesCase() throws IOException
    {
        TerminatesCase e = new TerminatesCase();

        e.t = readTerm();
        
	e.u = null;

	String errstr = "Unexpected end of input parsing assumption var.";

	if (!eat_ws())
	    handleError(errstr);

	if (tryToEat("by")) {
	    if (!eat_ws())
		handleError(errstr);
	    
	    Position p = getPos();
	    e.u = readBindingVar();
	    e.u.pos = p;

	    if (!eat_ws())
		handleError(errstr);
	}
	else {
	    if (e.t.construct == Expr.VAR || e.t.construct == Expr.CONST) {
		String n = 
		    (e.t.construct == Expr.VAR ? ((Var)e.t).name
		     : ((Const)e.t).name);
		e.u = new Var(n+"_eq");
		Position p = getPos();
		e.u.pos = p;
	    }
	}

	if (e.u == null) 
	    handleError("A terminates-case proof lacks a \"by\" clause, and we"
			+" cannot automatically declare\n"
			+"its variable, since the scrutinee is not"
			+" a variable.");

	ctxt.pushVar(e.u);

	
	eat("with", "case-terminates proof");
	// put an error message here if no with?

        eat_ws();
	e.x = readBindingVar();
        ctxt.pushVar(e.x);

	eat("=>", "case-terminates proof");

	e.p1 = readProof();
        ctxt.popVar(e.x);

	eat("|", "case-terminates proof");
	eat("abort", "case-terminates proof");
	//put in an error if abort isn't the second case

	eat("=>", "case-terminates proof");
	e.p2 = readProof();
	eat("end", "case-terminates proof");
		
	
	ctxt.popVar(e.u);

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
	
	tryToEat("|");	// Duckki: first bar is optional
	if (!eat_ws())
	    handleError("Unexpected end of input parsing "+where+".");
	
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

	e.x1_stat = readAnno();

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

	eatDelim("in", "let term");

	ctxt.pushVar(e.x2);

	ctxt.pushVar(e.x1);

        e.t2 = readTerm();

	ctxt.popVar(e.x1);

	ctxt.popVar(e.x2);

        return e;
    }

    protected Abbrev readAbbrev(int flags) throws IOException
    {
	Var x;
	Expr U, G;
        Position pos = getPos();

	if (!eat_ws())
	    handleError("Unexpected end of input parsing a abbrev term.");

	x = readBindingVar();

	eat("=", "abbrev term");
	    
	U = readAny();
        
	eatDelim("in", "abbrev term");
        
	ctxt.pushVar(x);
	
	ctxt.macroDefine(x,U); /* we do this now for the benefit
				  of readFormula() */

        G = readAny();
	
	ctxt.popVar(x);
	
        Abbrev ret = new Abbrev(flags,x,U,G);
	ret.pos = pos;
	return ret;
    }
    
    protected Lemma readLemma() throws IOException 
    {
    	Position pos = getPos();
    	
    	if (!eat_ws())
    	    handleError("Unexpected end of input parsing a lemma term.");

    	Expr lemmaProof = readProof();
    	
    	eat_ws();
    	
    	if (tryToEat("in", true))
    	{
        	Expr body = readProof();
        	Lemma ret = new Lemma(lemmaProof, body);
        	ret.pos = pos;
        	return ret;    
    	}
    	else
    	{
    		Expr body = readLemma();
    		Lemma ret = new Lemma(lemmaProof, body);
    		ret.pos = pos;
    		return ret;
    	}
    }
    
    protected LemmaMark readLemmaMark()
    {
    	Position pos = getPos();
    	LemmaMark ret = new LemmaMark();
    	ret.pos = pos;
    	return ret;
    }
    
    protected Const readBindingConst() throws IOException
    {
	Var v = (Var)readIdentifier(true);
	Expr e = ctxt.lookup(v.name);
	if (e != null) 
	    handleError("A previous definition or "
			+"declaration is being shadowed:"
			+"\n\n1. the defined constant: "+v.toString(ctxt)
			+(e.pos != null ?
			  "\n\n2. previously defined at: "+e.pos.toString()
			  : ""));
	Const c = new Const(v.name);

	c.pos = v.pos;
	return c;
    }

    protected Const readConst() throws IOException
    {
	Expr e = readIdentifier(false);
	if (e.construct != Expr.CONST)
	    handleError("Expected a constant, but found: \""+e.toString(ctxt)+"\".");
	return (Const)e;
    }

    protected Var readVar () throws IOException
    {
	Expr e = readIdentifier(false);
	if (e.construct != Expr.VAR)
	    handleError("Expected a variable, but found: \""+e.toString(ctxt)+"\".");
	return (Var)e;
    }

    protected Var readBindingVar () throws IOException
    {
	return (Var)readIdentifier(true);
    }

    protected Expr readAscription() throws IOException
    {
    	Expr classifier = readA();
    	Expr target = readArg();
    	return new Ascription(classifier, target);
    }
    
    protected Expr readIdentifier(boolean binding_occurrence) 
	throws IOException
    {
        Position pos = getPos();
        String theVarName = readID();

	Expr e = ctxt.lookup(theVarName);	
	/*
	ctxt.w.println("theVarName = "+theVarName+", binding_occurrence = "+(new Boolean(binding_occurrence)).toString());
	ctxt.w.flush();
	*/
	if (!binding_occurrence) {
	    if (e != null)
		return e;
	    handleError(pos, "Undeclared variable \""+theVarName+"\"");
	}

	Var v = new Var(theVarName);
	v.pos = pos;
	return v;
    }
     
    protected Ownership readAnno() throws IOException {
	if (tryToEat("#<")) {
	    Const c = readConst();
	    if (!eat_ws())
		handleError("Unexpected end of input reading a resource tracking annotation.");
	    Var v = readVar();
	    Ownership o = new Ownership(Ownership.PINNED,c,v);
	    eat(">", "resource type");
	    return o;
	}
	if (tryToEat("spec"))
	    return new Ownership(Ownership.SPEC);
	if (tryToEat("#untracked"))
	    return new Ownership(Ownership.UNTRACKED);
	if (tryToEat("#abort"))
	    return new Ownership(Ownership.ABORT);
	if (tryToEat("#",true))
	    return new Ownership(Ownership.RESOURCE, readConst());
	return new Ownership(Ownership.DEFAULT);
    }

    protected class VarList {
	public Ownership anno;
	public int consump;
	public Var[] vars;
	public Expr type;
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
	Ownership anno = new Ownership(Ownership.DEFAULT);
	int consump = FunAbstraction.CONSUMED_RET_OK;
	if (allow_annos) {
	    if (tryToEat("!"))
		consump = FunAbstraction.NOT_CONSUMED;
	    else if (tryToEat("^"))
		consump = FunAbstraction.CONSUMED_NO_RET;
	    if (!eat_ws())
		handleError("Unexpected end of input reading a variable list.");
	    anno = readAnno();
	    if ((anno.status == Ownership.SPEC || anno.status == Ownership.UNTRACKED) 
		&& consump != FunAbstraction.CONSUMED_RET_OK) 
		handleError("An untracked or specificational argument is labeled with either \"^\" or \"!\".");
	    if (!eat_ws())
		handleError("Unexpected end of input reading a variable"
			    +" list.");
	}
		
        do
        {        
	    Var v = readBindingVar();
	    if (ctxt.isResourceType(v.name))
		handleError("A variable is shadowing a resource type.  Perhaps you are missing the leading \"#\"?"
			    +"\n\n1. the variable: "+v.toString(ctxt)
			    +"\n\n2. should maybe be: #"+v.toString(ctxt));
		
            varList.add(v);

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
	    if (type.construct == Expr.CONST && ctxt.isUntracked((Const)type)
	    	&& anno.status == Ownership.DEFAULT)
	       anno = new Ownership(Ownership.UNTRACKED);

	    if (!eat_ws() || !tryToEat(")"))
		handleError("Unexpected end of input reading a variable list.");
	}

	VarList vl = new VarList();
        vl.vars = toVarArray(varList);
	vl.type = type;
	vl.anno = anno;
	vl.consump = consump;
	
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
        ArrayList consumpList = new ArrayList();

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
            for(int i=0; i<vl.vars.length;i++) {
                varList.add(vl.vars[i]);
                uList.add(vl.type);
		if (allow_annos) {
		    consumpList.add(new Integer(vl.consump));
		    annoList.add(vl.anno);
		}
	    }
        
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
	    a.consumps = toIntArray(consumpList);
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
	    e.ret_stat = readAnno();
	    e.T = readType();
	}
	else {
	    e.ret_stat = new Ownership(Ownership.DEFAULT);
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
	e.ret_stat = readAnno();
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

	if (e.P.length == 0)
	  handleError("Show-proof contains no content.");

        return e;
    }
    

    protected Transs readTranss() throws IOException
    {              
    	Transs e = new Transs();
        
        ArrayList proofs = new ArrayList();

	while (!tryToEat("end")) {
	    proofs.add(readProof());
	    
	    if (!eat_ws())
		handleError("Unexpected end of input parsing a transs proof.");
	}

        e.P = toExprArray(proofs);
	
	if (e.P.length == 0)
	  handleError("Transs-proof contains no content.");

        return e;
    }

    protected Do readDo() throws IOException
    {              
    	Do e = new Do();
        
        ArrayList terms = new ArrayList();

	while (!tryToEat("end")) {
	    terms.add(readAny());
	    
	    if (!eat_ws())
		handleError("Unexpected end of input parsing a show proof.");
	}

	int sz = terms.size();
	if (sz <= 1)
	    handleError("A do-term is used with fewer than 2 subterms.");

	e.t = (Expr)terms.get(sz-1);
	terms.remove(sz-1);
        e.ts = toExprArray(terms);

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

    protected CompileAs readCompileAs() throws IOException
    {
        CompileAs e = new CompileAs();

        e.t1 = readTerm();

        eat("as", "compiles-as term");

        e.t2 = readTerm();

        eat("by", "compiles-as term");

        e.P = readProof();

        return e;
    }

    protected Compress readCompress() throws IOException
    {
        Compress e = new Compress();

        e.t = readTerm();

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
	
	protected static DiscriminationTree	keywordTree;
	
	static {
		keywordTree = new DiscriminationTree();
		keywordTree.add( ":", Expr.ASCRIPTION);
		keywordTree.add( "**", Expr.STARSTAR );
		keywordTree.add( "*", Expr.STAR );
		keywordTree.add( "do", Expr.DO );
		keywordTree.add( "fun", Expr.FUN_TERM );
		keywordTree.add( "cast", Expr.CAST );
		keywordTree.add( "compile", Expr.COMPILE_AS );
		keywordTree.add( "terminates", Expr.TERMINATES );
		keywordTree.add( "(", Expr.TERM_APP );
		keywordTree.add( "abort", Expr.ABORT );
		keywordTree.add( "let", Expr.LET );
		keywordTree.add( "abbrev", Expr.ABBREV );
		keywordTree.add( "eabbrev", Expr.EABBREV );
		keywordTree.add( "cabbrev", Expr.CABBREV );
		keywordTree.add( "lemma", Expr.LEMMA );
		keywordTree.add( "##", Expr.LEMMA_MARK );
		keywordTree.add( "match", Expr.MATCH );
		keywordTree.add( "Fun", Expr.FUN_TYPE );
		keywordTree.add( "type", Expr.TYPE );
		keywordTree.add( "<", Expr.TYPE_APP );
		keywordTree.add( "@<", Expr.PRED_APP );
		keywordTree.add( "@", Expr.COMPRESS );	// prefix!
		keywordTree.add( "foralli", Expr.FORALLI );
		keywordTree.add( "[", Expr.PROOF_APP );
		keywordTree.add( "case", Expr.CASE_PROOF );
		keywordTree.add( "terminates-case", Expr.TERM_CASE ); 
		keywordTree.add( "!", Expr.BANG );
		keywordTree.add( "existsi", Expr.EXISTSI );
		keywordTree.add( "andi", Expr.ANDI );
		keywordTree.add( "existse_term", Expr.EXISTSE_TERM );
		keywordTree.add( "existse", Expr.EXISTSE );
		keywordTree.add( "truei", Expr.TRUEI );
		keywordTree.add( "diseqi", Expr.DISEQI );
		keywordTree.add( "True", Expr.TRUE );
		keywordTree.add( "False", Expr.FALSE );
		keywordTree.add( "voidi", Expr.VOIDI );
		keywordTree.add( "void", Expr.VOID );
		keywordTree.add( "join", Expr.JOIN );
		keywordTree.add( "evalto", Expr.EVALTO );
		keywordTree.add( "eval", Expr.EVAL );
		keywordTree.add( "hypjoin", Expr.HYPJOIN );
		keywordTree.add( "refl", Expr.REFL );
		keywordTree.add( "symm", Expr.SYMM );
		keywordTree.add( "transs", Expr.TRANSS );
		keywordTree.add( "trans", Expr.TRANS );
		keywordTree.add( "cong", Expr.CONG );
		keywordTree.add( "ncong", Expr.NCONG );
		keywordTree.add( "inj", Expr.INJ );
		keywordTree.add( "clash", Expr.CLASH );
		keywordTree.add( "aclash", Expr.ACLASH );
		keywordTree.add( "cinv", Expr.INV );
		keywordTree.add( "subst", Expr.SUBST );
		keywordTree.add( "show", Expr.SHOW );
		keywordTree.add( "contra", Expr.CONTRA );
		keywordTree.add( "induction", Expr.INDUCTION );
		keywordTree.add( "Forall", Expr.FORALL );
		keywordTree.add( "Exists", Expr.EXISTS );
		keywordTree.add( "{", Expr.ATOM );
		keywordTree.add( "cutoff", Expr.CUTOFF );
		keywordTree.add( "cind", Expr.CIND );
		keywordTree.add( "impossible", Expr.IMPOSSIBLE );
		keywordTree.add( "size", Expr.SIZE );
		keywordTree.add( "0x", Expr.WORD_EXPR );
		keywordTree.add( "\'", Expr.CHAR_EXPR );
		keywordTree.add( "\"", Expr.LAST + STRING );

		keywordTree.add( ")", Expr.INVALID );
		keywordTree.add( "]", Expr.INVALID );
		keywordTree.add( ">", Expr.INVALID );
		keywordTree.add( ".", Expr.INVALID );
		keywordTree.add( "=", Expr.INVALID );
		keywordTree.add( "|", Expr.INVALID );
	}

	static char[]	keywordBuf = new char[100];	// WARNING: assuming maximum length of keyword

	protected int tryToEatKeyword()  throws IOException
	{
		char[]	buf = keywordBuf;
		int		cur = 0;
		int		final_end = -1;	// end position of the longest keyword
		Integer	keyword_val = null;	// value for the longest keyword
		
		DiscriminationTree.Iterator	it = keywordTree.begin();
		for( ; ; )
		{
			int c = getc();
			//System.out.println( "keyword getc: " + String.valueOf((char)c) );
			if( c < 0 )
				break;
			buf[cur++] = (char)c;
			
			it.next( c );
			if( !it.isValid() )
				break;
			if( it.isFinal() ) {	// wait for the longest keyword
				//System.out.println( "keyword matched" );
				final_end = cur;
				keyword_val = it.value;
			}
		}
		
		// see if not starting with a valid keyword
		if( final_end == -1 )
		{
			// rollback all
			for( int j=cur-1; j>=0; j-- )
				ungetc( buf[j] );
			return -1;
		}
		
		// see if a legal id character is following a non-punctuation-keyword
		if( Character.isLetter(buf[0])	// not a punctuator
		 && cur != final_end	// there is a character after keyword
		 && !Character.isWhitespace(buf[final_end])
		 && LegalIdChar(buf[final_end])	// which is a legal id character
		  ) {
			// rollback all
			for( int j=cur-1; j>=0; j-- )
				ungetc( buf[j] );
			return -1;
		}
		// now, we got a keyword
		
		// but, some puctuation keyword is not allowed here.
		if( keyword_val.intValue() == Expr.INVALID )
			handleError("Unexpected punctuation." );
			
		// rollback tail
		for( int j=cur-1; j>=final_end; j-- )
			ungetc( buf[j] );

		return keyword_val.intValue();
	}

    protected int eatKeyword() throws IOException
    {
        if (!eat_ws())
	    return Expr.INVALID;
	int	val = tryToEatKeyword();
	//System.out.println( "tryToEatKeyword: " + String.valueOf(val) );
	if( val < 0 )
		return Expr.VAR;
	return val;
    }
}
