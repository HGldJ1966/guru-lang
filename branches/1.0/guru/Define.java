package guru;

import java.util.Iterator;

public class Define extends Command {
    public boolean spec;
    public boolean primitive;
    public boolean trusted;
    public boolean type_family_abbrev;
    public boolean predicate;
    public boolean abbrev;

    public Const c;
    public Ownership o;
    public Expr A;
    public Expr G;
    public Expr G_no_annos;

    public String delim, code; // if primitive

    public Define() {
	super(DEFINE);
    }

    public Define(boolean spec, boolean primitive, boolean trusted, boolean type_family_abbrev,
		  boolean predicate, boolean abbrev,
		  Const c, Ownership o, Expr A, Expr G, Expr G_no_annos, String delim, String code) {
	super(DEFINE);
	this.spec = spec;
	this.primitive = primitive;
	this.c = c;
	this.o = o;
	this.A = A;
	this.G = G;
	this.G_no_annos = G_no_annos;
	this.trusted = trusted;
	this.type_family_abbrev = type_family_abbrev;
	this.predicate = predicate;
	this.abbrev = abbrev;
	this.delim = delim;
	this.code = code;
    }

    public void process(Context ctxt) {

	if (spec && primitive) 
	    handleError(ctxt,
			"A Define-command is labeled as both \"spec\" and \"primitive\"."
			+"\n\n1. the defined constant: "+c.toString(ctxt));

	boolean spec_mode = G.isProof(ctxt) || spec || primitive || predicate || abbrev;

	boolean dont_classify = 
	    abbrev || (trusted && (A != null) && G.isProof(ctxt));

	Expr cG = null;
	if (dont_classify) 
	    // A != null
	    cG = A;
	else {
	    if (ctxt.getFlag("debug_define")) {
		ctxt.w.println("Define about to classify "+G.toString(ctxt));
		ctxt.w.flush();
	    }
	    cG = G.classify(ctxt, Expr.NO_APPROX, spec_mode); 
	}
	    
	if (A == null)
	    A = cG;
	else {
	    A.classify(ctxt); /* this needs to be done to set
				 ownership statuses correctly */
	    if (A != cG && !cG.defEq(ctxt,A,spec_mode))
		handleError(ctxt,
			    "The classifier computed for the body of a "
			    +"definition does not\n"
			    +"match the declared classifier.\n"
			    +"1. the defined constant: "
			    +c.toString(ctxt)+"\n"
			    +"2. declared classifier: "
			    +A.toString(ctxt)+"\n"
			    +"3. computed classifier: "
			    +cG.toString(ctxt));
	}

	if (!spec_mode)
	    G.checkSpec(ctxt, false /* in_type */, c.pos);

	if (spec) 
	    ctxt.markSpec(c); 
	if (primitive)
	    ctxt.makeOpaque(c);

	if (type_family_abbrev) {
	    /* check that G satisfies the syntactic requirements for
	       one of these, namely that it is a fun-term building a
	       type application. */

	   if (G.construct != Expr.FUN_TERM)
		handleError(ctxt,
			    "A type family abbreviation is not a fun-term.\n"
			    +"1. the given expression: "+G.toString(ctxt));
	   FunTerm f = (FunTerm)G;
	   f = (FunTerm)f.coalesce(ctxt, spec);

	   if (f.body.construct != Expr.CONST && f.body.construct != Expr.TYPE_APP)
		handleError(ctxt,
			    "The body of a type family abbreviation is not"
			    +" a constant or a type-level application.\n"
			    +"1. the body: "+f.body.toString(ctxt));
	    
	    ctxt.markTypeFamilyAbbrev(c);

	    /* we need to build the version of G without annotations
	       carefully, since these type family abbreviations work
	       differently from other fun-terms. */
	    
	    G_no_annos = f.dropAnnosSpecial(ctxt);
	    G = f;
	}
	else if (predicate) {
	    /* check that G satisfies the syntactic requirements for
	       one of these, namely that it is a fun-term building a
	       formula. */

	   if (G.construct != Expr.FUN_TERM)
		handleError(ctxt,
			    "A type family abbreviation is not a fun-term.\n"
			    +"1. the given expression: "+G.toString(ctxt));
	   FunTerm f = (FunTerm)G;
	   f = (FunTerm)f.coalesce(ctxt, spec);

	   if (!f.body.isFormula(ctxt))
		handleError(ctxt,
			    "The body of a predicate is not"
			    +" a formula.\n"
			    +"1. the body: "+f.body.toString(ctxt));
	    
	    ctxt.markPredicate(c);

	    /* we need to build the version of G without annotations
	       carefully, since these type family abbreviations work
	       differently from other fun-terms. */
	    
	    G_no_annos = f.dropAnnosSpecial(ctxt);
	    G = f;
	}
	else {
	    G_no_annos = G.dropAnnos(ctxt);
	    Expr tmp = G_no_annos.dropAnnos(ctxt);
	    if (G_no_annos != tmp
		/* && ctxt.getFlag("check_drop_annos_idem") */)
		handleError(ctxt,
			    "Internal error: dropping annotations twice does "
			    +"not give the same (in-memory) expression."
			    +"\n1. Expression: "+G.toString(ctxt)
			    +"\n2. With annotations dropped once: "
			    +G_no_annos.toString(ctxt)
			    +"\n3. With annotations dropped twice: "
			+tmp.toString(ctxt));
	}

	ctxt.define(c, o, A, G, G_no_annos, delim, code);

	if(trusted)
	    ctxt.markTrusted(c);
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("Define ");
	if (trusted)
	    w.print("trusted ");
	if (spec)
	    w.print("spec ");
	if (code != null)
	    w.print("primitive ");
	if (type_family_abbrev)
	    w.print("type_family_abbrev ");

	c.do_print(w, ctxt);
	
	if ( A != null)
	{
	    w.print(" : ");
	    A.print(w, ctxt);
	}
	
	w.print(" := ");
	Expr tmp = G;
	if (ctxt.getFlag("print_no_annos"))
	    tmp = G_no_annos;
	tmp.print(w, ctxt);

	if (delim != null) {
	    w.print("<<"+delim);
	    w.println(code);
	    w.println(delim);
	}

	w.println(".");
	w.flush();
    }

    public java.util.Set getDependences() {
        java.util.Set s = A.getDependences();
        s.addAll(G.getDependences());
        return s;
    }

    // this is just used for definitions of primitives.
    public guru.carraway.Primitive toCarraway(Context ctxt) {
	if (!primitive)
	    handleError(ctxt,"Internal error: toCarraway() function called on a non-primitive definition.");
	guru.carraway.Primitive P = new guru.carraway.Primitive();

	guru.carraway.Context cctxt = ctxt.carraway_ctxt;

	P.s = cctxt.newSym(c.name,c.pos,true);
	P.T = A.toCarrawayType(ctxt,false);
	P.delim = delim;
	P.code = code;
	return P;
    }
}
