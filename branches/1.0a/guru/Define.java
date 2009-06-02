package guru;

import java.util.Iterator;

public class Define extends Command {
    public boolean spec;
    public boolean trusted;
    public boolean type_family_abbrev;
    public boolean predicate;
    public boolean abbrev;

    public Const c;
    public Expr A;
    public Expr G;
    public Expr G_no_annos;

    public Define() {
	super(DEFINE);
    }

    public Define(boolean spec, boolean trusted, boolean type_family_abbrev,
		  boolean predicate, boolean abbrev,
		  Const c, Expr A, Expr G, Expr G_no_annos) {
	super(DEFINE);
	this.spec = spec;
	this.c = c;
	this.A = A;
	this.G = G;
	this.G_no_annos = G_no_annos;
	this.trusted = trusted;
	this.type_family_abbrev = type_family_abbrev;
	this.predicate = predicate;
	this.abbrev = abbrev;
    }

    public void process(Context ctxt) {

	boolean spec_mode = G.isProof(ctxt) || spec || predicate || abbrev;

	boolean dont_classify = abbrev || (trusted && (A != null) && G.isProof(ctxt));

	Expr cG = null;
	if (dont_classify) 
	    // A != null
	    cG = A;
	else {
	    if (ctxt.getFlag("debug_define")) {
		ctxt.w.println("Define about to classify "+G.toString(ctxt));
		ctxt.w.flush();
	    }
	    cG = G.classify(ctxt, Expr.NO_APPROX, spec); 
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
	    G.checkSpec(ctxt, false /* in_type */);

	if (spec) {
	    ctxt.markSpec(c); 
	    ctxt.makeOpaque(c); // so the compiler knows to stub this out
	    if (ctxt.isTypeCtor(c)) {
		// and tell the compiler to stub out its term ctors
		Iterator it = ctxt.getTermCtors(c).iterator();
		while (it.hasNext()) {
		    Const c2 = (Const)it.next();
		    ctxt.makeOpaque(c2);
		}
	    }
	}

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

	   if (f.body.construct != Expr.TYPE_APP)
		handleError(ctxt,
			    "The body of a type family abbreviation is not"
			    +" a type-level application.\n"
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

	ctxt.define(c, A, G, G_no_annos);

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

	w.println(".");
	w.flush();
    }

    public java.util.Set getDependences() {
        java.util.Set s = A.getDependences();
        s.addAll(G.getDependences());
        return s;
    }
}
