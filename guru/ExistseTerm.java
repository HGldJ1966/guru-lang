package guru;

public class ExistseTerm extends Expr{

    public Expr P;
    public Expr t;
    public Expr T;

    public ExistseTerm() {
	super(EXISTSE_TERM);
    }

    public ExistseTerm(Expr P, Expr t) {
	super(EXISTSE_TERM);
	this.P = P;
	this.t = t;
	this.T = null;
    }

    public Expr dropAnnos(Context ctxt) {
	return t.dropAnnos(ctxt);
    }

    public void do_print(java.io.PrintStream w,
			 Context ctxt) {
	w.print("existse_term ");
	if (ctxt.getFlag("show_some_computed_types")) {
	    w.print("%- ");
	    if (T == null)
		w.print(" <no computed type>");
	    else
		T.print(w,ctxt);
	    w.print(" -% ");
	}
	P.print(w,ctxt);
	w.print(" ");
	t.print(w,ctxt);
    }

    public int numOcc(Expr e) {
	return P.numOcc(e) + t.numOcc(e);
    }

    public Expr subst(Expr e, Expr x) {
	Expr nP = P.subst(e,x), nt = t.subst(e,x);
	Expr nT = (T != null ? T.subst(e,x) : null);
	if (nP != P || nt != t || nT != T) {
	    ExistseTerm ret = new ExistseTerm(nP, nt);
	    ret.T = nT;
	    return ret;
	}
	return this;
    }

    public Expr classify(Context ctxt, int approx, boolean spec) {
	if (approx > 0) {
	    if (T == null)
		handleError(ctxt,
			    "Approximate type checking called on an "
			    +"existse-term which has not\n"
			    +"been type checked yet.");
	    return T;
	}

	Expr cP = P.classify(ctxt,approx,spec).defExpandTop(ctxt);
	Expr ct = t.classify(ctxt,approx,spec).defExpandTop(ctxt);

	if (cP.construct != EXISTS)
	    handleError(ctxt,
			"The proof given to existse_term does not prove an"
			+" existential.\n"
			+"1. the proof's classifier: "+cP.toString(ctxt));
	if (ct.construct != FUN_TYPE)
	    handleError(ctxt,
			"The term given to existse_term is not a"
			+" function.\n"
			+"1. the term's classifier: "+ct.toString(ctxt));
	Abstraction a1 = (Exists)cP;
	FunType a2 = (FunType)ct;

	a1 = new Exists((Abstraction) a1.coalesce(ctxt,true));
	a2 = new FunType((FunAbstraction) a2.coalesce(ctxt,true));

	Var v2;
	Expr body1 = a1.body;
	if (a1.vars.length > a2.vars.length-1)
	{
	    Var _v[] = new Var[a1.vars.length-(a2.vars.length-1)];
	    Expr _t[] =new Expr[a1.types.length-(a2.types.length-1)];;

	    System.arraycopy(a1.vars, a2.vars.length-1, _v, 0,
			     a1.vars.length-(a2.vars.length-1));
	    System.arraycopy(a1.types, a2.types.length-1, _t, 0,
			     a1.vars.length-(a2.vars.length-1));

	    body1 = new Exists(_v,_t,a1.body);
	}
	for (int vp = 0; a2.vars.length > 1 && vp < a1.vars.length ; vp++) {

	    v2 = a1.vars[vp];

	    // for the benefit of subsequent calls to defEq (which calls
	    // dropAnnos):
	    ctxt.setClassifier(v2,a1.types[vp]);

	    if (!a1.types[vp].defEq(ctxt, a2.types[0], approx, spec))
		handleError(ctxt,
			    "In an existse_term, the " + (vp + 1) +
			    "th quantification is of the wrong type:\n" +
			    "1. existential's type: (" +
			    a1.vars[vp].toString(ctxt) + " : "
			    + a1.types[vp].toString(ctxt) + ")\n" +
			    "2. function's type: (" +
			    a2.vars[0].toString(ctxt) +
			    " : " + a2.types[0].toString(ctxt) + ")\n" );
	    if (a2.owned[0].status != Ownership.SPEC &&
		!a2.types[0].isFormula(ctxt)) 
		handleError(ctxt,
			    "The "+(new Integer(vp)).toString()+"th "
			    +"argument in the functional term of an"
			    +" existse_term\nis not specificational.\n"
			    +"1. the argument: "+a2.vars[vp].toString(ctxt));
	    a2 = (FunType) a2.instantiate(v2);
	}

	Expr body2 = a2;

	if (body2.construct != FUN_TYPE)
	    handleError(ctxt,
			"In an existse_term, the functional term does not"
			+" accept enough inputs\n"
			+"1. the term's type: "+ct.toString(ctxt));
	FunType a2a = (FunType)body2;

	if (!a2a.types[0].defEq(ctxt, body1, approx, spec))
	    handleError(ctxt,
			"The body of the proved existential does not match"
			+" the appropriate input of the functional term.\n"
			+"These two expressions should be definitionally "
			+"equal:\n1. existential body: "
			+body1.toString(ctxt)+"\n"
			+"2. function's argument type: "
			+a2a.types[0].toString(ctxt) );

	Expr body2a = a2a.body;

	int cnt = body2a.numOcc(a2a.vars[0]);
	for (int j=0; j < a1.vars.length;j++)
	    cnt += body2a.numOcc(a1.vars[j]);


	if (cnt > 0)
	    handleError(ctxt,
			"The return type of the functional term"
			+" refers to the quantified variables.\n"
			+"1. the type: "+ct.toString(ctxt));
	T = body2a;
	return T;
    }

    public void getFreeVarsComputational(Context ctxt, 
					 java.util.Collection vars) {
	t.getFreeVarsComputational(ctxt,vars);
    }

    public java.util.Set getDependences() {
        java.util.Set s = P.getDependences();
        s.addAll(t.getDependences());
        return s;
    }

    public void checkSpec(Context ctxt, boolean in_type, Position p) {
	t.checkSpec(ctxt, in_type, pos);
    }

    public void checkTermination(Context ctxt) {
	t.checkTermination(ctxt);
    }

}

