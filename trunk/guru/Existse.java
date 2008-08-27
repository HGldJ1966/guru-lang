package guru;

public class Existse extends Expr{

    public Expr P1;
    public Expr P2;

    public Existse() {
	super(EXISTSE);
    }

    public Existse(Expr P1, Expr P2) {
	super(EXISTSE);
	this.P1 = P1;
	this.P2 = P2;
    }

    public Expr dropAnnos(Context ctxt) {
	return new Bang();
    }

    public void do_print(java.io.PrintStream w,
		      Context ctxt) {
	w.print("existse ");
	P1.print(w,ctxt);
	w.print(" ");
	P2.print(w,ctxt);
    }

    public int numOcc(Expr e) {
	return P1.numOcc(e) + P2.numOcc(e);
    }

    public Expr subst(Expr e, Expr x) {
	Expr nP1 = P1.subst(e,x), nP2 = P2.subst(e,x);
	if (nP1 != P1 || nP2 != P2)
	    return new Existse(nP1, nP2);
	return this;
    }

    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars) {
	P1.checkTermination(ctxt,IH,arg,vars);
	P2.checkTermination(ctxt,IH,arg,vars);
    }

    public Expr classify(Context ctxt) {
	Expr cP1 = P1.classify(ctxt).defExpandTop(ctxt);
	Expr cP2 = P2.classify(ctxt).defExpandTop(ctxt);

	if (cP1.construct != EXISTS)
	    handleError(ctxt,
			"First proof given to existse does not prove an"
			+" existential.\n"
			+"1. the proof's classifier: "+cP1.toString(ctxt));
	if (cP2.construct != FORALL)
	    handleError(ctxt,
			"Second proof given to existse does not prove a"
			+" universal.\n"
			+"1. the proof's classifier: "+cP2.toString(ctxt));
	Abstraction a1 = (Exists)cP1;
	Forall a2 = (Forall)cP2;

	a1 = new Exists((Abstraction) a1.coalesce(ctxt,true));
	a2 = new Forall((Abstraction) a2.coalesce(ctxt,true));

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
	int vp = 0;
	for (vp=0; a2.vars.length > 1 && vp < a1.vars.length ; vp++) {

	    v2 = a1.vars[vp];

	    // for the benefit of subsequent calls to defEq (which calls
	    // dropAnnos):
	    ctxt.setClassifier(v2,a1.types[vp]);

	    if (!a1.types[vp].defEq(ctxt, a2.types[0]))
		handleError(ctxt,
			    "The " + (vp + 1) +
			    "th quantification is of the wrong type:\n" +
			    "1. existential type: (" +
			    a1.vars[vp].toString(ctxt) + " : "
			    + a1.types[vp].toString(ctxt) + ")\n" +
			    "2. universal type: (" +
			    a2.vars[0].toString(ctxt) +
			    " : " + a2.types[0].toString(ctxt) + ")\n" );
	    a2 = (Forall) a2.instantiate(v2);
	}

	Expr body2 = a2;

	if (body2.construct != FORALL)
	    handleError(ctxt,
			"Proved universal formula does not quantify enough"
			+" variables\n"
			+"1. the universal: "+cP2.toString(ctxt));
	Forall a2a = (Forall)body2;



	if (!a2a.types[0].defEq(ctxt, body1))
	    handleError(ctxt,
			"The body of the proved existential does not match"
			+" the expected universal formula.\n"
			+"These two formulas should be definitionally equal:\n"
			+"1. existential body: "+body1.toString(ctxt)+"\n"
			+"2. hypothesis of universal: "
			+a2a.types[0].toString(ctxt) );

	Expr body2a = a2a.next();

	int cnt = body2a.numOcc(a2a.vars[0]);
	for (int j=0; j < a1.vars.length;j++)
		cnt += body2a.numOcc(a1.vars[j]);


	if (cnt > 0)
	    handleError(ctxt,
			"Body of proved universal refers to the quantified"
			+" variables.\n"
			+"1. the universal: "+cP2.toString(ctxt));
	return body2a;
    }

    public java.util.Set getDependences() {
        java.util.Set s = P1.getDependences();
        s.addAll(P2.getDependences());
        return s;
    }
}
