package guru;

import java.util.Stack;
import java.util.ArrayList;
import java.util.ListIterator;
import java.util.Iterator;

public class Terminates extends Expr{

    public Expr t;
    public Expr P;

    public Terminates() {
	super(TERMINATES);
    }

    public Terminates(TermApp t, Expr P) {
	super(TERMINATES);
	this.t = t;
	this.P = P;
    }

    public void do_print(java.io.PrintStream w,
		      Context ctxt) {
	w.print("terminates ");
	t.print(w,ctxt);
	w.print(" by ");
	P.print(w,ctxt);
    }

    public int numOcc(Expr e) {
	return t.numOcc(e) + P.numOcc(e);
    }

    public Expr subst(Expr e, Expr x) {
	Expr nt = t.subst(e,x), nP = P.subst(e,x);
	if (nt != t || nP != P)
	    return new Terminates((TermApp)nt, nP);
	return this;
    }

    public Expr classify(Context ctxt, int approx, boolean spec) {
        return t.classify(ctxt, approx, spec);
    }

    public boolean defEqNoAnno(Context ctxt, Expr ee, boolean spec) {
	ee = ee.defExpandTop(ctxt, true, spec);
	if (ee.construct != construct) {
	    ctxt.notDefEq(this,ee);
	    return false;
	}

	return t.defEqNoAnno(ctxt,((Terminates)ee).t, spec);
    }

    public Expr dropAnnos(Context ctxt) {
	return t.dropAnnos(ctxt);
    }

    public boolean termTerminates(Context ctxt) {
        boolean dbg = ctxt.getFlag("debug_terminates");

        if(dbg) {
            ctxt.w.println("========== terminate-checking a "
                               +"terminates-casting expression: ==========");
            ctxt.w.println("term : "+t.toString(ctxt));
            ctxt.w.println("Ptype: "+P.classify(ctxt).toString(ctxt));
            ctxt.w.println("================================"
                               +"=========================================");
	    ctxt.w.flush();
        }

        /* We implement the terminating judgments:
         *
         * P : Forall(xs).Exists(y).{ (f xs) = y }
         * t_i : T_i
         * x_i : T_i
         * t_i terminates
         * -------------------------------------------------------------
         * terminates (f ts) by P   terminates
         *
         *
         * P : Exists(y).{ (f ts) = y }
         * t_i terminates
         * -------------------------------------------------------------
         * terminates (f ts) by P   terminates
         */

        ArrayList ts = new ArrayList();
        ArrayList xs = null;
        ArrayList us = new ArrayList();
        Expr x1, x2;
        Var y;
        Stack s = new Stack();

        /*
         * 1. P must have the form Forall(xs).Exists(y).{ (f xs) = y }.
         *    This is separated into four subchecks, all of which must hold:
         *
         *    (a) P ends with an equational proof
         *
         *    (b) the rhs of P's equational proof is y
         *
         *    (c) (f ts) is in fact a term application
         *
         *    (d) the lhs of P's equational proof is a term application
         */

        /* get the type of P */
        Expr p = P;
        p = p.classify(ctxt);
        Expr pclass = p;

        /* now get xs */
        if(p.construct == FORALL) {
            xs = new ArrayList();
            do {
                Forall fa = (Forall)p;
                for(int i = 0, iend = fa.vars.length; i < iend; i++)
                    xs.add(fa.vars[i]);
                p = fa.body;
            } while(p.construct == FORALL);
        }

        if(p.construct != EXISTS || ((Exists)p).vars.length != 1)
            handleError(ctxt, "terminates...by requires a proof proving a"
                        +"formula of the form\n"
			+"Forall(xs).Exists(y).{ (f xs) = y } or "
                        +"Exists(y).{ (f ts) = y }."
			+"\n1. the formula proved: "+p.toString(ctxt));
        y = ((Exists)p).vars[0];
        p = ((Exists)p).body;

        if(dbg) {
            ctxt.w.println("checking (1a)... equational proof: "
                               +p.toString(ctxt));
	    ctxt.w.flush();
	}
        if(p.construct == ATOM && ((Atom)p).equality) {
            Atom a = (Atom)p;
            if(dbg) {
                ctxt.w.println("checking (1b)... "+a.Y2.toString(ctxt)
                                   +" = "+y.toString(ctxt));
		ctxt.w.flush();
	    }
            if(a.Y2 != y)//!a.Y2.defEq(ctxt, y))
                handleError(ctxt, "terminates...by proof malformed: "
                            +"expected Exists(y).{ ... = y } but got "
                            +"Exists("+y.toString(ctxt)+").{ ... = "
                            +a.Y2.toString(ctxt)+" }\n"
                            +"Proof's classification is: "
                            +pclass.toString(ctxt));
            p = a.Y1;
        } else handleError(ctxt, "terminates...by proof malformed: "
                           +"expected equational proof but got "
                           +p.toString(ctxt)+"\n"
                           +"Proof's classification is: "
                           +pclass.toString(ctxt));
        /* p is now the lhs of the equation */

        /* now get f1 and its args */
        t = t.defExpandTop(ctxt);
        if(dbg) {
            ctxt.w.println("checking (1c)... terminates-cast was "
                               +"given a term app: "+t.toString(ctxt));
	    ctxt.w.flush();
	}
        if(t.construct != TERM_APP)
            handleError(ctxt, "terminates-casting can only be applied "
                        +"to term applications,\nnot: "+t.toString(ctxt)+"\n"
                        +"with type: "+t.classify(ctxt).toString(ctxt));
        x1 = ((App)t).spineForm(ctxt, false, true, true);

        /* now get f2 and its args */
        x2 = p.defExpandTop(ctxt);
        if(dbg) {
            ctxt.w.println("checking (1d)... P's lhs a term application: "
                               +x2.toString(ctxt));
	    ctxt.w.flush();
	}
        if(x2.construct != TERM_APP)
            handleError(ctxt, "terminates-casting can only take proofs "
                        +"about term applications,\n"
                        +"not: "+x2.toString(ctxt)+"\n"
                        +"with type: "+x2.classify(ctxt).toString(ctxt));
        x2 = ((App)x2).spineForm(ctxt, false, true, true);

	x1 = x1.dropAnnos(ctxt);
	x2 = x2.dropAnnos(ctxt);

	if (x1.construct == CONST || x1.construct == FUN_TERM)
	    /* dropping annotations reduced this to a value. */
	    return true;

        if(dbg) {
            ctxt.w.println("with annotations dropped we have: "
                               +x1.toString(ctxt)+" and "
                               +x2.toString(ctxt));
	    ctxt.w.flush();
	}

        /* 2. The function f in t and the function f in P must be the same. */

        if(dbg) {
            ctxt.w.println("checking (2)... function equality: "
                               +((App)x1).head.toString(ctxt)+" = "
                               +((App)x2).head.toString(ctxt));
	    ctxt.w.flush();
	}
        if(!((App)x1).head.defEq(ctxt, ((App)x2).head))
            handleError(ctxt, "terminates...by proof doesn't match the cast; "
                        +"the cast is on an application of function "
                        +((App)x1).head.toString(ctxt)+
                        " but the proof is about an application of the "
                        +"function "+((App)x2).head.toString(ctxt)+"\n"
                        +"The casted application: "+x1.toString(ctxt)+"\n"
                        +"The proof application: "+x2.toString(ctxt)+"\n"
                        +"The proof's full classifier: "+pclass.toString(ctxt));

        /* 3. |ts| must equal |xs|. */

        if(dbg) {
            ctxt.w.println("checking (3)... application arity equality: "
                               +((App)x1).X.length+" = "+((App)x2).X.length);
	    ctxt.w.flush();
	}
        if(((App)x1).X.length != ((App)x2).X.length)
            handleError(ctxt, "terminates...by proof doesn't match the cast; "
                        +"there is a function arity mismatch in the "
                        +"applications\n"
                        +"The casted application: "+x1.toString(ctxt)+"\n"
                        +"The proof application: "+x2.toString(ctxt)+"\n"
                        +"The proof's full classifier: "+pclass.toString(ctxt));

        if(xs == null) {
            /* 4. ts in p must be the same as ts in t */

            if(dbg) {
                ctxt.w.println("checking (4)... application equality");
		ctxt.w.flush();
	    }
            for(int i = 0; i < ((App)x1).X.length; ++i) {
                if(((App)x2).X[i].construct != BANG &&
                   !((App)x1).X[i].defEq(ctxt, ((App)x2).X[i]))
                    handleError(ctxt, "terminates...by proof doesn't match "
                                +"the cast; a proof application argument "
                                +"doesn't match a casted term application "
                                +"argument\n"
                                +"Argument position: "+i+"\n"
                                +"Casted term application argument: "
                                +((App)x1).X[i].toString(ctxt)+"\n"
                                +"Proof term application argument: "
                                +((App)x2).X[i].toString(ctxt)+"\n"
                                +"The full casted application: "
                                +x1.toString(ctxt)+"\n"
                                +"The full proof application: "
                                +x2.toString(ctxt)+"\n"
                                +"The proof's full classifier: "
                                +pclass.toString(ctxt));
            }
        } else {
            /* 4. The arguments of the lhs term application must
	          be distinct universally quantified variables. */

            if(dbg) {
                ctxt.w.println("checking (4)... lhs term app uses "
                                   +"distinct quantified vars...");
		ctxt.w.flush();
	    }
	    ArrayList S = new ArrayList();
            Iterator it = xs.iterator();
	    for (int i = 0, iend = ((App)x2).X.length; i < iend; i++)
		S.add(((App)x2).X[i]);
	    while(it.hasNext()) {
                Var e = (Var)it.next();
		S.remove(e);
            }
	    if (S.size() != 0)
		handleError(ctxt, "A termination proof proves the wrong"
			    +" form of equation.  The lhs of\nthe equation"
			    +" should apply a function to distinct"
			    +" universally\nquantified variables, but\n"
			    +" it does not."
			    +" \n1. the formula proved: "
			    +pclass.toString(ctxt)
			    +" \n2. a disallowed argument: "
			    +((Expr)S.get(0)).toString(ctxt));
        }

        /* All done. */
        if(dbg) {
            ctxt.w.println("======================================"
                               +"============================");
            ctxt.w.println("G |- "+toString(ctxt)+"   terminates");
            ctxt.w.println("======================================"
                               +"============================");
	    ctxt.w.flush();
        }

	/* do not call on x1, because we have dropped annotations on x1,
	   to get rid of specificational arguments.  But t is still the
	   original typed term, so any terminates...by-terms it contains
	   are still there (they would get erased by dropAnnos()). */
        return ((TermApp)t).headAndArgsTerminate(ctxt, true);
    }

    public java.util.Set getDependences() {
        java.util.Set s = t.getDependences();
        s.addAll(P.getDependences());
        return s;
    }

    public void checkSpec(Context ctxt, boolean in_type){
	t.checkSpec(ctxt, in_type);
    }

    public void getFreeVarsComputational(Context ctxt, 
					 java.util.Collection vars) {
	t.getFreeVarsComputational(ctxt,vars);
    }

}
