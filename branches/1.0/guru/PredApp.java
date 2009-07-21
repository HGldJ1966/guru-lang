package guru;

import java.util.Stack;

public class PredApp extends ReducibleApp{
    
    public PredApp() {
	super(PRED_APP);
    }
    
    public PredApp(App a) {
	super(PRED_APP, a.head, a.X);
    }

    public PredApp(Expr head, Expr[] X) {
	super(PRED_APP, head, X);
    }

    public void do_print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("@<");
	super.do_print(w,ctxt);
	w.print(">");
    }

    public Expr subst(Expr e, Expr x) {
	App s = (App)super.subst(e,x);
	if (s != this)
	    return new PredApp(s);
	return this;
    }
    
    public Expr getHeadKind(Context ctxt) {
	return ctxt.fkind;
    }

    /* we cannot use this, since beta-reduction may return an arbitrary
       formula. */
    public Expr spineForm(Context ctxt, boolean drop_annos, boolean spec,
			  boolean expand_defs) {
	handleError(ctxt,"Internal error: spineForm called on a PredApp.");
	return null;
    }

    protected boolean headBetaOk(Context ctxt, boolean spec) {
	Const c = (Const)head;

	if (!spec && ctxt.isOpaque(c))
	    return false;

	return ctxt.isPredicate(c); 
    }

    public Expr dropAnnos(Context ctxt) {
	App s = (App)super.dropAnnos(ctxt);
	if (s != this)
	    return new PredApp(s);
	return this;
    }

    protected boolean defEqNoAnno(Context ctxt, Expr ee, boolean spec) {
	Expr e1 = doBeta(ctxt,true,spec,true);
	if (e1 != this)
	    return e1.defEqNoAnno(ctxt,ee,spec);
	if (ee.construct != PRED_APP) {
	    ctxt.notDefEq(e1, ee);
	    return false;
	}
	Expr e2 = ((PredApp)ee).doBeta(ctxt,true,spec,true);
	if (e2 != ee)
	    return defEqNoAnno(ctxt,e2,spec);
	return super.defEqNoAnno(ctxt,ee,spec);
    }


    /* a type application is compiled to the head of its spine form,
       which cannot be a variable in our type system.  So it has no
       free vars. */
    public void getFreeVarsComputational(Context ctxt,
					 java.util.Collection vars) { }

}
