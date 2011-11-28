package guru;

import java.util.Stack;

public class TypeApp extends ReducibleApp{
    
    public TypeApp() {
	super(TYPE_APP);
    }
    
    public TypeApp(App a) {
	super(TYPE_APP, a.head, a.X);
    }

    public TypeApp(Expr head, Expr[] X) {
	super(TYPE_APP, head, X);
    }

    public void do_print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("<");
	super.do_print(w,ctxt);
	w.print(">");
    }

    public Expr subst(Expr e, Expr x) {
	App s = (App)super.subst(e,x);
	if (s != this)
	    return new TypeApp(s);
	return this;
    }
    
    public Expr getHeadKind(Context ctxt) {
	return ctxt.tkind;
    }

    public Expr spineForm(Context ctxt, boolean drop_annos, boolean spec,
			 boolean expand_defs) {
	Expr s = super.spineForm(ctxt, drop_annos, spec, expand_defs);
	if (s == this)
	    return this;
	if (s.construct == CONST)
	    return s;
	return new TypeApp((App)s);
    }

    protected boolean headBetaOk(Context ctxt, boolean spec) {
	Const c = (Const)head;

	if (!spec && ctxt.isOpaque(c))
	    return false;

	return ctxt.isTypeFamilyAbbrev(c); 
    }

    public Expr dropAnnos(Context ctxt) {
	App s = (App)super.dropAnnos(ctxt);
	if (s != this)
	    return new TypeApp(s);
	return this;
    }

    public Expr classify(Context ctxt, int approx, boolean spec) {
	if (approx > NO_APPROX) {
	    return ctxt.type;
	}

	if (ctxt.getFlag("debug_classify_apps")) {
	    ctxt.w.print("(Classifying type app ");
	    print(ctxt.w,ctxt);
	    ctxt.w.println("");
	    ctxt.w.flush();
	}

	Expr ret = super.classify(ctxt,approx,spec);

	if (ctxt.getFlag("debug_classify_apps")) {
	    ctxt.w.println(") Classifier is:");
	    ret.print(ctxt.w,ctxt);
	    ctxt.w.println("");
	    ctxt.w.flush();
	}

	return ret;
    }

    /* a type application is compiled to the head of its spine form,
       which cannot be a variable in our type system.  So it has no
       free vars. */
    public void getFreeVarsComputational(Context ctxt,
					 java.util.Collection vars) { }

    public guru.carraway.Expr toCarrawayType(Context ctxt, boolean dtype) {
	return head.toCarrawayType(ctxt,dtype);
    }
}
