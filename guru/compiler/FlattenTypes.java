package guru.compiler;

import guru.*;
import java.util.*;
import java.io.*;

public class FlattenTypes {
    Context src;
    Context dst;

    Vector types;
    HashSet in_types;
    boolean dbg;

    public FlattenTypes() {
	types = new Vector();
	in_types = new HashSet();
    }

    public void process(Context src, Context dst) {
	this.src = src;
	this.dst = dst;

	dbg = src.getFlag("debug_flatten_types");

	if (dbg) {
	    src.w.println("Flattening types begins.");
	    src.w.println("First flattening type ctors and the types of their"
			  +" term ctors.");
	    src.w.flush();
	}

	/*
	 * first flatten types of type and term ctors
	 *
	 * We do not assume that the declarations are in the right order.
	 */

	types = new Vector();

	// we need to flatten all the types of our term and type ctors.
	// We add the type ctors to the Vector "types", so that the Compiler
	// can emit typedefs and types in the proper order.
	Iterator it = dst.getTypeCtors().iterator();
	while(it.hasNext()) {
	    Const d = (Const)it.next();
	    dst.reclassifyTypeCtor(d,flattenType(dst.getClassifier(d),false));

	    if (dbg) {
		src.w.println("Inductive type: "+d.toString(src));
		src.w.flush();
	    }		    

	    // before we add the term ctors, we need to prevent the
	    // type ctor from being added to the types Vector.  We
	    // will add it after the term ctors, below; but only if we
	    // did not already add it previously (due to processing
	    // some other types -- as noted above, we do not assume
	    // the declarations are in order).
	    boolean do_add = !in_types.contains(d);
	    in_types.add(d);

	    Iterator it2 = dst.getTermCtors(d).iterator();
	    while (it2.hasNext()) {
		Const c = (Const)it2.next();
		Expr T = dst.getClassifier(c);
		
		/*T.print(dst.w,dst);
		  dst.w.print(" --> "); */
		
		Expr fT = flattenType(T, false);
		dst.reclassifyTermCtor(c,fT);
		
		/*		fT.print(dst.w,dst);
		dst.w.println("");
		dst.w.flush();*/
	    }

	    // we need to add the type ctor after its term ctors,
	    // since the Compiler emits code for the latter when
	    // it finds the former in "types", and we may have
	    // added other Consts to "types" when we flatten the
	    // term ctors' types.
	    if (do_add)
		types.add(d);
	}

	/*
	 * now flatten types occurring in defined terms
	 */

	if (dbg) {
	    src.w.println("Now flattening types found in defined terms.");
	    src.w.flush();
	}

	it = src.getDefinedConsts().iterator();
	while(it.hasNext()) {
	    Const c = (Const)it.next();

	    Expr T = src.getClassifier(c);

	    if (src.isTypeFamilyAbbrev(c)) {
		if (dbg) {
		    src.w.println("Encountered this type family abbrev while "
				  +"flattening types: "+c.toString(src));
		    src.w.flush();
		}
		continue;
	    }

	    if (c.isTypeOrKind(src))
		// we are handling these elsewhere, as they arise
		continue;

	    if (dbg) {
		src.w.println("Flattening types found in definition of "
			      +c.toString(src));
		src.w.flush();
	    }

	    Expr t = src.getDefBody(c);

	    if (src.isOpaque(c)) {
		dst.define(c,flattenType(T,false),t,src.getDefBodyNoAnnos(c));
		dst.makeOpaque(c);
		continue;
	    }

	    /*src.w.println(c.name);
	      src.w.flush();*/
	    
	    Expr nt = process(t);

	    /*src.w.print("Define ");
	    src.w.print(c.name);
	    src.w.print(" := ");
	    nt.print(src.w,src);
	    src.w.println(";;");
	    src.w.flush();*/
	    
	    // if this is a constant, we handle it differently in Compiler.
	    boolean flatten_type = (nt.construct == Expr.CONST);
	    dst.define(c, flattenType(T,flatten_type), nt, nt.dropAnnos(dst));
	}

	if (dbg) {
	    src.w.println("Flattening types ends.");
	    src.w.flush();
	}
    }

    protected void addType(Const c) {
	if (!in_types.contains(c)) {
	    /* a ctor which we will process later, but which we must
	       add to types now to get the order right */
	    if (dbg) {
		dst.w.println("Adding type "+c.toString(dst));
		dst.w.flush();
	    }
	    types.add(c);
	    in_types.add(c);
	}
    }

    protected Const addDef(Const c) {
	if (src.isDefined(c) && !dst.isDefined(c)) {
	    dst.define(c, src.getClassifier(c), src.getDefBody(c), 
		       src.getDefBodyNoAnnos(c));
	    if (src.isOpaque(c))
		dst.makeOpaque(c);
	    if (src.isTypeFamilyAbbrev(c))
		dst.markTypeFamilyAbbrev(c);
	}

	addType(c);

	return c;
    }

    protected Expr[] flattenType(Var[] xs, Expr[] Ts, boolean do_define) {
	int iend = Ts.length;
	Expr[] nTs = new Expr[iend];
	for (int i = 0; i < iend; i++) {
	    nTs[i] = flattenType(Ts[i],do_define);
	    dst.setClassifier(xs[i],nTs[i]);
	}
	return nTs;
    }


    protected Expr flattenType(Expr T, boolean do_define) {
	if (dbg) {
	    dst.w.println("Flattening "+T.toString(src));
	    dst.w.flush();
	}

	if (T.construct == Expr.CONST) {
	    Expr T1 = T.defExpandTop(src,false,false);
	    if (dbg) {
		dst.w.println("Expanding def to "+T1.toString(src));
		dst.w.flush();
	    }
	    if (T != T1)
		flattenType(T1,false);
	    return addDef((Const)T);
	}
	    
	if (T.construct == Expr.TYPE_APP) {
	    TypeApp tmp =
		(TypeApp)((TypeApp)T).spineForm(src, false, false,
						true /* expand_defs */);

	    addDef((Const)tmp.head);

	    return tmp;
	}

	if (T.construct == Expr.VAR && dst.isMacroDefined((Var)T)) {
	    /* a little care is needed here, because we do not
	       want to refine a non-specificational to a specificational
	       type variable. */
	    if (src.getFlag("debug_flatten_types")) {
		src.w.println("Handling macro-defined var: "+T.toString(src));
		src.w.flush();
	    }
	    Expr b = T.defExpandTop(dst,false,false);
	    if (src.getFlag("debug_flatten_types")) {
		src.w.println("Expands to: "+b.toString(src));
		src.w.flush();
	    }
	    if (b.construct == Expr.VAR)
		return T;
	    return flattenType(b,do_define);
	}

	if (T.construct != Expr.FUN_TYPE) 
	    return T;
	FunType f = (FunType)T;
	f = (FunType)f.coalesce(dst, false);
	Expr nbody = flattenType(f.body, true);
	Expr[] ntypes = flattenType(f.vars, f.types, true);
	Expr nf = new FunType(f.vars, ntypes, f.owned, f.ret_stat, nbody);
	if (do_define) {
	    Const c = dst.define("funtp", dst.type, nf, nf.dropAnnos(dst));
	    addType(c);
	    return c;
	}
	return nf;
    }

    public Expr[] process(Expr[] X) {
	int iend = X.length;
	Expr[] nX = new Expr[iend];
	for (int i = 0; i < iend; i++)
	    nX[i] = process(X[i]);
	return nX;
    }

    public Expr process(Expr e) {
	if (dbg) {
	    dst.w.println("Processing types in "+e.toString(src));
	    dst.w.flush();
	}

	switch (e.construct) {
	case Expr.FUN_TERM: {
	    FunTerm f = (FunTerm)e;
	    Expr[] ntypes = flattenType(f.vars, f.types, true);
	    Expr nT = flattenType(f.T, true);
	    FunTerm f2 = new FunTerm(f.r, nT, f.vars, ntypes, f.owned, 
				     f.ret_stat, null);
	    f2.setClassifiers(dst);
	    f2.body = process(f.body);
	    f2.pos = e.pos;
	    return f2;
	}
	case Expr.STRING_EXPR:
	    return e;
	case Expr.CONST: 
	case Expr.VAR:
	    if (e.isTypeOrKind(src)) {
		// handle this in the same way as other types below.
		Expr ret = flattenType(e,true);
		ret.pos = e.pos;
		return ret;
	    }
	    return e;
	case Expr.ABORT:
	    return e;
	case Expr.LET: {
	    Let l = (Let)e;
	    Expr nt1 = process(l.t1);
	    Let nl = new Let(l.x1,l.x1_stat,nt1,l.x2,null);
	    if (dbg) {
		src.w.println("Classifying "+nt1.toString(dst));
		src.w.flush();
	    }
	    Expr nT = flattenType(nt1.classify(dst,Expr.APPROX_TRIVIAL,false),
				  true);
	    dst.setClassifier(l.x1,nT);
	    nl.setClassifier2(dst);
	    nl.t2 = process(l.t2);
	    nl.pos = e.pos;
	    return nl;
	}
	case Expr.CAST: {
	    Cast c = (Cast)e;
	    Expr nt = process(c.t);
	    Expr ret = new Cast(nt, c.P, flattenType(c.T,true));
	    ret.pos = e.pos;
	    return ret;
	}
	case Expr.INC: {
	    Inc i = (Inc)e;
	    Expr nt = process(i.t);
	    Expr ret = new Inc(nt, flattenType(i.T,true));
	    ret.pos = e.pos;
	    return ret;
	}
	case Expr.DEC: {
	    Dec d = (Dec)e;
	    Expr nI = process(d.I);
	    Expr nt = process(d.t);
	    Expr ret = new Dec(nI,nt,flattenType(d.T,true));
	    ret.pos = e.pos;
	    return ret;
	}
	case Expr.MATCH: {
	    Match m = (Match)e;
	    Expr nt = process(m.t);
	    Case[] nC = new Case[m.C.length];
	    Expr scruttp = nt.classify(dst,Expr.APPROX_TRIVIAL,false);
	    for (int i = 0, iend = m.C.length; i < iend; i++) {
		Case c = m.C[i];
		if (dbg) {
		    dst.w.println("Processing pattern with head "
				  +c.c.toString(dst)+" : "
				  +dst.getClassifier(c.c).toString(dst));
		    dst.w.flush();
		}
		c.setPatternVarTypes(dst, true); 
		if (dbg && c.x.length > 0 
		    && dst.getFlag("print_pattern_var_types")) {
		    dst.w.println("Flattening types in pattern vars:");
		    c.print_pattern_var_types_if(dst.w,dst);
		    dst.w.println("");
		    dst.w.flush();
		}
		c.refine(dst,scruttp,Expr.APPROX_TRIVIAL,false);
		Expr nbody = process(c.body);
		nC[i] = new Case(c.c,c.x,nbody,c.impossible);
		nC[i].pos = e.pos;
		/* flatten the pattern var types now, since
		   they may have gotten refined into function types */
		for (int j = 0, jend = c.x.length; j < jend; j++) {
		    Expr T = dst.getClassifier(c.x[j]);
		    dst.setClassifier(c.x[j],process(T));
		}
	    }

	    Expr ret = new Match(nt,m.x1,m.x2, null /* we do not bother
						       to flatten the 
						       return type, if there
						       is one*/,
				 nC, m.scrut_stat);
	    ret.pos = e.pos;
	    return ret;
	}
	case Expr.TERM_APP: {
	    TermApp a = (TermApp)e;
	    Expr ret = new TermApp(process(a.head), process(a.X));
	    ret.pos = e.pos;
	    return ret;
	}
	default: {
	    if (e.isTypeOrKind(src)) {
		// We want to introduce a new definition
		// for this if it is a Fun-type, because then if it is
		// substituted for a type variable in the return type
		// of whatever function is being called, we will have a 
		// Const for the name of the type, for the benefit of
		// casting (in the Compiler).
		Expr ret = flattenType(e,true);
		ret.pos = e.pos;
		return ret;
	    }
	    return e;
	}
	}
    }

    // return a list of the defined type constants and the type constructors,
    // in definition order, from the starting context.
    public Collection getTypes() {
	return types;
    }
}
