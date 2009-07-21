package guru;

import java.io.*;
import java.util.Collection;
import java.util.ArrayList;
import java.util.Iterator;

public class Compile extends Command {
    Const cmain;

    public String filename;
    public File f, root, ifile;

    public Compile() {
	super(COMPILE);
    }

    public Compile(String file) {
	super(COMPILE);
	filename = file;
    }

    protected void printCmd_if(Context ctxt, guru.carraway.Context cctxt, guru.carraway.Command cmd) {
	if (ctxt.getFlag("debug_to_carraway")) {
	    cctxt.stage = 0;
	    cmd.print(ctxt.w, cctxt);
	    ctxt.w.flush();
	}
    }

    protected Collection cmds_for_resource_types(Context ctxt,guru.carraway.Context cctxt) {
	ArrayList cmds = new ArrayList();

	Iterator it = ctxt.getResourceTypes().iterator(); 
	
	if (ctxt.getFlag("debug_to_carraway")) {
	    ctxt.w.println("\nTranslating resource types (");
	    ctxt.w.flush();
	}

	while(it.hasNext()) {
	    Const c = (Const)it.next();

	    if (ctxt.getFlag("debug_to_carraway")) {
		ctxt.w.println("Translating resource type \""+c.toString(ctxt)+"\" (");
		ctxt.w.flush();
	    }

	    guru.carraway.ResourceType R = new guru.carraway.ResourceType();
	    R.pos = c.pos;
	    R.s = cctxt.newSym(c.name,c.pos);
	    cctxt.declareConst(R.s);
	
	    Define drop = ctxt.getDropFuncDef(ctxt.getDropFunc(c));
	    R.drop = drop.toCarraway(ctxt);

	    cmds.add(R);

	    if (ctxt.getFlag("debug_to_carraway")) {
		ctxt.w.println(") done translating resource type \""+c.toString(ctxt)+"\".");
		ctxt.w.flush();
	    }

	}

	if (ctxt.getFlag("debug_to_carraway")) {
	    ctxt.w.println(") done translating resource types.");
	    ctxt.w.flush();
	}

	return cmds;
    }

    protected Collection cmds_for_other_consts(Collection all, Context ctxt,guru.carraway.Context cctxt) {
	ArrayList cmds = new ArrayList();

	if (ctxt.getFlag("debug_to_carraway")) {
	    ctxt.w.println("\nTranslating defined and declared constants (");
	    ctxt.w.flush();
	}

	Iterator it = all.iterator(); 
	while (it.hasNext()) {
	    Const d = (Const)it.next();

	    if (ctxt.isTypeCtor(d)) {
		Collection ctors = ctxt.getTermCtors(d);
		
		if (ctxt.getFlag("debug_to_carraway")) {
		    ctxt.w.println("\nTranslating type constructor \""+d.toString(ctxt)+"\"(");
		    ctxt.w.flush();
		}

		Ownership ret_stat = ctxt.getTypeCtorRetStat(d);

		guru.carraway.Datatype dc = new guru.carraway.Datatype();
		dc.pos = d.pos;
		dc.tp = cctxt.newSym(d.name, d.pos);
		cctxt.declareConst(dc.tp); // for benefit of translation of ctors' types
		int num_ctors = ctors.size();
		dc.ctors = new guru.carraway.Sym[num_ctors];
		dc.types = new guru.carraway.Expr[num_ctors];
		dc.rttypes = new guru.carraway.Expr[num_ctors];
		int j = 0;
		Iterator it2 = ctors.iterator();
		while (it2.hasNext()) {
		    Const c = (Const)it2.next();
		    Expr D = ctxt.getClassifier(c);
		    dc.ctors[j] = cctxt.newSym(c.name,c.pos);
		    cctxt.declareConst(dc.ctors[j]);
		    if (ctxt.getFlag("debug_to_carraway")) {
			ctxt.w.println("Translating term constructor \""+c.toString(ctxt)+"\"(");
			ctxt.w.flush();
		    }

		    // the resource type
		    dc.types[j] = D.toCarrawayType(ctxt,false);
		    if (ret_stat != null && dc.types[j].construct == guru.carraway.Expr.SYM) 			
			dc.types[j] = ret_stat.toCarrawayType(ctxt,c.pos);

		    if (ctxt.getFlag("debug_to_carraway")) {
			ctxt.w.println("Its resource type: "+dc.types[j].toString(cctxt)+".");
			ctxt.w.flush();
		    }

		    if (D.construct == Expr.CONST || D.construct == Expr.TYPE_APP) 
			dc.rttypes[j] = D.toCarrawayType(ctxt,false);
		    else 
			dc.rttypes[j] = D.toCarrawayType(ctxt,true);

		    if (ctxt.getFlag("debug_to_carraway")) {
			ctxt.w.println("Its data type: "+dc.rttypes[j].toString(cctxt)+".");
			ctxt.w.println(") done translating term constructor \""+d.toString(ctxt)+"\".");
			ctxt.w.flush();
		    }
		    j++;
		}
		if (ctxt.getFlag("debug_to_carraway")) {
		    ctxt.w.println(") done translating type constructor \""+d.toString(ctxt)+"\".");
		    ctxt.w.flush();
		}
		cmds.add(dc);
	    }
	    else if (ctxt.isDefined(d)) {
		Const c = d;

		if (ctxt.getFlag("debug_to_carraway")) {
		    ctxt.w.println("\nTranslating defined constant \""+c.toString(ctxt)+"\".");
		    ctxt.w.flush();
		}

		if (ctxt.isDropFunc(c)) {
		    // we include drop functions when we process resource types
		    if (ctxt.getFlag("debug_to_carraway")) {
			ctxt.w.println("skipping, since this is a drop function (already included with resource types).");
			ctxt.w.flush();
		    }
		    continue;
		}
		else if (ctxt.getDefCode(c) != null) {
		    // this is a primitive

		    guru.carraway.Primitive p = new guru.carraway.Primitive();
		    p.pos = c.pos;
		    guru.carraway.Sym cc = cctxt.newSym(c.name,c.pos);

		    if (c.isTypeOrKind(ctxt)) {
			// primitive types are translated as Datatype commands

			if (ctxt.getFlag("debug_to_carraway")) {
			    ctxt.w.println("Defined constant \""+c.toString(ctxt)+"\" is a primitive type.");
			    ctxt.w.flush();
			}

			guru.carraway.Datatype dc = new guru.carraway.Datatype();
			dc.tp = cc;
			cctxt.declareConst(cc);

			// build the delete primitive
			p.s = cctxt.newSym("delete_"+cc.name, c.pos);
			p.T = dc.buildDeleteType(cctxt);
			p.delim = ctxt.getDefDelim(c);
			p.code = ctxt.getDefCode(c);


			dc.del = p;

			cmds.add(dc);
		    }
		    else {
			if (ctxt.getFlag("debug_to_carraway")) {
			    ctxt.w.println("Defined constant \""+c.toString(ctxt)+"\" is a primitive term.");
			    ctxt.w.flush();
			}

			p.s = cc;
			cctxt.declareConst(p.s);
			Ownership o = ctxt.getDefOwnership(c);
			if (o.status != Ownership.DEFAULT)
			    p.T = o.toCarrawayType(ctxt, c.pos);
			else
			    p.T = ctxt.getClassifier(c).toCarrawayType(ctxt, false);
			p.delim = ctxt.getDefDelim(c);
			p.code = ctxt.getDefCode(c);
			cmds.add(p);
		    }
		}
		// not a primitive
		else if (ctxt.isSpec(c)) {
		    if (ctxt.getFlag("debug_to_carraway")) {
			ctxt.w.println("Skipping specificational \""+c.toString(ctxt)+"\".");
			ctxt.w.flush();
		    }
		    continue;
		}
		else if (c.isProof(ctxt)) {
		    if (ctxt.getFlag("debug_to_carraway")) {
			ctxt.w.println("Skipping proof \""+c.toString(ctxt)+"\".");
			ctxt.w.flush();
		    }
		    continue;
		}
		else { 

		    if (ctxt.getFlag("debug_to_carraway")) {
			ctxt.w.println("Defined constant \""+c.toString(ctxt)+"\" is not a primitive.");
			ctxt.w.flush();
		    }
		    
		    Expr body = ctxt.getDefBody(c);

		    if (c.isTypeOrKind(ctxt)) {
			guru.carraway.TypeDef td = new guru.carraway.TypeDef();
			td.pos = c.pos;
			td.c = cctxt.newSym(c.name,c.pos);
			cctxt.declareConst(td.c);
			td.T = body.toCarrawayType(ctxt,true);
			cmds.add(td);
			continue;
		    }
		
		    if (body.construct == Expr.FUN_TERM) {
			FunTerm F = (FunTerm)body;
			guru.carraway.Function g = new guru.carraway.Function();
			g.pos = c.pos;
			if (F.r == null) {
			    F.r = new Var(c.name);
			    F.r.pos = c.pos;
			}
			else 
			    F.r.name = c.name;
			g.t = (guru.carraway.FunTerm)body.toCarraway(ctxt);
			cmds.add(g);
			continue;
		    }

		    // this should be something we can include as a global.

		    guru.carraway.Global g = new guru.carraway.Global();
		    g.pos = c.pos;
		    g.c = cctxt.newSym(c.name,c.pos);
		    cctxt.declareConst(g.c);
		    g.t = body.toCarraway(ctxt);
		    cmds.add(g);
		}
	    }
	}

	if (ctxt.getFlag("debug_to_carraway")) {
	    ctxt.w.println(") done translating declared and defined constants.");
	    ctxt.w.flush();
	}

	return cmds;
    }

    protected void printContext(String msg, Context ctxt) {
	ctxt.w.println("% ---------------------------------");
	ctxt.w.print("% ");
	ctxt.w.println(msg);
	ctxt.w.println("");
	Iterator it = ctxt.getTypeCtors().iterator();
	while(it.hasNext()) {
	    Const c = (Const)it.next();
	    ctxt.w.println("Inductive type: "+c.toString(ctxt));
	}

	it = ctxt.getResourceTypes().iterator();
	while(it.hasNext()) {
	    Const c = (Const)it.next();
	    ctxt.w.println("Resource type: "+c.toString(ctxt));
	}

        it = ctxt.getDefinedConsts().iterator();
	while(it.hasNext()) {
	    Const c = (Const)it.next();
	    
	    Expr body = (ctxt.isOpaque(c) ? c : ctxt.getDefBody(c));
	    
	    Expr T = ctxt.getClassifier(c);
	    
	    Define D = new Define(ctxt.isSpec(c), (ctxt.getDefCode(c) != null), ctxt.isTrusted(c),
				  ctxt.isTypeFamilyAbbrev(c),
				  ctxt.isPredicate(c),
				  false,
				  c, ctxt.getDefOwnership(c), T, body, body.dropAnnos(ctxt),
				  ctxt.getDefDelim(c), ctxt.getDefCode(c));
	    
	    if (ctxt.isDropFunc(c)) 
		ctxt.w.println("% "+c.toString(ctxt)+" is a drop function:");
	    D.print(ctxt.w, ctxt);
	}
	ctxt.w.print("% end of ");
	ctxt.w.println(msg);
	ctxt.w.println("");

	ctxt.w.flush();
    }

    // c should hold Init-Commands.
    protected Collection init_cmds(Collection c, Context ctxt, guru.carraway.Context cctxt) {
	ArrayList cmds = new ArrayList();
	Iterator it = c.iterator();

	if (ctxt.getFlag("debug_to_carraway")) {
	    ctxt.w.println("\nTranslating Init commands (");
	    ctxt.w.flush();
	}

	while (it.hasNext()) {
	    Init I = (Init)it.next();
	    guru.carraway.Init C = new guru.carraway.Init();
	    
	    if (ctxt.getFlag("debug_to_carraway")) {
		ctxt.w.println("Translating Init command \""+I.s.toString(ctxt)+"\" (");
		ctxt.w.flush();
	    }

	    C.pos = I.pos;
	    C.init = new guru.carraway.Primitive();
	    C.init.pos = I.pos;
	    C.init.s = cctxt.newSym(I.s.name, I.s.pos);
	    cctxt.declareConst(C.init.s);
	    C.init.T = new guru.carraway.FunType();
	    guru.carraway.FunType F = new guru.carraway.FunType();
	    C.init.T = F;
	    C.must_consume_scrut = I.must_consume_scrut;
	    C.take_pointer = I.take_pointer;
	    F.pos = I.v1.pos;
	    F.vars = new guru.carraway.Sym[3];
	    F.types = new guru.carraway.Expr[3];
	    F.consumps = new int[3];

	    F.vars[0] = cctxt.newVar(I.v1.pos);
	    F.vars[1] = cctxt.newSym(I.v1.name, I.v1.pos);
	    F.vars[2] = cctxt.newSym(I.v2.name, I.v2.pos);

	    cctxt.pushVar(F.vars[1]);
	    cctxt.pushVar(F.vars[2]);

	    F.types[0] = new guru.carraway.Type();
	    F.types[1] = I.T1.toCarrawayType(ctxt,I.pos);
	    F.types[2] = I.T2.toCarrawayType(ctxt,I.pos);

	    F.consumps[0] = FunAbstraction.CONSUMED_RET_OK;
	    F.consumps[1] = FunAbstraction.NOT_CONSUMED;
	    F.consumps[2] = FunAbstraction.CONSUMED_RET_OK;

	    F.rettype = I.T3.toCarrawayType(ctxt,I.pos);

	    cctxt.popVar(F.vars[1]);
	    cctxt.popVar(F.vars[2]);

	    C.init.delim = I.delim;
	    C.init.code = I.code;

	    if (ctxt.getFlag("debug_to_carraway")) {
		ctxt.w.println(") done translating Init command \""+I.s.toString(ctxt)+"\".");
		ctxt.w.flush();
	    }

	    cmds.add(C);
	}

	if (ctxt.getFlag("debug_to_carraway")) {
	    ctxt.w.println(") done translating Init commands.");
	    ctxt.w.flush();
	}

	return cmds;
    }

    protected Const lookup_const(Context ctxt, String name) {
	Expr e = ctxt.lookup(name);
	if (e == null || e.construct != Expr.CONST)
	    handleError(ctxt, "Guru declaration missing for \""+name+"\", needed for compilation.");
	return (Const)e;
    }
	

    protected void copy_needed_init_cmds(Context src, Context tgt) {
	Iterator it = src.initCmds.iterator();
	
	while (it.hasNext()) {
	    Init I = (Init)it.next();
	    if (src.getFlag("debug_to_carraway")) {
		src.w.println("Adding Init command \""+I.s.toString(src)+"\" to list to translate.");
		src.w.flush();
	    }
	    tgt.initCmds.add(I);
	}
    }

    protected void processCommands(Collection c, Context ctxt, guru.carraway.Context cctxt) {
	Iterator it = c.iterator();
	while(it.hasNext()) {
	    guru.carraway.Command cmd = (guru.carraway.Command)it.next();
	    printCmd_if(ctxt,cctxt,cmd);
	    cmd.process(cctxt);
	}
    }

    public void process(Context ctxt) {
	if (f == null) {
	    File tmp = null;
	    try {
		tmp = (new File(filename)).getCanonicalFile();
		root = tmp.getParentFile();
	    }
	    catch (Exception e) {
		handleError(ctxt,"Cannot open file "+f+".");
	    }
	    f = new File(tmp.getName());
	}

	ifile = (f.isAbsolute() 
		    ? f
		    : (new File(root.getAbsolutePath() + "/" + f.getPath())));
	
	Context trans_ctxt = new Context(); 
	trans_ctxt.copyFlags(ctxt);

	guru.compiler.EtaExpand ee = new guru.compiler.EtaExpand(ctxt,trans_ctxt);
	ee.expand(cmain);

	if (ctxt.getFlag("debug_eta_expand")) 
	    printContext("After eta expansion", trans_ctxt);

	if (ctxt.getFlag("debug_to_carraway")) {
	    ctxt.w.println("Translation to Carraway begins.");
	    ctxt.w.flush();
	}

	copy_needed_init_cmds(ctxt,trans_ctxt);

	guru.carraway.Context cctxt = new guru.carraway.Context(".g");
	trans_ctxt.carraway_ctxt = cctxt;
	cctxt.copyFlags(trans_ctxt);

	if (false && trans_ctxt.getFlag("debug_to_carraway")) {
	    ctxt.w.println("Copied flags (on):");
	    Iterator it2 = cctxt.getFlags().iterator();
	    while (it2.hasNext()) {
		String flag = (String)it2.next();
		ctxt.w.println("  "+flag);
		ctxt.w.flush();
	    }
	}

	if (ctxt.getFlag("debug_to_carraway")) 
	    printContext("Just about to begin translating commands to Carraway.", trans_ctxt);

	Collection resource_decls = cmds_for_resource_types(trans_ctxt, cctxt);

	cctxt.setFile(ifile);

	guru.carraway.Command cmd;

	guru.carraway.Include.start_emit(cctxt);

	cctxt.commentBox("Data types and resource types");
	processCommands(resource_decls, trans_ctxt, cctxt);

	cctxt.stage = 0;
	Collection init_cmds = init_cmds(trans_ctxt.initCmds,trans_ctxt,cctxt);

	cctxt.commentBox("Init functions");
	processCommands(init_cmds, trans_ctxt, cctxt);

	cctxt.stage = 0;
	Collection defs = cmds_for_other_consts(ee.all_consts,trans_ctxt, cctxt);

	cctxt.commentBox("Definitions");
	processCommands(defs, trans_ctxt, cctxt);

	guru.carraway.Include.finish_emit(cctxt);
    }
    
    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	w.println("Compiled " + ifile.getPath() + ".");
    }
}
