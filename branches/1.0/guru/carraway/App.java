package guru.carraway;
import guru.Position;
import java.util.Collection;
import java.util.Iterator;

public class App extends Expr {

    public Sym head;
    public Expr[] args;

    public App(){
	super(APP);
    }

    public App(Sym head, Expr[] args){
	super(APP);
	this.head = head;
	this.args = args;
    }


    public App(Sym head, Expr[] args,Position p){
	super(APP);
	this.head = head;
	this.args = args;
	this.pos = p;
    }

    public App(Sym head, Expr arg, Position p){
	super(APP);
	this.head = head;
	this.args = new Expr[1];
	this.args[0] = arg;
	this.pos = p;
    }

    public App(Sym head, Position p){
	super(APP);
	this.head = head;
	this.args = new Expr[0];
	this.pos = p;
    }

    public void do_print(java.io.PrintStream w, Context ctxt) {
	if (head == ctxt.returnf) {
	    w.print("return ");
	    args[0].print(w,ctxt);
	    w.println(";");
	}
	else if (ctxt.stage >= 2) {
	    head.print(w,ctxt);
	    w.print("(");
	    for (int i = 0, iend = args.length; i < iend; i++) {
		args[i].print(w,ctxt);
		if (i < iend - 1)
		    w.print(", ");
	    }
	    w.print(")");
	}
	else {
	    w.print("(");
	    head.print(w,ctxt);
	    for (int i = 0, iend = args.length; i < iend; i++) {
		w.print(" ");
		args[i].print(w,ctxt);
	    }
	    w.print(")");
	}
    }    

    public Expr simpleType(Context ctxt) {
	Expr hT = ctxt.getType(head);
	if (hT == null)
	    classifyError(ctxt,"The head of an application is missing a type.\n\n"
			+"1. the head: "+head.toString(ctxt));
	FunType F = (FunType)hT;
	if (F.vars.length != args.length)
	    classifyError(ctxt,"The head of an application does not accept as many arguments as given.\n\n"
			    +"1. the head: "+head.toString(ctxt)
			    +"\n2. its type: "+ctxt.getType(head).toString(ctxt)
			    +"\n3. the number of arguments: "+(new Integer(args.length)).toString());
	for (int i = 0, iend = args.length; i < iend; i++) {
	    Expr T = args[i].simpleType(ctxt);
	    if ((F.consumps[i] == FunBase.CONSUMED_NO_RET ||
		 F.consumps[i] == FunBase.NOT_CONSUMED) && T.construct == PIN && F.types[i].construct == SYM)
		T = ((Pin)T).s;
	    Expr hdT = T;
	    if (!F.types[i].eqType(ctxt,hdT))
		classifyError(ctxt,"The type computed for an argument does not match the expected type.\n\n"
			    +"1. the argument: "+args[i].toString(ctxt)
			    +"\n2. its type: "+T.toString(ctxt)
			    +"\n2. the expected type: "+F.types[i].toString(ctxt));
	    if (F.nonBindingOccurrence(ctxt, F.vars[i])) {
		// dependent type here
		if (args[i].construct != SYM || (!ctxt.isVar((Sym)args[i]) && !ctxt.isGlobal((Sym)args[i])))
		    classifyError(ctxt,"The type for an application will depend on an argument which is not a variable or global.\n\n"
				  +"1. the argument (which is argument "+(new Integer(i+1)).toString()+"): "+args[i].toString(ctxt)
				  +"\n\n2. the type of the head: "+F.applySubst(ctxt).toString(ctxt)
				  +"\n\n3. the variable with a non-binding occurrence in the type: "+F.vars[i].toString(ctxt));
		
		ctxt.setSubst(F.vars[i],(Sym)args[i]);
	    }
	}

	return F.rettype.applySubst(ctxt);
    }

    public Sym simulate_h(Context ctxt, Position p) {
	FunType f = (FunType) ctxt.getType(head);

	if (ctxt.getFlag("debug_refs")) {
	    ctxt.w.println("(Simulating an application: "+toString(ctxt));
	    ctxt.w.flush();
	}

	Sym[] rs = new Sym[args.length];
	for (int i = 0, iend = args.length; i < iend; i++) {
	    rs[i] = args[i].simulate(ctxt,pos);

	    if (rs[i] == null) {
		// an argument aborts
		if (ctxt.getFlag("debug_refs")) {
		    ctxt.w.println(") aborting");
		    ctxt.w.flush();
		}

		return null;
	    }
	}

	Collection[] rs_pinnedby = new Collection[args.length];
	Sym[] prev = new Sym[args.length];
	for (int i = 0, iend = args.length; i < iend; i++) {
	    if ((f.consumps[i] == FunBase.CONSUMED_RET_OK || f.consumps[i] == FunBase.CONSUMED_NO_RET) 
		&& f.types[i].consumable()) {
		// this is a reference we are supposed to consume
		Context.RefStat u = ctxt.refStatus(rs[i]);
		if (!u.consume)
		    simulateError(ctxt,"A reference that is marked not to be consumed is being consumed.\n\n"
				  +"1. the reference was created at: "+rs[i].posToString()
				  +"\n\n2. the consuming function: "+head.toString(ctxt));
		if (u.non_ret && f.consumps[i] == FunBase.CONSUMED_RET_OK)
		    simulateError(ctxt,"A reference that is marked not to be returned is being passed to a function that\n"
				  +"might return it.\n\n"
				  +"1. the reference: "+rs[i].refString(ctxt)
				  +"\n\n2. the consuming function: "+head.toString(ctxt));

		Position pp = ctxt.wasDropped(rs[i]);
		if (pp != null) 
		    simulateError(ctxt,"A reference that was already consumed is being consumed again.\n\n"
				  +"1. the reference created at: "+rs[i].posToString()
				  +"\n\n2. first consumed at: "+pp.toString());
		rs_pinnedby[i] = ctxt.dropRef(rs[i], pos);
	    }
	    prev[i] = ctxt.getSubst(f.vars[i]);
	    ctxt.setSubst(f.vars[i],rs[i]);
	}
	
	for (int i = 0, iend = args.length; i < iend; i++) 
	    if (rs_pinnedby[i] != null && rs_pinnedby[i].size() > 0) {
		Iterator it = rs_pinnedby[i].iterator();
		simulateError(ctxt,"A pinned reference is being consumed.\n\n"
			      +"1. the reference created at: "+rs[i].posToString()
			      +"\n\n2. pinned by the reference created at: "+((Sym)it.next()).posToString());
	    }

	Expr rettype = f.rettype.applySubst(ctxt);

	for (int i = 0, iend = args.length; i < iend; i++)
	    ctxt.setSubst(f.vars[i],prev[i]);

	if (rettype.construct == VOID ||
	    rettype.construct == TYPE ||
	    rettype.construct == UNTRACKED)
	    return ctxt.voidref;

	Sym ret = ctxt.newRef(pos);
	if (rettype.construct == PIN) {
	    // we need to make sure this does not depend on any consumed references

	    Pin pi = (Pin)rettype;

	    for (int i = 0, iend = pi.pinned.length; i < iend; i++) {
		Position pp = ctxt.wasDropped(pi.pinned[i]);
		if (pp != null)
		    simulateError(ctxt,"The return type of a function depends on a consumed reference.\n\n"
				  +"1. the function: "+head.toString(ctxt)
				  +"\n\n2. its type: "+f.toString(ctxt)
				  +"\n\n3. the consumed reference was created at: "+pi.pinned[i].posToString()
				  +"\n\n4. it was consumed at: "+pp.toString());
	    }

	    ctxt.pin(ret,pi.pinned);
	}

	if (ctxt.getFlag("debug_refs")) {
	    ctxt.w.println(") returning" + ret.refString(ctxt));
	    ctxt.w.flush();
	}
	return ret;
    }

    public Expr linearize(Context ctxt, Position p, Sym dest, Collection decls, Collection defs) {
	int iend = args.length;
	Expr[] nargs = new Expr[iend];
	for (int i = 0; i < iend; i++) 
	    nargs[i] = args[i].linearize(ctxt,p,null,decls,defs);
	
	return linearize_return(ctxt, new App(head,nargs,pos), p, dest);
    }
}