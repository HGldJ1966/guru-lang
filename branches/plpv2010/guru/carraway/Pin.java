package guru.carraway;

public class Pin extends Expr {

    public Sym s;
    public Sym[] pinned;

    public Pin(){
	super(PIN);
    }

    public Pin(Sym s1, Sym s2){
	super(PIN);
	s = s1;
	pinned = new Sym[1];
	pinned[0] = s2;
    }

    public Expr simpleType(Context ctxt) {
	if (!ctxt.isResourceType(s))
	    classifyError(ctxt,"A pin expression begins with a symbol which is not an attribute.\n\n"
			+"1. The symbol: "+s.toString(ctxt));
	for (int i = 0, iend = pinned.length; i < iend; i++) {
	    Expr T = ctxt.getType(pinned[i]);
	    if (T == null)
		classifyError(ctxt,"Missing a type for a symbol in a pin-type.\n\n"
			    +"1. The symbol: "+pinned[i].toString(ctxt));
	}
	return new Type();
    }

    public boolean eqType(Context ctxt, Expr T) {
	if (ctxt.getFlag("debug_eqType")) {
	    ctxt.w.println("Testing pin-type equality: ");
	    ctxt.w.println("  1. "+toString(ctxt));
	    ctxt.w.println("  2. "+T.toString(ctxt));
	    ctxt.w.flush();
	}

	if (T.construct == ABORT)
	    return true;

	if (T.construct != PIN)
	    return false;

	Pin p = (Pin)T;
	
	if (!s.eqType(ctxt,p.s))
	    return false;

	if (pinned.length != p.pinned.length)
	    return false;

	for (int i = 0, iend = pinned.length; i < iend; i++) 
	    if (!pinned[i].eq(ctxt,p.pinned[i]))
		return false;
	return true;
    }

    public boolean nonBindingOccurrence_h(Context ctxt, Sym x) {
	if (s.nonBindingOccurrence(ctxt,x))
	    return true;
	for (int i = 0, iend = pinned.length; i < iend; i++) 
	    if (pinned[i].nonBindingOccurrence(ctxt,x))
		return true;
	return false;
   }

    public Expr applySubst(Context ctxt) {
	Sym ns = (Sym)s.applySubst(ctxt);
	Sym[] np = new Sym[pinned.length];

	boolean changed = (ns != s);
	for (int i = 0, iend = pinned.length; i < iend; i++) {
	    np[i] = (Sym)pinned[i].applySubst(ctxt);
	    changed = changed || (np[i] != pinned[i]);
	}
	if (changed) {
	    Pin p = new Pin();
	    p.pos = pos;
	    p.s = ns;
	    p.pinned = np;
	    return p;
	}
	
	return this;
    }

    public void do_print(java.io.PrintStream w, Context ctxt) {
	if (ctxt.stage <= 2) {
	    w.print("<");
	    s.print(w,ctxt);
	    for (int i = 0, iend = pinned.length; i < iend; i++) {
		w.print(" ");
		pinned[i].print(w,ctxt);
	    }
	    w.print(">");
	}
	else 
	    s.print(w,ctxt);
    }    

}