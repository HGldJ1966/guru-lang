package guru.carraway;
import guru.Position;
import java.util.Collection;
import java.util.Iterator;
import java.util.HashSet;

public class Compress extends Expr {

    public Expr t;
    public Sym p1; // filled in by simpleType()
    public Sym p2;

    public Compress(){
	super(COMPRESS);
    }

    public Compress(Expr t, Position p){
	super(COMPRESS);
	this.t = t;
	this.pos = p;
    }

    public Expr simpleType(Context ctxt) {
	Expr T = t.simpleType(ctxt); 
	if (T.construct != PIN)
	    classifyError(ctxt, "The subterm of a compress-term has a type which is not a pin-type.\n\n"
			  +"1. the subterm: "+t.toString(ctxt)
			  +"\n\n2. its type: "+T.toString(ctxt));
	Pin P = (Pin)T;
	if (P.pinned.length != 1)
	    classifyError(ctxt, "The subterm of a compress-term does not pin exactly one other reference.\n\n"
			  +"1. the subterm: "+t.toString(ctxt)
			  +"\n\n2. its type: "+T.toString(ctxt));
	p1 = P.pinned[0];

	Expr T2 = ctxt.getType(p1);

	if (T2.construct != PIN)
	    classifyError(ctxt, "The subterm of a compress-term does not pin another pinning reference.\n\n"
			  +"1. the subterm: "+t.toString(ctxt)
			  +"\n\n2. its type: "+T.toString(ctxt)
			  +"\n\n3. the type of the above pinned reference: "+T2.toString(ctxt));
	Pin P2 = (Pin)T2;
	if (P2.pinned.length != 1)
	    classifyError(ctxt, "The subterm of a compress-term does not pin another reference pinning exactly one other reference.\n\n"
			  +"1. the subterm: "+t.toString(ctxt)
			  +"\n\n2. its type: "+T.toString(ctxt)
			  +"\n\n3. the type of the above pinned reference: "+T2.toString(ctxt));

	p2 = P2.pinned[0];
	    
	return T2;
    }

    public void do_print(java.io.PrintStream w, Context ctxt) {
	if (ctxt.stage <= 2) {
	    w.print("@ ");
	    if (p2 != null) {
		p2.print(w,ctxt);
		w.print(" <-- ");
		p1.print(w,ctxt);
		w.print(" <-- ");
	    }
	}
	t.print(w,ctxt);
    }    

    public Sym simulate_h(Context ctxt, Position p) {
	Sym r = t.simulate(ctxt,pos);
	if (r == null)
	    return null;
	Context.RefStat u = ctxt.refStatus(r);
	Iterator it = u.pinning.iterator();
	Sym p1a = null;
	Sym r1 = p1.simulate(ctxt,pos);
	if (u.pinning.size() != 1 || !it.hasNext() || ((p1a = (Sym)it.next()) != r1))
	    simulateError(ctxt,"Simulation of a compress-term does not match what we expected from type checking.\n\n"
			  +"1. the starting reference: "+r.refString(ctxt)
			  +"\n\n2. "+(p1a == null ? "does not pin any reference" 
				      : ("pins "+p1a.refString(ctxt)
					 +(u.pinning.size() != 1 ? "\n\n3. and other references"
					   : "\n\n3. which is different from the expected: "+r1.refString(ctxt)))));
	Context.RefStat v1 = ctxt.refStatus(r1);	    
	v1.pinnedby.remove(r);
	u.pinning.remove(r1);

	it = v1.pinning.iterator();
	Sym p2a = null;
	Sym r2 = p2.simulate(ctxt,pos);
	if (v1.pinning.size() != 1 || !it.hasNext() || ((p2a = (Sym)it.next()) != r2))
	    simulateError(ctxt,"Simulation of a compress-term does not match what we expected from type checking.\n\n"
			  +"1. the starting reference: "+r.refString(ctxt)
			  +"\n\n2. "+(p2a == null ? "does not pin any reference" 
				      : ("pins "+p2a.refString(ctxt)
					 +(v1.pinning.size() != 1 ? "\n\n3. and other references"
					   : "\n\n3. which is different from the expected: "+r2.refString(ctxt)))));

	Context.RefStat v2 = ctxt.refStatus(r2);
	v2.pinnedby.add(r);

	u.pinning.add(r2);
	return r;
    }

    public Expr linearize(Context ctxt, Position p, Sym dest, Collection decls, Collection defs) {
	return t.linearize(ctxt,pos,dest,decls,defs);
    }

}