package guru.carraway;
import guru.Position;
import java.util.Collection;

public class Cast extends Expr {

    public Expr T,t;

    public Cast(){
	super(CAST);
    }

    public Cast(Expr T, Expr t){
	super(CAST);
	this.T = T;
	this.t = t;
    }

    public Cast(Expr T, Expr t, Position p){
	super(CAST);
	this.T = T;
	this.t = t;
	this.pos = p;
    }

    public Expr simpleType(Context ctxt) {
	t.simpleType(ctxt); // just type check these
	if (T.construct != FUN_TYPE)
	    classifyError(ctxt, "A cast is being used to cast to an expression which is not a Fun-type.\n\n"
			  +"1. the expression: "+T.toString(ctxt));
	Expr k = T.simpleType(ctxt);
	if (!k.eqType(ctxt, new Type()))
	    classifyError(ctxt, "A cast is being used to cast to an expression which is not a type.\n\n"
			  +"1. the expression: "+T.toString(ctxt)
			  +"\n2. its type: "+k.toString(ctxt));
	if (T.construct != SYM || !ctxt.isAttribute((Sym)T))
	    classifyError(ctxt, "A cast is being used to cast to an attribute.\n\n"
			  +"1. the attribute: "+T.toString(ctxt));

	return T;
    }

    public void do_print(java.io.PrintStream w, Context ctxt) {
	if (ctxt.stage <= 2) {
	    w.print("cast ");
	    T.print(w,ctxt);
	    w.print(" ");
	    t.print(w,ctxt);
	}
	else {
	    w.print("((");
	    T.print(w,ctxt);
	    w.print(" )");
	    t.print(w,ctxt);
	    w.print(")");
	}
    }    

    public Sym simulate_h(Context ctxt, Position p) {
	return t.simulate(ctxt,pos);
    }

    public Expr linearize(Context ctxt, Position p, Sym dest, Collection decls, Collection defs) {
	Expr nt = t.linearize(ctxt,pos,null,decls,defs);
	return linearize_return(ctxt, new Cast(T,nt,pos), pos, dest);
    }

}