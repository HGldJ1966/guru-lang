package guru.carraway;
import guru.Position;

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

    public Expr simpleType(Context ctxt) {
	t.simpleType(ctxt); // just type check these
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

    public void print(java.io.PrintStream w, Context ctxt) {
	w.print("cast ");
	T.print(w,ctxt);
	w.print(" ");
	t.print(w,ctxt);
    }    

    public Sym simulate(Context ctxt, Position p) {
	return t.simulate(ctxt,pos);
    }

}