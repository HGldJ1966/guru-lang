package guru.carraway;

public class Cast extends Expr {

    public Expr T,t;

    public Cast(){
	super(CAST);
    }

    public Expr simpleType(Context ctxt) {
	t.simpleType(ctxt); // just type check these
	Expr k = T.simpleType(ctxt);
	if (!k.eqType(ctxt, new Type()))
	    classifyError(ctxt, "A cast is being used with an expression which is not a type.\n\n"
			  +"1. the expression: "+T.toString(ctxt)
			  +"\n2. its type: "+k.toString(ctxt));
	return T;
    }

    public void print(java.io.PrintStream w, Context ctxt) {
	w.print("cast ");
	T.print(w,ctxt);
	w.print(" ");
	t.print(w,ctxt);
    }    

    public Sym simulate(Context ctxt) {
	return t.simulate(ctxt);
    }
}