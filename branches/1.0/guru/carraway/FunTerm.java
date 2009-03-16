package guru.carraway;

public class FunTerm extends FunBase {
    public Sym f;
    public Expr body;

    public FunTerm(){
	super(FUN_TERM);
    }

    public void print(java.io.PrintStream w, Context ctxt) {
	f.print(w,ctxt);
	super.print(w,ctxt);
	w.println(" :=");
	w.print("  ");
	body.print(w,ctxt);
    }    

    public Expr simpleType(Context ctxt) {
	checkTypes(ctxt);

	FunType F = new FunType();
	F.vars = vars;
	F.types = types;
	F.specs = specs;
	F.consumes = consumes;
	F.rettype = rettype;

	ctxt.setType(f,F);

	Expr bT = body.simpleType(ctxt);
	if (!bT.eqType(ctxt, rettype))
	    classifyError(ctxt,"The expected and computed return types of a function do not match.\n\n"
			  +"1. the expected return type: "+rettype.toString(ctxt)
			  +"\n\n2. the computed return type: "+bT.toString(ctxt));

	return F;
    }
}