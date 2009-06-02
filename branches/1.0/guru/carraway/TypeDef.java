package guru.carraway;
import java.util.Collection;
import java.util.Iterator;

public class TypeDef extends Command {
    public Sym c;
    public Expr T;

    public TypeDef() {
	super(TYPEDEF);
    }

    public void process(Context ctxt) {

	// stage 0

	ctxt.stage = 0;
	ctxt.commentBox(c.toString(ctxt));
	T.comment_expr(c,ctxt);

	ctxt.addTypeDef(c,T);

	// stage 3
 
	ctxt.stage = 3;

	if (!ctxt.getFlag("output_ocaml")) {
	    if (T.construct == Expr.FUN_TYPE) {
		FunType F = (FunType)T;
		ctxt.cw.print("typedef ");
		F.rettype.print(ctxt.cw,ctxt);
		ctxt.cw.print("(* ");
		c.print(ctxt.cw,ctxt);
		ctxt.cw.print(")");
		F.print(ctxt.cw,ctxt);
		ctxt.cw.println(";\n");
	    }
	    else {
		ctxt.cw.print("#define ");
		c.print(ctxt.cw,ctxt);
		ctxt.cw.print(" ");
		T.print(ctxt.cw,ctxt);
		ctxt.cw.println("\n");
	    }
	}
	ctxt.cw.flush();
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {
	w.print("TypeDef ");
	c.print(w,ctxt);
	w.print(" := ");
	T.print(w,ctxt);
	w.println(".");
    }
}
