package guru;

import java.util.*;
import java.io.*;


public class Bang extends Expr{
    public Bang() { 
	super(BANG);
    }
    public void do_print(java.io.PrintStream w, Context ctxt) {
	w.print("!");
    }

    public Expr do_rewrite(Context ctxt, Expr e, Expr x, Stack boundVars)
    {
	return this;
    }

    public int numOcc(Expr e) {
	return (e.construct == BANG) ? 1 : 0;
    }
    public Expr subst(Expr e, Expr x) {
	return this;
    }
    
    public Expr classify(Context ctxt, int approx, boolean spec) {
	handleError(ctxt,
		    "The expression \"!\" is not classifiable.");
	return null;
    }

    public boolean defEqNoAnno(Context ctxt, Expr e, boolean spec) {
	return (e.defExpandTop(ctxt).construct == Expr.BANG);
    }

    public Expr dropAnnos(Context ctxt) {
	return this;
    }

    public boolean isAnnotation(Context ctxt){
	return true;
    }
    
    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars)
    { }
    
    public void getFreeVarsComputational(Context ctxt, Collection vars){
    }
}
