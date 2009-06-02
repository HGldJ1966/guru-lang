package guru;
import java.util.ArrayList;
import java.util.HashMap;

public class Cutoff extends Expr
{
    public Expr t;
    public Expr nat_t;
    public boolean spec;
    private Expr nat_t_T;
    private Var new_fun_name;
    
    public Cutoff()
    {
	super(CUTOFF);
    }
    
    public Cutoff(Expr t)
    {
	super(CUTOFF);
	this.t = t;
    }
    
    private Expr create_nat_t(Context ctxt, boolean spec)
    {
	//System.out.println("In create_nat_t.");
	Expr et = t.defExpandTop(ctxt, false /* do not drop annotations */,
				 spec);
	if (nat_t == null || (this.spec && !spec)) {
	    this.spec = spec;
	    if (et.construct != FUN_TERM) {
		handleError(ctxt, "Cutoff of non-function terms not allowed");
	    }
	    FunTerm ft = (FunTerm)et;
	    //System.out.println(" - Actually creating.");
	    Var nat_name = new Var("CutoffNat");
	    Var nat_minus_one_name = new Var("CutoffNatMinusOne");
	    Expr ftbody = (Expr)ft.body;
	    Expr temp_t;
	    if (ft.r == null) {
		if (ft.T == null) {
		    handleError(ctxt, "A cutoff of an anonymous function requires the function to be appropriately typed");
		}
		temp_t = ftbody;
	    } else {
		Var old_fun_name = ft.r;
		new_fun_name = new Var("Cutoff_of_" + ft.r.name);
		TermApp temp_app = new TermApp(new_fun_name, nat_minus_one_name);
		temp_t = ftbody.subst(temp_app, old_fun_name);
	    }

	    Expr old_fun_type = ft.T;
	    assert(old_fun_type != null);
	    assert(old_fun_type.construct == FUN_TYPE);
	    Case[] cases = new Case[2];
	    Var[] case_vars = new Var[0];
	    cases[0] = new Case((Const)ctxt.lookup("Z"), case_vars, new Abort(old_fun_type),
				false);
	    case_vars = new Var[1];
	    case_vars[0] = nat_minus_one_name;
	    cases[1] = new Case((Const)ctxt.lookup("S"), case_vars, temp_t, false);
	    Match match_t = new Match(nat_name, new Var("CutoffNatX1"), new Var("CutoffNatX2"), old_fun_type, cases, false);
	    
	    Var [] new_fun_vars = new Var[ft.vars.length + 1];
	    Expr [] new_fun_types = new Expr[ft.types.length + 1];
	    Ownership[] new_owned = new Ownership[ft.types.length+1];
	    int[] new_consumps = new int[ft.types.length+1];
	    new_fun_vars[0] = nat_name;
	    for (int i = 0; i < ft.vars.length; i++)
		new_fun_vars[i+1] = ft.vars[i];
	    
	    new_fun_types[0] = ctxt.lookup("nat");
	    for (int i = 0; i < ft.types.length; i++)
		new_fun_types[i+1] = ft.types[i];
	    
	    // ownership annotations should not matter here

	    new_owned[0] = new Ownership(Ownership.DEFAULT);
	    for (int i = 0; i < ft.types.length; i++)
		new_owned[i+1] = ft.owned[i];
	    
	    new_consumps[0] = FunAbstraction.CONSUMED_RET_OK; 
	    for (int i = 0; i < ft.types.length; i++)
		new_consumps[i+1] = ft.consumps[i];
	    
	    nat_t_T = new FunType(new_fun_vars, new_fun_types, new_owned, new_consumps, ft.ret_stat, ft.T);
	    nat_t = new FunTerm(new_fun_name, old_fun_type, new_fun_vars, new_fun_types, new_owned, new_consumps,
				ft.ret_stat, match_t);
	}
	//((FunTerm)nat_t).do_print(System.out, ctxt); System.out.println();
	return nat_t;
    }
    
    public void do_print(java.io.PrintStream w, Context ctxt)
    {
	w.print("cutoff ");
	t.print(w,ctxt);
    }
    
    public int numOcc(Expr e)
    {
	//System.out.println("In numOcc.");
	return t.numOcc(e);
    }
    
    public Expr subst(Expr e, Expr x)
    {
	//System.out.println("In subst.");
	Expr nt = t.subst(e,x);
	if (nt != t)
	    return new Cutoff(nt);
	return this;
    }

    public Expr get_nat_t(Context ctxt, boolean spec)
    {
	create_nat_t(ctxt, spec);
	ctxt.setClassifier(new_fun_name, nat_t_T);
	return nat_t;
    }

    public Expr classify(Context ctxt, int approx, boolean spec)
    {
	//System.out.println("In classify.");
	create_nat_t(ctxt, spec);
	ctxt.setClassifier(new_fun_name, nat_t_T);
	return nat_t.classify(ctxt);
    }
    
    public boolean defEqNoAnno(Context ctxt, Expr ee, boolean spec)
    {
	//System.out.println("In defEqNoAnno.");
	create_nat_t(ctxt, spec);
	ctxt.setClassifier(new_fun_name, nat_t_T);
	return nat_t.defEqNoAnno(ctxt, ee,spec);
    }
    
    public Expr dropAnnos(Context ctxt)
    {
	create_nat_t(ctxt, true);
	ctxt.setClassifier(new_fun_name, nat_t_T); // following line fails without this
	return nat_t.dropAnnos(ctxt);
    }
    
    public java.util.Set getDependences() {
	return t.getDependences(); // no idea if this is right
    }
    
    public Expr stepEval(Context ctxt) {
	// make sure we put the cutoff back in, in case someone is joining
	return create_nat_t(ctxt, true);
    }

    public void checkSpec(Context ctxt, boolean in_type){
	create_nat_t(ctxt, false);
	ctxt.setClassifier(new_fun_name, nat_t_T);
	nat_t.checkSpec(ctxt, in_type);
	return;
    }
}
