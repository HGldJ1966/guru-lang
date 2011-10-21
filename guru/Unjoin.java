package guru;

import java.io.PrintStream;
import java.util.*;

public class Unjoin extends Expr {

	// An expression which proves the scrutinee atom.
	public final Expr scrutineeProof;
	
	// An equation of the form t = v or a disequation of the form t != v,
	// where t is a terminating term and v is a value.
	public Atom scrutinee;
	
	// A list containing forall proofs which quantify over the
	// deductions made in each unjoin path.
	private final Vector paths;
	
	public Unjoin(Expr scrutineeProof, Vector paths)
	{
		super(UNJOIN);
		
		this.scrutineeProof = scrutineeProof;
		this.paths = paths;
	}
	
	// Expr override
	protected void do_print(PrintStream w, Context ctxt) {
		// TODO Auto-generated method stub

	}
	
//	private boolean covers(VarListExpr parsedPath, Vector unjoinedPath)
//	{
//		int parsedPathInd = 0;
//		
//		while(parsedPathInd < parsedPath.vars.length)
//		{
//			
//		}
//	}
	
	public Expr classify(Context ctxt) {
		Expr cScrutProof = scrutineeProof.classify(ctxt);
		
		if (cScrutProof.construct != ATOM) {
			handleError(ctxt,
					"Attempted to unjoin an expression not classified as an equation" +
					" or disequation.\n" + 
					"1. classifier of expression: " + cScrutProof.toString(ctxt)
			);
			
			System.exit(0);
		}
		
		scrutinee = (Atom)cScrutProof;
		
		if (!scrutinee.Y2.isI(ctxt))
		{
			handleError(ctxt,
					"Right hand side of unjoin scrutinee classifier is not" +
					"a value.\n" + 
					"1. scrutinee classifier: " + cScrutProof.toString(ctxt)
			);
			
			System.exit(0);
		}
		
		UnjoinDeduction deduction = scrutinee.Y1.Unjoin(
			scrutinee.Y2, 
			new UnjoinContext(ctxt),
			ctxt,
			scrutinee.equality
		);
		
		
		List unjoinPaths = UnjoinDeduction.Flatten(deduction, ctxt);
		
		Iterator it = unjoinPaths.iterator();
		while(it.hasNext())
		{
			if (((Stack)it.next()).size() == 0)
				it.remove();
		}
		
		if (unjoinPaths.size() != paths.size())
		{
			//TODO: spit out error message, remove assert
			DumpUnjoinPaths(unjoinPaths, ctxt);
			handleError(ctxt, "blaaarg!");
			assert(false);
			System.exit(0);
		}
		
//		Expr [] pathClassifiers = new Expr[paths.size()];
//		
//		for (int i = 0; i < paths.size(); ++i)
//		{
//			Foralli parsedPath = (Foralli)paths.get(i);
//			
//			Iterator it = unjoinPaths.iterator();
//			while (it.hasNext()) 
//			{
//				Stack unjoinedPath = (Stack)it.next();
//				
//				// If the parsed path is a subsequence of the
//				// unjoined path, we consider the parsed path adequate 
//				// and remove the unjoined path.
//				
//				
//				
//			}
//		}
		
		Expr [] pathClassifiers = new Expr[paths.size()];
		for (int i = 0; i < paths.size(); ++i)
		{
			Foralli parsedPath = (Foralli)paths.get(i);
			Stack unjoinedPath = (Stack)unjoinPaths.get(i);
			
			//convert unjoined path into a exists
			Var[] unjoinVars = new Var[unjoinedPath.size()-1];
			Expr[] unjoinTypes = new Expr[unjoinedPath.size()-1];
			for(int j = 0; j < unjoinedPath.size()-1; ++j)
			{
				unjoinVars[j] = ((UnjoinIntro)unjoinedPath.get(j)).introVar;
				unjoinTypes[j] = ((UnjoinIntro)unjoinedPath.get(j)).introVarType;
			}
			
			Expr body = ((UnjoinIntro)unjoinedPath.lastElement()).introVarType;
			assert(body.isFormula(ctxt));
			Exists unjoinedExists = new Exists(unjoinVars,unjoinTypes,body);
			Var existsVar = new Var("path " + Integer.toString(i));
			ctxt.setClassifier(existsVar, unjoinedExists);
			
			//TODO: Might be able to compare the paths here to get
			//better error message
			
			Existse eliminator = new Existse(existsVar, parsedPath);
			eliminator.pos = parsedPath.pos;
			pathClassifiers[i] = eliminator.classify(ctxt);
		}
		
		for(int i = 1; i < pathClassifiers.length; ++i)
		{
			if (!pathClassifiers[i].defEq(ctxt, pathClassifiers[0]))
			{
				handleError(ctxt, "unjoin path classifiers do not match");
				System.exit(0);
			}
		}
		
		return pathClassifiers[0];
	}
	
    public void checkTermination(Context ctxt, Expr IH, int arg, Var[] vars) { 
    	for (int i = 0; i < paths.size(); ++i)
    		((Foralli)paths.get(i)).checkTermination(ctxt,IH,arg,vars);
	}
	
	private void DumpUnjoinPaths(List unjoinPaths, Context ctxt)
	{
		for(int i = 0; i < unjoinPaths.size(); ++i)
		{
			String pathString = "";
			Stack path = (Stack)unjoinPaths.get(i);
			for(int j = 0; j < path.size(); ++j)
			{
				UnjoinIntro u = (UnjoinIntro)path.get(j);
				
				pathString += "(" + u.introVar.toString(ctxt) + " : " + 
					u.introVarType.toString(ctxt) + ")";
			}
			
			System.out.println(pathString);
		}
	}
	
	// Expr override
	public int numOcc(Expr e) {
		// TODO Auto-generated method stub
		return 0;
	}

	// Expr override
	public Expr subst(Expr e, Expr x) {
		// TODO Auto-generated method stub
		return null;
	}

	// Expr override
	public Expr dropAnnos(Context ctxt) {
		// TODO Auto-generated method stub
		return null;
	}

}
