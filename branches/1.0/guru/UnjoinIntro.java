package guru;

import java.util.ArrayList;

public class UnjoinIntro extends UnjoinDeduction {

	public final Var introVar;
	public final Expr introVarType;
	public final UnjoinDeduction rest;
	
	public UnjoinIntro(Var introVar, Expr introVarType, UnjoinDeduction rest) {
		assert(introVar != null);
		assert(introVarType != null);
		assert(rest != null);
		
		this.introVar = introVar; 
		this.introVarType = introVarType;
		this.rest = rest;
	}
	
	public int GetDeductionType()
	{
		return INTRO;
	}
}
