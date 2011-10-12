package guru;

import java.util.ArrayList;

public class UnjoinOr extends UnjoinDeduction {

	public final UnjoinDeduction d0;
	public final UnjoinDeduction d1;
	
	public UnjoinOr(UnjoinDeduction d0, UnjoinDeduction d1) {
		assert(d0 != null);
		assert(d1 != null);
		
		this.d0 = d0;
		this.d1 = d1;
	}

	public UnjoinDeduction Or(UnjoinDeduction deduction) {
		if (deduction == contradiction)
			return this;
		
		return new UnjoinOr(deduction, this);
	}
	
	public int GetDeductionType()
	{
		return OR;
	}
}
