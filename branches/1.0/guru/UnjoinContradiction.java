package guru;

import java.util.ArrayList;

public class UnjoinContradiction extends UnjoinDeduction {

	public static int count = 0;
	
	public UnjoinContradiction()
	{
		count++;
		assert(count <= 1);
	}
	
	public int GetDeductionType()
	{
		return CONTRADICTION;
	}

}
