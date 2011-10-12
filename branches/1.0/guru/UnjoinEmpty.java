package guru;

public class UnjoinEmpty extends UnjoinDeduction {
	
	private static int count = 0;
	
	public UnjoinEmpty() {
		count++;
		assert(count <= 1);
	}
	
	public int GetDeductionType()
	{
		return EMPTY;
	}
}
