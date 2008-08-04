package guru;

// a parent class for Inc and Dec
public abstract class IncDec extends Expr{
    
    public IncDec(int construct) {
	super(construct);
    }
    
    // make sure T is a suitable type for a reference to be inc'ed or dec'ed.
    protected void checkType(Context ctxt, Expr T) {
	if (!isTrackedType(ctxt))
	    handleError(ctxt,"An inc- or dec-term is being used with a "
			+"type of term\nthat is not tracked.\n"
			+"1. the inc/dec term: "+toString(ctxt)
			+"\n2. the subterm's type: " + T.toString(ctxt));
    }
}