package guru;

public class Ownership {
    public int status;
    public Expr e; // null except for OWNEDBY and UNIQUE_OWNEDBY
    public Ownership(int status) {
	this.status = status;
	this.e = null;
    }
    public Ownership(int status, Expr e) {
	this.status = status;//could be OWNEDBY or UNIQUE_OWNEDBY
	this.e = e;
    }

    /* UNIQUE means unowned and cannot be incremented. */
    public static final int UNOWNED = 0;
    public static final int OWNEDBY = 1;
    public static final int UNIQUE = 2; 
    public static final int NOT_TRACKED = 3; /* for functions and elts. of 
						flat types */
    public static final int UNIQUE_OWNEDBY = 4; 
    public static final int NEW = 5; /* for constructor terms.  New things
					can become UNIQUE or UNOWNED. */
    public static final int KILLED = 6; /* introduced by compiler/CheckRefs. */

    public static final int SPEC = 7; //for specificational data


    public String toString(Context ctxt) {
	switch (status) {
	case OWNEDBY:
	    if (e == null)
		return "owned";
	    else
		return "owned_by "+e.toString(ctxt);
	case UNIQUE_OWNEDBY:
	    if (e == null)
		return "unique_owned";
	    else
		return "unique_owned_by "+e.toString(ctxt);
	case UNOWNED:
	    return "unowned";
	case UNIQUE:
	    return "unique";
	case NOT_TRACKED:
	    return "untracked";
	case NEW:
	    return "new";
	case KILLED:
	    return "killed";
	case SPEC:
	    return "spec";
	default:
	    return "unrecognized status ("
		+(new Integer(status)).toString()+")";
	}
    }


    // return true iff this is coercible to owned2.
    public boolean subStatus(Ownership owned2) {
	if (status == owned2.status)
	    return true;

	if ((status == UNOWNED || status == NEW) && 
	    owned2.status == OWNEDBY)
	    // unowned/new things can be coerced to owned.
	    return true;

	if (status == NEW && 
	    (owned2.status == UNIQUE || owned2.status == UNOWNED 
	     || owned2.status == UNIQUE_OWNEDBY))
	    return true;

	if (status == UNIQUE && owned2.status == UNIQUE_OWNEDBY)
	    return true;
	
	if (status == NOT_TRACKED && 
	    (owned2.status == OWNEDBY || owned2.status == UNOWNED))
	    return true;

	if ((status == OWNEDBY || status == UNOWNED) && 
	    (owned2.status == NOT_TRACKED))
	    return true;

	return false;
    }

    boolean shouldPrint(Context ctxt) {
	return ((status != UNOWNED && status != NOT_TRACKED)
		|| ctxt.getFlag("print_ownership_annos"));
    }



}