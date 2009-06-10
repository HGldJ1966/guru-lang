package guru;

public class Ownership {
    public int status;
    public Const e1;
    public Var e2; // null except for PINNED
    public Ownership(int status) {
	this.status = status;
	this.e1 = null;
	this.e2 = null;
    }
    public Ownership(int status, Const c) {
	this.status = status;
	this.e1 = c;
	this.e2 = null;
    }
    public Ownership(int status, Const e1, Var e2) {
	this.status = status;
	this.e1 = e1;
	this.e2 = e2;
    }

    public static final int DEFAULT = 0;
    public static final int PINNED = 1;
    public static final int SPEC = 2; 
    public static final int RESOURCE = 3; 
    public static final int UNTRACKED = 4; 

    public boolean mustTrack() {
	return (status != DEFAULT && status != SPEC && status != UNTRACKED);
    }

    public String toString(Context ctxt) {
	switch (status) {
	case DEFAULT:
	    return "";
	case PINNED:
	    return "#<"+e1.toString(ctxt)+" "+e2.toString(ctxt)+">";
	case SPEC:
	    return "spec";
	case UNTRACKED:
	    return "#untracked";
	case RESOURCE:
	    return "#"+e1.toString(ctxt);
	default:
	    return "unrecognized status ("
		+(new Integer(status)).toString()+")";
	}
    }

    public guru.carraway.Expr toCarrawayType(Context ctxt, Position p) {
	guru.carraway.Context cctxt = ctxt.carraway_ctxt;

	switch (status) {
	case DEFAULT: {
	    guru.carraway.Sym e = cctxt.lookup("unowned");
	    if (e == null) 
		Expr.handleError(p,"The declaration of the \"unowned\" resource type is missing.  \n\n"
				 +"You need to include lib/unowned.g.");
	    return e;
	}
	case PINNED: 
	    return new guru.carraway.Pin((guru.carraway.Sym)e1.toCarrawayType(ctxt,true),
					 (guru.carraway.Sym)e2.toCarrawayType(ctxt,true));
	case UNTRACKED:
	    return new guru.carraway.Untracked();
	case RESOURCE:
	    return e1.toCarrawayType(ctxt,true);

	}
	return null;
    }
	
}