package guru;

public class Main {

    public Main() { }

    // exit status codes:
    //   0 = success
    //   1 = parse error
    //   2 = classification error
    //   3 = classification error: a Define is declared to have one type but has another
    //   4 = command processing error
    //   5 = internal classification error (something unimplemented etc.)
    //   6 = compiler error
    public static void main(String[] args)
    {
	Context ctxt = new Context();
	ctxt.setFlag("check_drop_annos_idem"); // see Define.java
	for (int i = 0; i < args.length; i++) 
	    if (args[i].equals("--help")) {
		System.out.println("Guru [input files].");
		System.exit(0);
	    }
	    else {
		Include cmd = new Include(args[i]);
		cmd.process(ctxt);
	    }
	java.util.Collection trusted = ctxt.getTrustedDefs();
	if (trusted.size() > 0) {
	    ctxt.w.println("Trusting "+(new Integer(trusted.size())).toString()
			   +":\n");
	    java.util.Iterator it = trusted.iterator();
	    if (ctxt.getFlag("print_trusted_details")) {
		boolean first = true;
		while(it.hasNext()) {
		    Const c = (Const)it.next();
		    if (first)
			first = false;
		    else
			ctxt.w.println("");
		    ctxt.w.print(c.name + " : ");
		    ctxt.getClassifier(c).print(ctxt.w,ctxt);
		    ctxt.w.println(".");
		}
	    }
	    else {
		while(it.hasNext()) {
		    Const c = (Const)it.next();
		    ctxt.w.print(" "+c.name);
		}
		ctxt.w.println("");
	    }
	    ctxt.w.flush();
	}
    }
}
