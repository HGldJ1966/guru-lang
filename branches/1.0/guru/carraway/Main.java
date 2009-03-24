package guru.carraway;

public class Main {

    public Main() { }

    public static void main(String[] args)
    {
	Context ctxt = new Context(".w");

	boolean processed_one = false;

	for (int i = 0; i < args.length; i++) 
	    if (args[i].equals("--help")) {
		System.out.println("carraway <input files>.");
		System.exit(0);
	    }
	    else {
		if (processed_one) {
		    System.out.println("Command-line error: multiple input files were given on the command line.\n");
		    System.exit(1);
		}
		Include cmd = new Include(args[i], true);
		cmd.process(ctxt);
	    }
    }
}
