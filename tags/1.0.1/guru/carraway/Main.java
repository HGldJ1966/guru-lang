package guru.carraway;

public class Main {

    public Main() { }

    public static void main(String[] args)
    {
	Context ctxt = new Context();

	boolean processed_one = false;

	for (int i = 0; i < args.length; i++) 
	    if (args[i].equals("--help")) {
		System.out.println("carraway [--help | --output-ocaml] <input files>.");
		System.exit(0);
	    }
	    else if (args[i].equals("--output-ocaml"))
		ctxt.setFlag("output_ocaml");
	    else {
		if (processed_one) {
		    System.out.println("Command-line error: multiple input files were given on the command line.\n");
		    System.exit(1);
		}
		// Include cmd = new Include(args[i], true);
		// cmd.process(ctxt);
		System.out.println("Direct compilation for carraway is currently disabled.  Please go through Guru.\n");
		System.exit(1);
	    }
    }
}
