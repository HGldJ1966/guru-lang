package guru.carraway;

public class Main {

    public Main() { }

    public static void main(String[] args)
    {
	Context ctxt = new Context();
	for (int i = 0; i < args.length; i++) 
	    if (args[i].equals("--help")) {
		System.out.println("carraway [input files].");
		System.exit(0);
	    }
	    else {
		Include cmd = new Include(args[i]);
		cmd.process(ctxt);
	    }
    }
}
