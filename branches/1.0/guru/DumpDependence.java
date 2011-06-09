package guru;
import java.io.*;
import java.util.*;

public class DumpDependence extends Command {
    public String outfile;
    protected TreeSet trackedFiles;
    protected TreeSet tracked;
    protected TreeSet limitFiles;
    protected TreeSet limitIDs;

    public DumpDependence() {
	super(DUMPDEPENDENCE);
    }

    public void limitID(String id) {
        if(limitIDs == null)
            limitIDs = new TreeSet();
        limitIDs.add(id);
    }

    public void trackID(Const c) {
        if(tracked == null)
            tracked = new TreeSet();
        tracked.add(c);
    }

    public void limitFile(File root, String filename) {
        File tmp = null;

        if(limitFiles == null)
            limitFiles = new TreeSet();

        // this code has to match what's in Include.java so that paths
        // in Positions match exactly
        tmp = new File(filename);
        if(!tmp.isAbsolute())
            tmp = new File(root.getAbsolutePath() + "/" + tmp.getPath());

        try {
            tmp = tmp.getCanonicalFile();
        } catch(IOException e) {
            System.out.println("Error locating dependence-limiting source "
                               +"file \""+filename+"\"\n"+e.toString());
            System.exit(4);
        }

        String p = tmp.getAbsolutePath();
        limitFiles.add(p);
    }

    public void trackFile(File root, String filename) {
        File tmp = null;

        if(trackedFiles == null)
            trackedFiles = new TreeSet();

        // this code has to match what's in Include.java so that paths
        // in Positions match exactly
        tmp = new File(filename);
        if(!tmp.isAbsolute())
            tmp = new File(root.getAbsolutePath() + "/" + tmp.getPath());

        try {
            tmp = tmp.getCanonicalFile();
        } catch(IOException e) {
            System.out.println("Error locating tracked source file "
                               +"\""+filename+"\"\n"+e.toString());
            System.exit(4);
        }

        String p = tmp.getAbsolutePath();
        trackedFiles.add(p);
    }

    private boolean inTheLimit(Const c1, Const c2) {
        if(limitIDs == null && limitFiles == null)
            return true;

        boolean c1y = false, c2y = false;

        if(limitIDs != null) {
            c1y = limitIDs.contains(c1.name);
            c2y = limitIDs.contains(c2.name);
        }

        if(limitFiles != null) {
            c1y = c1y || limitFiles.contains(c1.pos.file);
            c2y = c2y || limitFiles.contains(c2.pos.file);
        }

        return c1y && c2y;
    }

    public void process(Context ctxt) {
        PrintStream out = null;
        boolean output = false;
        boolean deps = false;

        // keep a separate copy of tracked so that the print()
        // method prints the input as it was initially
        TreeSet all_tracked =
            (tracked != null) ? (TreeSet)tracked.clone() : new TreeSet();

        try {
            out = new PrintStream(
                      new BufferedOutputStream(
                          new FileOutputStream(outfile)));
        } catch(IOException e) {
            System.out.println("error opening dependence output file "+outfile);
            System.exit(4);
        }

	out.println("/*");
	out.println(" * Note that _trusted_ lemmas are displayed as circles and _untrusted_ lemmas as diamonds.");
	out.println(" */");
        out.println("digraph dependence {");

        if(trackedFiles != null) {
            Collection csts = ctxt.getDefinedConsts();
            for(Iterator i = csts.iterator(); i.hasNext();) {
                Const cst = ((Const)i.next());
                if(trackedFiles.contains(cst.pos.file))
                    all_tracked.add(cst);
            }
        }

        if(all_tracked.isEmpty()) {
            for(Iterator i = ctxt.getTypeCtors().iterator(); i.hasNext();)
                all_tracked.add(((Const)i.next()));
            for(Iterator i = ctxt.getDefinedConsts().iterator(); i.hasNext();)
                all_tracked.add(((Const)i.next()));
        }

        TreeSet typeSet = new TreeSet();
        TreeSet proofSet = new TreeSet();

        LinkedList worklist = new LinkedList();
        worklist.addAll(all_tracked);
        TreeSet finished = new TreeSet();

        while(!worklist.isEmpty()) {
	    Const c1 = (Const)worklist.removeFirst();

            if(finished.contains(c1))
                continue;
            finished.add(c1);

            Expr cst = ctxt.lookup(c1.name);
            if(cst == null) {
                handleError(ctxt, "DumpDependence: identifier `" + c1.name + "' "
                            +"not found in context.");
                continue;
            }
            if(cst.construct != Expr.CONST) {
                handleError(ctxt, "DumpDependence: can't handle identifier "
                            + "`" + c1.name + "', which is a "
                            + cst.getClass().getName() + ".");
                continue;
            }

            Expr t = ctxt.getClassifier((Const)cst);
            Expr e = ctxt.getDefBody((Const)cst);

            java.util.Set depset = t.getDependences();

            if(e != null)
                depset.addAll(e.getDependences());

            TreeSet typedeps = new TreeSet();
            for(Iterator j = depset.iterator(); j.hasNext();) {
                Const c = (Const)j.next();
                if(ctxt.isTermCtor(c)) {
                    // flatten ctors to their types (or type constructors)
                    j.remove();
                    Expr ex = ctxt.getClassifier(c);
                    if(ex.construct == Expr.FUN_TYPE)
                        ex = ((FunType)ex).body;
                    if(ex.construct == Expr.TYPE_APP)
                        ex = ((App)ex).getHead(ctxt, false, true, false);
                    typedeps.add(ex);
                }
            }

            depset.addAll(typedeps);
            for(Iterator j = depset.iterator(); j.hasNext();) {
                Const c = (Const)j.next();
                // NOTE you can get a disconnected graph when tracking
                // one specific ID if a (transitive) dependence leaves
                // the limited set of IDs/files then re-enters it
                if(!finished.contains(c))
                    worklist.addFirst(c);
                if(inTheLimit((Const)cst, c)) {
                    out.println(c1.name + " -> " + c.name + ";");
                    deps = output = true;

                    if(ctxt.isTypeCtor((Const)cst))
                        typeSet.add((Const)cst);
                    else if(ctxt.getClassifier((Const)cst).isFormula(ctxt))
                        proofSet.add(c1);

                    if(ctxt.isTypeCtor(c))
                        typeSet.add(c);
                    else if(ctxt.getClassifier(c).isFormula(ctxt))
                        proofSet.add(c);
                }
            }
        }
        for(Iterator i = typeSet.iterator(); i.hasNext();) {
            Const cst = (Const) i.next();
            output = true;
            out.println(cst.name + " [shape=record];");
            Collection ctorList = ctxt.getTermCtors(cst);
            if(ctorList != null) {
                out.print(cst.name + " [label=\"{\\N|");
                for(Iterator ctors = ctorList.iterator(); ctors.hasNext();)
                    out.print(((Expr)ctors.next()).toString(ctxt)+"\\n");
                out.println("}\"];");
            }
        }
        for(Iterator proofs = proofSet.iterator(); proofs.hasNext();) {
            Const proof = (Const) proofs.next();
            output = true;
	    if (ctxt.isTrusted(proof))
		out.println(proof.name+" [shape=circle];");
	    else
		out.println(proof.name+" [shape=diamond];");
        }

        out.println("}");
        out.close();
        out = null;

        if(!output) {
            handleWarning(ctxt, "dependence information empty; "
                          +"possibly improper track or limit clauses?");
        } else if(!deps) {
            handleWarning(ctxt, "no dependences found between top-level "
                          +"definitions; possibly improper\n"
                          +"track or limit clauses?");
        }
    }

    public void print(java.io.PrintStream w, Context ctxt) {
	w.print("DumpDependence to \""+outfile+"\"");
        if(tracked != null || trackedFiles != null) {
            w.print(" track");
            if(tracked != null)
                for(Iterator i = tracked.iterator(); i.hasNext();)
                    w.print(" " + ((Const)i.next()).name);
            if(trackedFiles != null)
                for(Iterator i = trackedFiles.iterator(); i.hasNext();)
                    w.print(" \"" + i.next() + "\"");
            w.print(" end");
        }
        if(limitIDs != null || limitFiles != null) {
            w.print(" limit to");
            if(limitIDs != null)
                for(Iterator i = limitIDs.iterator(); i.hasNext();)
                    w.print(" " + i.next());
            if(limitFiles != null)
                for(Iterator i = limitFiles.iterator(); i.hasNext();)
                    w.print(" \"" + i.next() + "\"");
            w.print(" end");
        }
        w.println(".");
    }
}
