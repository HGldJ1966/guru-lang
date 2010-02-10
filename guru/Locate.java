package guru;

import java.util.*;

public class Locate extends Command {
    public Const[] c;

    public Locate() {
	super(LOCATE);
    }

    public void process(Context ctxt) {
       Const d = c[0];
       Vector usingDefs = new Vector(ctxt.getUsingDefs(d));
    
        for (int i = 1; i < c.length; i++) {
           d = c[i];
           Vector compareDefs = new Vector(ctxt.getUsingDefs(d));
           usingDefs.retainAll(compareDefs);
        
        }
      
        if (usingDefs.isEmpty()){
           ctxt.w.println("");
           ctxt.w.println("Locate query returned zero results.");
        } else {
          int i = usingDefs.size();
          ctxt.w.println("");
          ctxt.w.println("The following " + i + " definitions use the elements of your locate query: ");

          for (int k = 0; k < usingDefs.size(); k++){
               Const c = (Const)usingDefs.get(k);
               ctxt.w.print(k+1 + ") ");
               c.print(ctxt.w, ctxt);
               ctxt.w.print(" : ");
               Expr e = (Expr)ctxt.getClassifier(c);
               e.print(ctxt.w, ctxt);
               ctxt.w.println("");
               Position p = e.pos;
               ctxt.w.print("Location: ");
               p.printNoQuotes(ctxt.w);
               ctxt.w.println("\n");
          }
        }
     
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {

    }
}
