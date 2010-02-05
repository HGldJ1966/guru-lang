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
          ctxt.w.print("The following ");
          ctxt.w.print( i );
          ctxt.w.println(" definitions use the elements of your locate query: ");
          ctxt.w.println("");

          for (int k = 0; k < usingDefs.size(); k++){
               Const c = (Const)usingDefs.get(k);
               ctxt.w.print(k+1);
               ctxt.w.print(") ");
               c.print(ctxt.w, ctxt);
               ctxt.w.println("");
               Expr e = (Expr)ctxt.getClassifier(c);
               ctxt.w.print("   Classifier: ");
               e.print(ctxt.w, ctxt);
               ctxt.w.println("");
               Position p = e.pos;
               ctxt.w.print("   Location: ");
               p.printNoQuotes(ctxt.w);
               ctxt.w.println("\n");
          }
        }
     
    }

    public void print(java.io.PrintStream w, 
		      Context ctxt) {

    }
}
