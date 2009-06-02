package guru;

public class Position {
    public int linenum;
    public int column;
    public String file;

    public Position(int linenum, int column, String file) {
	this.linenum = linenum;
	this.column = column;
	this.file = file;
    }
    
    public void print(java.io.PrintStream w) {
	w.print("\"");
	w.print(file);
	if (linenum > 0) {
		w.print("\", line ");
		w.print(new Integer(linenum));
		w.print(", column ");
		w.print(new Integer(column));
	}
	else
		w.print("\" ");
    }

    public String toString() {
	java.io.ByteArrayOutputStream s = new java.io.ByteArrayOutputStream();
	java.io.PrintStream w = new java.io.PrintStream(s);
	print(w);
	return s.toString();
    }

    public void printNoQuotes(java.io.PrintStream w) {
	w.print(file);
	if (linenum > 0) {
		w.print(", line ");
		w.print(new Integer(linenum));
		w.print(", column ");
		w.print(new Integer(column));
	}
	else
		w.print(" ");
    }

    public String toStringNoQuotes() {
	java.io.ByteArrayOutputStream s = new java.io.ByteArrayOutputStream();
	java.io.PrintStream w = new java.io.PrintStream(s);
	printNoQuotes(w);
	return s.toString();
    }
}
