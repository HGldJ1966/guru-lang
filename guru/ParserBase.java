package guru;
import java.io.*;
import java.util.*;

public class ParserBase {
    
    PushbackReader pr;
    int linenum;
    int column;
    int prev_column;
    String file;
    File root;

    protected static final boolean using_metavars = false;

    public ParserBase() {
	linenum = 1;
	column = 1;
	prev_column = 0;
    }
    
    public void Reset() {
	linenum = 1;
	column = 1;
	prev_column = 0;
    }	

    protected int getc() throws IOException {
	int c = pr.read();
	if ((char)c == '\n') {
	    prev_column = column;
	    linenum++;
	    column=0;
	}
	else
	    column++;
	return c;
    }

    protected void ungetc(int c) throws IOException {
	if (c == -1)
	    // it seems pushing back -1 causes problems
	    return;
	if ((char)c == '\n') {
	    column=prev_column;
	    linenum--;
	}
	else
	    column--;
  	pr.unread(c);
    }

    public void openFile(String fn)
	throws IOException
    {
	FileReader fr = new FileReader(fn);
	BufferedReader br = new BufferedReader(fr);
	pr = new PushbackReader(br, 20);
	file = fn;
	root = new File(file).getCanonicalFile().getParentFile();
    }

    protected void handleError(String msg)
    {
	handleError(new Position(linenum, column, file), msg);
    }

    protected void handleError(Position pos, String msg)
    {
	pos.print(System.out);
        System.out.println(": parse error.\n"+msg);
        System.exit(1);
    }

    protected Position getPos() {
	return new Position(linenum,column,file);
    }

    static public int[] toIntArray(ArrayList a) {
	int iend = a.size();
	int[] v = new int[iend];
	for (int i = 0; i < iend; i++)
	    v[i] = ((Integer)a.get(i)).intValue();
	return v;
    }

    static public boolean[] toBooleanArray(ArrayList a) {
	int iend = a.size();
	boolean[] v = new boolean[iend];
	for (int i = 0; i < iend; i++)
	    v[i] = ((Boolean)a.get(i)).booleanValue();
	return v;
    }

    protected String readID ()
        throws IOException
    {
        int c;
        char ch;
        StringBuffer theID = new StringBuffer();

        do{
            c=getc();
            ch=(char) c;
	    if (c == -1 || Character.isWhitespace(ch) || !LegalIdChar(ch))
            {
                if(!LegalIdChar(ch))
                    ungetc(c);
		break;
            }
            theID.append(ch);
        } while(true);

	if (theID.length() == 0)
	    handleError("Expected an identifier.");

        return theID.toString();
    }

    protected String readString() throws IOException
    {
        int c;
        String s="";
	c=getc();

	if ((char)c != '"')
	    handleError("Expecting a double quotation mark (\") to start a"
			+" string.");
        do{
	    c=getc();
	    if (c == -1 || (char)c == '"') {
		break; 
            }
            s+=(char)c;
        } while(true);
        
	return s;
    }
    
    protected void eat(String kw, String parsing_what) throws IOException {
	if (!eat_ws())
	    handleError("Unexpected end of input parsing "+parsing_what);
	if (!tryToEat(kw))
	    handleError("Expected \""+kw+"\" parsing "+parsing_what);
    }

    protected boolean tryToEat(String kw) 
	throws IOException 
    {
	return tryToEat(kw.toCharArray());
    }

    protected boolean tryToEat(char[] kw) 
	throws IOException 
    {
	int c;
	int cur = 0;
	
	c = getc();
	while (c != -1 && cur < kw.length) {
	    char b = kw[cur++];
	    if ((char)c != b) {
		ungetc(c);
		for (int j = cur-2; j >= 0; j--)
			ungetc(kw[j]);
			
		
		return false;
	    }
	    c = getc();
	}
	int j = kw.length - 1;
	ungetc(c);
	if (Character.isLetterOrDigit(kw[j]))
	    if (!Character.isWhitespace((char)c) && LegalIdChar((char)c)) {
		// a keyword ending in a letter or number is being
		// followed by a character allowed for variables, thus
		// yielding an identifier, not a keyword.
		for ( ; j>=0; j--)
		    ungetc(kw[j]);
		return false;
	    }
	return true;
    }

    // return false if we encounter end of file, true otherwise
    protected boolean eat_ws() throws java.io.IOException {
	int i;
	int comment_level = 0; // how far are we nested in comments
	boolean in_single_line_comment = false;

	while ((i = getc()) != -1) {
	    char c = (char)i;
	    if (Character.isWhitespace(c)) {
		if (c == '\n') {
		    if (in_single_line_comment) {
			comment_level--;
			in_single_line_comment = false;
		    }
		}
		continue; // with while loop
	    }
	    else if (c == '%') {
		// check if this starting a new nested comment
		int j = getc();
		if (j == -1)
		    return false;
		if ((char)j == '-') 
		    // yes, this is a new nested comment
		    comment_level++;
		else 
		    // this % is starting a single line comment
		    if (comment_level == 0 && !in_single_line_comment) {
			in_single_line_comment = true;
			comment_level++;
		    }
	    }
	    else if (c == '-') {
		// we are expecting this will end a nested comment
		int j = getc();
		if ((char)j == '%') {
		    if (comment_level == 0)
			handleError("A comment is being closed with \"-%\" "
				    +"where\nthe parser does not find a"
				    +" matching \"%-\"\n"
				    +"to start the comment.");
		    comment_level--;
		}
	    }
	    else if (comment_level == 0) {
		// we have encountered a non-whitespace character that
		// is not starting a comment, and we are not already inside
		// a comment
		ungetc(i);
		return true;
	    }
	}
	return false; // we encountered EOF
    }

    
   protected boolean LegalIdChar(char ch)
   {
       if("<>|(){}[]=%:.-\"".indexOf(ch)>=0)
            return false;
       else
           return true;             
   }
}

