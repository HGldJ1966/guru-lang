package guru;
import java.io.*;
import java.util.*;

public class ParserBase {
    
    protected PushbackReader pr;
    protected int linenum;
    protected int column;
    protected int prev_column;
    protected String file;
    protected File root;

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

    int tabwidth = 2;	// todo: should be configurable
    
    protected int getc() throws IOException {
	int c = pr.read();
	if ((char)c == '\n') {
	    prev_column = column;
	    linenum++;
	    column=1;
	}
	else if ((char)c == '\t')
		column += tabwidth;
	else if (c != -1)	// EOF doesn't count
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

    protected void handleWarning(String msg)
    {
    	handleWarning(new Position(linenum, column, file), msg);
    }
    
    protected void handleWarning(Position pos, String msg)
    {
    	pos.print(System.out);
        System.out.println(": parse warning - "+msg);
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
                if(c != -1)
                    ungetc(c);
		break;
            }
            theID.append(ch);
        } while(true);

	if (theID.length() == 0)
	    handleError("Expected an identifier.");

        return theID.toString();
    }


	protected String readHex() throws IOException
	{
		int c;
		StringBuffer hexBuf = new StringBuffer();
		while (true) {
			c = getc();
			//Check for 0-9, A-F, a-f
			if ((! ((c <= 57 && c >= 48) || (c >= 65 && c<=70) ||
				(c >= 97 && c <= 102))) || c == -1) {
				if(c != -1)
					ungetc(c);
				break;
			}
			hexBuf.append((char) c);
		}
		if (hexBuf.length() == 0)
			handleError("No hex digits specified after 0x .");
		if (hexBuf.length() > 8)
			handleError("Hex value greater than 32-bits.");
		return hexBuf.toString();
	}


    protected String readString(Character delimiter) throws IOException
    {
        int c;
        String s="";
        boolean escaped = false;
	c=getc();

	if ((char)c != delimiter.charValue())
	    if(delimiter.charValue() == '\"')
	    	handleError("Expecting a double quotation mark (\") to start a"
			+" string.");
	    else
	    	handleError("Expecting a single quotation mark (\') to start a"
			+" character.");

        do{
	    c=getc();
	    if ((char)c == '\\') {
	        if (! escaped)
                    escaped = true;
                else
                    escaped = false;
            } else if ((char)c == delimiter.charValue()) {
                if (!escaped)
                    break;
                escaped = false;
            } else if (c == -1) {
                if (delimiter.charValue() == '\"')
                    handleError("Expecting a double quotation mark (\") to end a"
                                +" string");
                else
	            handleError("Expecting a single quotation mark (\') to end a"
			+" character.");

            } else {
                escaped = false;
            }

            s+=(char)c;
        } while(true);
        
	if(delimiter.charValue() == '\'')
           if ((s.length() == 2) && ((int)s.charAt(0) == 92))
               return s;
           else if (s.length() > 2)
               handleError("Expecting only one alphanumeric for a character.");
	return s;
    }

    //Default mething for reading strings
    protected String readString() throws IOException
    {
	return readString(new Character('\"'));
    }


    protected String read_until_newline_delim(String delim) 
	throws IOException 
    {
        StringBuffer code_str = new StringBuffer();

	int c;
	char ch;
	do{
            c=getc();
            ch=(char) c;
	    if (c == -1) 
		handleError("Unexpected end of delimited text.\n\n"
			    +"1. the text read (starts on next line):\n"
			    +code_str.toString());
	    if (ch == '\n') {
		/* check to see if we have reached our delimiter */
		if (tryToEat(delim))
		    return code_str.toString();
            }
            code_str.append(ch);
        } while(true);
    }

    protected void eat(String kw, String parsing_what) throws IOException {
	if (!eat_ws())
	    handleError("Unexpected end of input parsing "+parsing_what);
	if (!tryToEat(kw)) {
	    if (kw == "\n")
		handleError("Expected newline parsing "+parsing_what);
	    handleError("Expected \""+kw+"\" parsing "+parsing_what);
	}
    }

    // [Duckki] more flexible syntax:
    // allows to omit delimiters like "in" when a new line starts.
    protected void eatDelim(String kw, String parsing_what) throws IOException {
    	boolean	delim_ok = false;
    	if( lineBreakDelimiter )	// already satisfied a delimiter
    		delim_ok = true;
    	if( !eat_ws() )
    		return;	// EOF is also considered a delimiter
    	if (!tryToEat(kw)) {
        	if( delim_ok || lineBreakDelimiter )
        		return;	// OK - a new line is considered a proper delimiter
    	    if (kw == "\n")
        		handleError("Expected newline parsing "+parsing_what);
    	    else
    	    	handleError("Expected \""+kw+"\" (or line break) parsing "+parsing_what);
    	}
	}

    protected boolean tryToEat(String kw) throws IOException 
    {
	return tryToEat(kw.toCharArray());
    }

    // see below for ok_if_id.
    protected boolean tryToEat(String kw, boolean ok_if_id) throws IOException 
    {
	return tryToEat(kw.toCharArray(),ok_if_id);
    }

    protected boolean tryToEat(char[] kw) throws IOException {
	return tryToEat(kw,false);
    }
    
    /* try to eat the string kw.  When ok_if_id is true, we will not
       consider the next character after kw in the input string;
       otherwise, we will make sure that it is not a legal character
       for an identifier, thus ruling out eating prefixes of
       identifiers. */
    protected boolean tryToEat(char[] kw, boolean ok_if_id) throws IOException {
	int c;
	int cur = 0;
	
	c = getc();
	while (c != -1 && cur < kw.length) {
	    char b = kw[cur++];

	    /*System.out.print("tryToEat c = ");
	    System.out.print((char)c);
	    System.out.print("b = ");
	    System.out.println(b);  */
	    
	    if ((char)c != b) {
		ungetc(c);
		for (int j = cur-2; j >= 0; j--)
			ungetc(kw[j]);
			
		//System.out.println("tryToEat returning false (1).");
		//System.out.flush();

		return false;
	    }
	    c = getc();
	}
	int j = kw.length - 1;
	ungetc(c);
	if (Character.isLetterOrDigit(kw[j]))
	    if (c != -1 && !ok_if_id && !Character.isWhitespace((char)c) && LegalIdChar((char)c)) {
		// a keyword ending in a letter or number is being
		// followed by a character allowed for variables, thus
		// yielding an identifier, not a keyword.
		for ( ; j>=0; j--)
		    ungetc(kw[j]);
		//System.out.println("tryToEat returning false with c = "+(char)c);
		return false;
	    }

	/* System.out.println("ate "+java.util.Arrays.toString(kw));
	  System.out.flush();*/
	lineBreakDelimiter = false;	// an optional keyword disqualifies line-break delimiters
	return true;
    }

    boolean	lineBreakDelimiter = false;
    
    // return false if we encounter end of file, true otherwise
    protected boolean eat_ws() throws java.io.IOException {
	int i;
	int comment_level = 0; // how far are we nested in comments
	boolean in_single_line_comment = false;

	lineBreakDelimiter = false;
	while ((i = getc()) != -1) {
	    char c = (char)i;
	    if (Character.isWhitespace(c)) {
		if (c == '\n') {
		    if (in_single_line_comment) {
			comment_level--;
			in_single_line_comment = false;
		    }
		    lineBreakDelimiter = true;	// A line break qualify a delimiter
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
		else if ((char)j == '\n')
		    // we start and immediately end a single line comment
		    continue;
		else
		    // this % is starting a single line comment
		    if (comment_level == 0 && !in_single_line_comment) {
			in_single_line_comment = true;
			comment_level++;
		    }
	    }
	    else if (c == '-') {
		// this might be ending a nested comment
		int j = getc();
		if ((char)j == '%') {
		    if (in_single_line_comment)
			handleError("A comment is being closed with \"-%\" "
				    +"inside a single-line comment.  This is not allowed.\n");
		    if (comment_level == 0)
			handleError("A comment is being closed with \"-%\" "
				    +"where\nthe parser does not find a"
				    +" matching \"%-\"\n"
				    +"to start the comment.");
		    comment_level--;
		}
		else 
		    ungetc(j);
	    }
	    else if (comment_level == 0) {
		// we have encountered a non-whitespace character that
		// is not starting a comment, and we are not already inside
		// a comment
		ungetc(i);
		return true;
	    }
	}
    if (comment_level != 0)
    	handleWarning("A comment is not closed at the end of file\n");
	return false; // we encountered EOF
    }

    
   protected boolean LegalIdChar(char ch)
   {
       if("@$<>|(){}[]=%:.-\"#".indexOf(ch)>=0)
            return false;
       else
           return true;             
   }
}

