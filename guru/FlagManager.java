package guru;
import java.io.*;
import java.util.HashMap;

public class FlagManager {

    protected HashMap flags;

    public PrintStream w;

    public FlagManager() {
	flags = new HashMap(256);
	w = new PrintStream(new BufferedOutputStream(System.out));
    }

    public FlagManager(FlagManager prev) {
	flags = prev.flags;
	w = prev.w;
    }

    public void setFlag(String flag) {
	flags.put(flag, new Boolean(true));
    }

    public void unsetFlag(String flag) {
	flags.put(flag, new Boolean(false));
    }

    public boolean getFlag(String flag) {
	Boolean b = (Boolean)flags.get(flag);
	if (b == null)
	    return false;
	return b.booleanValue();
    }

    public java.util.Collection getFlags() {
	return flags.keySet();
    }

    public void copyFlags(FlagManager fm) {
	java.util.Iterator it = fm.getFlags().iterator();
	while(it.hasNext()) {
	    String flag = (String)it.next();
	    if (fm.getFlag(flag)) 
		setFlag(flag);
	}
    }

}