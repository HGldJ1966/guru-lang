package guru;
import java.util.*;

public class DiscriminationTree {
	ArrayList	ValueTable;
	ArrayList	TransTable;
	
	public DiscriminationTree()
	{
		ValueTable = new ArrayList();
		TransTable = new ArrayList();
	}
	
	void add( int state, byte[] word, int pos, Integer val )
	{
		assert( state <= ValueTable.size() );
		if( state == ValueTable.size() )	// new state!
		{
			//System.out.println( "new state: " + String.valueOf(state) );
			ValueTable.add( null );
			TransTable.add( new Integer[0x100] );
		}
		//System.out.println( "at state: " + String.valueOf(state) );
		if( pos == word.length ) {	// final state
			//System.out.println( "set value: " + val.toString() );
			ValueTable.set( state, val );
			return;
		}
		byte		index = word[pos];
		Integer[]	map = (Integer[])TransTable.get( state );
		Integer		next = map[index];
		if( next == null ) {	// no edge
			next = new Integer( ValueTable.size() );	// new state
			map[index] = next;
		}
		add( next.intValue(), word, pos+1, val );
	}
	
	public void add( String word, int val ) {
		add( 0, word.getBytes(), 0, new Integer(val) );
	}
		
	public class Iterator {
		Integer		value;
		Integer[]	map;
		
		boolean isValid() {
			return map != null;
		}
		
		boolean isFinal() {
			return value != null;
		}
		
		public void next( int ch ) {
			if( map == null )
				return;
			if( ch >= 0 && ch <= 0xff ) {
				Integer	next_st = map[ch];
				if( next_st != null ) {
					value = (Integer)ValueTable.get( next_st.intValue() );
					map = (Integer[])TransTable.get( next_st.intValue() );
					return;
				}
			}
			value = null;
			map = null;
		}
	}
	
	public Iterator begin() {
		Iterator	it = new Iterator();
		it.value = (Integer)ValueTable.get( 0 );
		it.map = (Integer[])TransTable.get( 0 );
		return it;
	}
}
