Include "bool.g".
Include "owned.g".

Inductive comp : type :=
  LT : comp
| EQ : comp
| GT : comp.

Define comparator1: Fun(A:type)(lt:Fun(^ #owned a b:A).bool)(eq:Fun(^ #owned a b:A).bool)
       		       (^ #owned x y:A). comp :=
  fun(A:type)(lt:Fun(^ #owned a b:A).bool)(eq:Fun(^ #owned a b:A).bool)
     (^ #owned x y:A).
    match (lt (clone_owned A x) (clone_owned A y)) with
      ff => match (eq x y) with
      	      ff => GT
 	    | tt => EQ
	    end
    | tt => do (consume_owned A x)
      	       (consume_owned A y)
	       LT
	    end
    end.

Define comparator2: Fun(A:type)(lt:Fun(w1 w2:A).bool)
       		    	       (le:Fun(w1 w2:A).bool)
		       (x y:A). comp :=
  fun(A:type)(lt:Fun(w1 w2:A).bool)
       	     (le:Fun(w1 w2:A).bool)
     (x y:A).
  match (lt x y) with
    ff => match (le x y) with
            ff => GT
	  | tt => EQ
          end
  | tt => LT
  end.

Define ucomparator: Fun(A:type)(lt:Fun(#untracked w1 w2:A).bool)
       		    	       (le:Fun(#untracked w1 w2:A).bool)
		       (#untracked x y:A). comp :=
  fun(A:type)(lt:Fun(#untracked w1 w2:A).bool)
       	     (le:Fun(#untracked w1 w2:A).bool)
     (#untracked x y:A).
  match (lt x y) with
    ff => match (le x y) with
            ff => GT
	  | tt => EQ
          end
  | tt => LT
  end.
