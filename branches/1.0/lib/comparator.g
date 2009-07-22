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
