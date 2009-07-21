Include "bool.g".
Include "owned.g".

Inductive comp : type :=
  LT : comp
| EQ : comp
| GT : comp.

Define comparator1: Fun(A:type)(leq:Fun(a b:A).bool)(eq:Fun(^ #owned a b:A).bool)
       		      (x y:A). comp :=
  fun(A:type)(leq:Fun(a b:A).bool)(eq:Fun(^ #owned a b:A).bool)(x y:A).
    match (leq x y) with
      ff => GT
    | tt => match (eq x y) with
              ff => LT
            | tt => EQ
            end
    end.

Define comparator2: Fun(A:type)(leq:Fun(#untracked a b:A).bool)
                               (eq:Fun(#untracked a b:A).bool)(x y:A). comp :=
  fun(A:type)(leq:Fun(#untracked a b:A).bool)
             (eq:Fun(#untracked a b:A).bool)(x y:A).
    match (leq x y) with
      ff => GT
    | tt => match (eq x y) with
              ff => LT
            | tt => EQ
            end
    end.
