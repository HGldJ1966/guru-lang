Include "subset.g".


%====== statement that cardinality of A|f2 <= cardinality of A|f1
Inductive cardinality_le_P := Fun( a : A )( f1 f2 : Fun( a : A ). A ).type :=
  cardinality_le_p : Fun( a : A )( f1 f2 : Fun( a : A ). A )( g : Fun( a : A ).A )
                        ( u : <feq_P A A f1 (compose A A f1 g)> ).<cardinality_le_P A f1 f2>.
