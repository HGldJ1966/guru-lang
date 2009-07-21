Include "unique.g".

Inductive qpair : Fun(A B:type).type :=
  mkqpair : Fun(A B:type)(a:A)(#unique b:B). #unique <qpair A B>.

