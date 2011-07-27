Include "unique.g".

Inductive qqpair : Fun(A B:type).type :=
  mkqqpair : Fun(A B:type)(#unique a:A)(#unique b:B). #unique <qqpair A B>.

