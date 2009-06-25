Include "unique.g".

Inductive pair : Fun(A B:type).type :=
  mkpair : Fun(spec A B:type)(#unique a:A)(#unique b:B). #unique <pair A B>.

