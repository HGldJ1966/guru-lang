Include "unique.g".

Inductive qoption : Fun(A:type).type :=
  qnothing : Fun(spec A:type).#unique <qoption A>
| qsomething : Fun(A:type)(#unique a:A).#unique <qoption A>.
