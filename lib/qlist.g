Include "unique.g".

Inductive qlist : Fun(A:type).type :=
  qnil : Fun(A:type).#unique <qlist A>
| qcons : Fun(A:type)(#unique a:A)(#unique l:<qlist A>).#unique <qlist A>.
