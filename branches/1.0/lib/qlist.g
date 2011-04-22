Include "unique.g".

Inductive qlist : Fun(A:type).type :=
  qnil : Fun(A:type).#unique <qlist A>
| qcons : Fun(A:type)(a:A)(#unique l:<qlist A>). #unique <qlist A>.

% Define qlist_remove : Fun(A:type)(a:A)(eqA:Fun(x y : A)