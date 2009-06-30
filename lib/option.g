Inductive option : Fun(A:type).type :=
  nothing : Fun(spec A:type).<option A>
| something : Fun(A:type)(a:A).<option A>.
