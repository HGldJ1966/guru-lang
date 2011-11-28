Include "bool.g".
Include "owned.g".

Inductive option : Fun(A:type).type :=
  nothing : Fun(spec A:type).<option A>
| something : Fun(A:type)(a:A).<option A>.

Define is_something : Fun(A:type)(^#owned o:<option A>). bool :=
  fun(A:type)(^#owned o:<option A>).
      match ! o with
        nothing _ => ff
      | something _ a => tt
      end.