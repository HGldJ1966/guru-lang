Inductive option : Fun(A:type).type :=
  nothing : Fun(spec A:type).<option A>
| something : Fun(A:type)(a:A).<option A>.

Define is_something : Fun(A:type)(^#owned o:<option A>). bool :=
  fun(A:type)(^#owned o:<option A>).
  let ret = 
      match ! o with
        nothing _ => ff
      | something _ a => do (consume_owned A a) tt end
      end in
  do (consume_owned <option A> o)
     ret
  end.