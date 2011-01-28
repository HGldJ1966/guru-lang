Include trusted "list.g".

Define primitive eqref : Fun(spec A:type)(! #unowned x y:A).bool <<END
inline unsigned geqref(void* x, void* y) {
	return (x == y)? gtt(): gff();
}
END.

Define erase_ref := fun erase_ref
  (A:type)
  (!x:A)
  (l:<list A>)
  : <list A>.
  match l with
    nil _ => (nil A)
  | cons _ a l' =>
      match (eqref A x a) with
				ff => (cons A a (erase_ref A x l'))
			| tt =>
				do
				(consume_unowned A a)
				(erase_ref A x l')
				end
			end
  end.
