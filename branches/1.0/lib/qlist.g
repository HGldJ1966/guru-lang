Include "unique.g".
Include "qlist.g".
Include "erase_ref.g".

Inductive qlist : Fun(A:type).type :=
  qnil : Fun(A:type).#unique <qlist A>
| qcons : Fun(A:type)(a:A)(#unique l:<qlist A>). #unique <qlist A>.


Define qlist_erase_ref := fun erase_ref
  (A:type)
  (!x:A)
  (#uniquew l:<qlist A>)
  : void.
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
