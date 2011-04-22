Include "unique.g".
Include "ref.g".
Include "erase_ref.g".
Include "unique_owned.g". % temporarily added by Duckki
Include "debug_log.g".

Inductive qlist : Fun(A:type).type :=
  qnil : Fun(A:type).#unique <qlist A>
| qcons : Fun(A:type)(#unique a:A)(#unique l:<qlist A>). #unique <qlist A>.

% temporarily added by Duckki
Define primitive inspect_uniquew : Fun(spec A:type)(!#uniquew a:A).#<unique_owned a> A :=
  fun(spec A:type)(a:A).a <<END
#define ginspect_uniquew(a) a
END.

Define qlist_replace_ref := fun qlist_replace_ref
  (A:type)
  (!x:A) % the reference to find
  (y:A)  % replacement
  (^#uniquew l:<qlist <ref A>>)
  : bool. % success or not
  match !l with
  	qnil _ =>
  		do
  		(consume_unowned A y)
  		ff
  		end
  | qcons _ r l' =>
  		let a = (read_ref A (inspect_uniquew <ref A> r)) in
  		match (eqref A x a) with
  			ff =>
  				do
  				(consume_unowned A a)
  				(consume_uniquew <ref A> r)
  				(qlist_replace_ref A x y l')
  				end
  		| tt =>
					do
  				(consume_unowned A a)
					(consume_uniquew <qlist <ref A>> l')
					(write_ref_once A y r)
					tt
					end
  		end
  end.

Define qlist_erase_ref := fun
  (A:type)
  (!x:A)
  (#unique l:<qlist <ref A>>)
  :#unique <qlist <ref A>>.
  match l with
  	qnil _ => (qnil <ref A>)
  | qcons _ r l' =>
  		let a = (read_ref A (inspect_unique <ref A> r)) in
  		match (eqref A x a) with
  			ff =>
					match (get_uniquew <qlist <ref A>> l') with mk_get_uniquew_t _ l'_pinned l'_w =>
					match (qlist_replace_ref A x a l'_w) with
						ff =>
							let l'' = (unpin_unique <qlist <ref A>> l'_pinned) in
							(qcons <ref A> r l'')	% nothings erased, restore the original list
					| tt =>
							do
							(consume_unique <ref A> r)
							(unpin_unique <qlist <ref A>> l'_pinned)
							end
					end
					end
  		| tt =>
  				do
  				(consume_unowned A a)
					(consume_unique <ref A> r)
  				l'
  				end
  		end
  end
  .

Define qlength_word_h :=  fun qlength_word_h(A:type)(^#unique_owned l:<qlist A>)(i:word) : word.
  match l with
    qnil _ => i
  | qcons _ _ l' =>
      (qlength_word_h A l' (word_inc2 i))
  end.

Define qlength_word := fun(A:type)(!#unique l:<qlist A>).
  (qlength_word_h A (inspect_unique <qlist A> l) word0).
