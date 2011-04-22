Include "unique.g".
Include "ref.g".
Include "erase_ref.g".
Include "unique_owned.g". % temporarily added by Duckki

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
  match l with
  	qnil _ => ff
  | qcons _ r l' =>
  		let a = (read_ref A (inspect_uniquew <ref A> r)) in
  		match (eqref A x a) with
  			ff => (qlist_replace_ref A x y l')
  		| tt =>
  				% cannot overwrite r because r is already uniquew, and no pinned_unique ref here
					match (get_uniquew <ref A> r) with mk_get_uniquew_t _ rp rw =>
					let rw' = (write_ref A y rp rw) in
					let r' = (unpin_unique <ref A> rp) in
					tt
					end
  		end
  end.

Define qlist_erase_ref := fun
  (A:type)
  (!x:A)
  (#unique l:<qlist <ref A>>)
  .
  match l with
  	qnil _ => (qnil <ref A>)
  | qcons _ r l' =>
  		let a = (read_ref A (inspect_uniquew <ref A> r)) in
  		match (eqref A x a) with
  			ff =>
					match (get_uniquew <qlist <ref A>> l') with mk_get_uniquew_t _ l'_pinned l'_w =>
					match (qlist_replace_ref A x a l'_w) with
						ff =>
							let l'' = (unpin_unique <qlist <ref A>> l'_pinned) in
							(qcons <ref A> r l')	% nothings erased, restore the original list
					| tt =>
							(unpin_unique <qlist <ref A>> l'_pinned)
					end
					end
  		| tt =>
  				l'
  		end
  end
  .

Define main :=
	let u = (mk_ref nat one) in
	let l = (qcons <ref nat> u (qnil <ref nat>)) in
	(qlist_erase_ref nat one l)
	.

Compile main to "qlist_test.c".
