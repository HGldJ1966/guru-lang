%Set "use_malloc".

Include "../guru-lang/tests/carraway/stdin.w".

Function append(l1:unowned)(l2:unowned).unowned :=
  match l1 with
    unil => l2
  | ucons a l1' => (ucons a (append l1' l2))
  end.

Function length(l1:unowned).unowned :=
  match l1 with
    unil => Z
  | ucons a l1' => (S (length l1'))
  end.

Global main :=
  let s = (read_all stdin) in
  let t = (length (append (inc s) (inc s))) in
  do (dec ulist s)
     (dec ulist t)
     tt
  end.
