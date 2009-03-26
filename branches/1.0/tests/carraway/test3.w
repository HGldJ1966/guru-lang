Set "use_malloc".

Include "stdin.w".
Include "bool.w".
Include "list.w".

Set "debug_stages".
%Set "debug_refs".

Function read_all(^x:unique).unowned :=
  let c = (curc x) in
  match (eof c) with
    ff => (ucons c (read_all (nextc x)))
  | tt => do (close x) nil end
  end.

Function print_list(^x:owned).void :=
  match x with
    unil => done
  | ucons a x' => do (printc a) (print_list x') end
  end.

Global main :=
  let s = (read_all stdin) in
  do (print_list (inspect s))
     (dec ulist s)
     (dec ulist (ucons tt (ucons ff unil)))
     (dec nat (S Z))
     tt
  end.
  