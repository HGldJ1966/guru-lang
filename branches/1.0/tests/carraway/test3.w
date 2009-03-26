Set "use_malloc".

Include "stdin.w".
Include "bool.w".
Include "list.w".

Set "debug_stages".
%Set "debug_refs".

Global main :=
  let s = (read_all stdin) in
  do (print_list (inspect s))
     (dec ulist s)
     (dec ulist (ucons tt (ucons ff unil)))
     (dec nat (S Z))
     tt
  end.
  