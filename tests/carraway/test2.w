%Set "print_parsed".
%Set "debug_primitives".
%Set "debug_stages".

Set "use_malloc".

Include "nat.w".
Include "list.w".

Global alist := (cons nat (S Z) nil). 

Global test := 
  let n = Z in
  let l = (inspect alist) in
  let ret = @ (get (inspect n) l) in
    do (dec nat n)
       (consume_owned list l)
       ret
    end.

