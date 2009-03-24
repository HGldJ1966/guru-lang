%Set "print_parsed".
%Set "debug_primitives".
Set "debug_stages".

Include "nat.w".
Include "list.w".

Datatype nat := Z : unowned | S : Fun(x:unowned & nat).unowned.

Global alist := (cons nat (S Z) nil). 

Global test := 
  let n = Z in
  let l = (inspect alist) in
  let ret = @ (get (inspect n) l) in
    do (dec nat n)
       (consume_owned l)
       ret
    end.

