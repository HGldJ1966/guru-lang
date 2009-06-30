Include trusted "../lib/bool.g".
Include trusted "../lib/list.g".


Define trusted list_setmbr: Forall(A:type)(a:A)(eqA:Fun(x y: A).bool)(l' l'':<list A>)(u:{(eqA a a) = tt}).{(member a (append l' (cons a l'')) eqA) = tt } :=  truei.
