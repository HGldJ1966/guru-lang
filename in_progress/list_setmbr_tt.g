Define trusted list_setmbr: Forall(A:type)(a:A)(eqA:Fun(^ #owned x y: A).bool)(l' l'':<list A>)(u:{(eqA a a) = tt}).{(member a (append l' (cons a l'')) eqA) = tt } :=
  truei.
  
