Include trusted "../lib/plus.g".
Include trusted "../lib/bool.g".
Include trusted "../lib/mult.g".
Include trusted "../lib/pow.g".
Include trusted "../lib/list.g".


Define list_setmbr: Forall(A:type)(a:A)(eqA:Fun(x y: A).bool)(l' l'':<list A>)(u:{(eqA a a) = tt}).{(member a (append l' (cons a l'')) eqA) = tt } :=  truei.
  foralli(A:type)(a:A)(eqA:Fun(x y: A).bool)(l'':<list A>)(u:{(eqA a a) = tt}).
  induction(l':<list A>) return { (member a (append l' (cons a l'')) eqA) = tt } with

       nil _ => trans cong (member a (append * (cons a l'')) eqA) l'_eq
		      hypjoin (member a (append nil (cons a l'')) eqA) tt by u end


    | cons _ b k => truei
                    %l'_eq
                    %cong (member a (append * (cons a l'')) eqA) l'_eq
                    %join (append (cons b k) l') (append (append (cons b k) l') l')
                    %join (append l' (cons a l'')) (append (append l' (cons a nil)) l'')
                    %[l'_IH l']
                    
end.
