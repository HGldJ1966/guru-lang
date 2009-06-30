Define list_setmbr: Forall(A:type)(a:A)(eqA:Fun(^ #owned x y: A).bool)(l' l'':<list A>)(u:{(eqA a a) = tt}).{(member a (append l' (cons a l'')) eqA) = tt } :=
  foralli(A:type)(a:A)(eqA:Fun(^ #owned x y: A).bool)(l'':<list A>)(u:{(eqA a a) = tt}).
  induction(l':<list A>) return { (member a (append l' (cons a l'')) eqA) = tt } with

       nil _ => show 
                cong (member a (append * (cons a l'')) eqA) l'_eq
                end

    | cons _ b k => truei
                    %l'_eq
                    %cong (member a (append * (cons a l'')) eqA) l'_eq
                    %join (append (cons b k) l') (append (append (cons b k) l') l')
                    %join (append l' (cons a l'')) (append (append l' (cons a nil)) l'')
                    %[l'_IH l']
                    
end.
