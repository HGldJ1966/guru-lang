
Include "../guru-lang/lib/bool.g" 
Include "../guru-lang/lib/nat.g"
Include "../guru-lang/lib/minus.g"

Define minus_lt_Z : Forall
	(a b:nat)(u:{ (lt b a) = tt }).{ (lt Z (minus a b)) = tt }
	:=
  induction(a: nat) return
    Forall(b: nat)(u:{ (lt b a) = tt }).{ (lt Z (minus a b)) = tt }
  with
    | Z =>
      foralli(b:nat)(u:{ (lt b a) = tt }).
      contra
        trans symm u
        trans hypjoin (lt b a) ff by [lt_Z b] a_eq end
              clash ff tt
        
        { (lt Z (minus a b)) = tt }
    | S a' =>
      foralli(b:nat)(u:{ (lt b a) = tt }).
      case b with
        | Z =>
          hypjoin (lt Z (minus a b)) tt by b_eq a_eq end
        | S b' =>
          lemma
            : { (lt b' a') = tt }
              hypjoin (lt b' a') tt by a_eq b_eq [S_lt_S b' a'] u end
          in
          hypjoin (lt Z (minus a b)) tt by
            : { a = (S a') } 
              a_eq

            : { b = (S b') } 
              b_eq
               
            : { (lt Z (minus a' b')) = tt } 
              [a_IH a' b' ##]
              
            : { (minus a' b') = (S (minus a' (S b'))) }
              [minusS2 a' b' ##]
          end
      end %b
  end. %a
  
Classify minus_lt_Z.
