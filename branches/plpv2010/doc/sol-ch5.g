Include "../guru-lang/lib/pow.g".

Define ZltS : Forall(x:nat)(u:{(lt Z x) = tt}). Exists(x':nat). { x = (S x') } :=
   foralli(x:nat)(u:{(lt Z x) = tt}).
     case x with
       Z => 
       contra
         trans symm u
         trans cong (lt Z *) x_eq
         trans join (lt Z Z) ff
               clash ff tt
       Exists(x':nat). { x = (S x') }
    | S x' => existsi x' { x = (S *) } x_eq
    end.

Define multSZ : Forall(x y:nat)(u:{(mult y (S x)) = Z}). { y = Z } :=
  foralli(x:nat).
  induction(y:nat) return Forall(u:{(mult y (S x)) = Z}). { y = Z } 
  with
    Z => foralli(u:{(mult y (S x)) = Z}). y_eq
  | S y' => 
    foralli(u:{(mult y (S x)) = Z}). 
    contra
      trans symm u
      trans cong (mult * (S x)) y_eq
      trans join (mult (S y') (S x)) (S (plus x (mult y' (S x))))
            clash (S (plus x (mult y' (S x)))) Z
    { y = Z }
  end.
       
Define pow_not_zero_le : Forall(b e : nat)(u:{ b != Z }). { (le (S Z) (pow b e)) = tt } :=
  foralli(b e : nat)(u:{ b != Z }).
    case (pow b e) by v ign with
      Z => contra 
             trans symm v
                   [pow_not_zero b e u] 
           { (le (S Z) (pow b e)) = tt } 
    | S x => trans cong (le (S Z) *) v
             trans [S_le_S Z x]
                   [leZ x]              
    end.

