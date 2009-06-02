Include "../lib/plus.g".

Define existsle : Forall(x:nat).Exists(y:nat). {(le x y) = tt } :=
  foralli(x:nat). existsi x { (le x *) = tt } [x_le_x x].

Define ltcomm : Forall(x:nat).Exists(y:nat). { (le x y) = (le y y) } :=
  foralli(x:nat).
   existsi x { (le x *) = (le * *) } 
      refl (le x x).
     
Define plusZ' :=
  foralli(x:nat)(u : { x = Z }). 
    trans cong (plus * *) u
          join (plus Z Z) Z.


Classify [plusZ' Z refl Z].

Define existslt : Forall(x:nat). Exists(y:nat). {(lt x y) = tt } :=
 foralli(x:nat).
 existse [existsle x]
   foralli(y:nat)(u:{(le x y) = tt}).
     existsi (S y) { (lt x *) = tt }
       [lelt_trans x y (S y) u [lt_S y]].

Define Zle : Forall(x:nat)(u:{(le x Z) = tt}). { x = Z} :=
  foralli(x:nat)(u:{(le x Z) = tt}).
  case x with
    Z => x_eq
  | S x' => 
    contra 
    show
      trans symm u
      trans cong (le * Z) x_eq
      trans join (le (S x') Z) ff
            clash ff tt
    end
    { x = Z }
  end.
