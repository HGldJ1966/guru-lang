Include "nat.g".

Define subtract := 
  fun subtract(x y:nat):nat.
  match y with
    Z => x
  | S y' => 
    match x with
      Z => Z
    | S x' => (subtract x' y')
    end
  end.


