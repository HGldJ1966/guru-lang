Include "plus.g".

Define min : Fun(x y:nat).nat :=
  fun(x y:nat).
    match (le x y) with
      ff => y
    | tt => x
    end.

Define max : Fun(x y:nat).nat :=
  fun(x y:nat).
    match (le x y) with
      ff => x
    | tt => y
    end.

Define min_total : Forall(x y:nat). Exists(z:nat). { (min x y) = z} :=
  foralli(x y:nat).
    case (le x y) by u _ with
      ff => existsi y { (min x y) = * }
              hypjoin (min x y) y by u end
    | tt => existsi x { (min x y) = * }
              hypjoin (min x y) x by u end
    end.
    
Define max_total : Forall(x y:nat). Exists(z:nat). { (max x y) = z} :=
  foralli(x y:nat).
    case (le x y) by u _ with
      ff => existsi x { (max x y) = * }
              hypjoin (max x y) x by u end
    | tt => existsi y { (max x y) = * }
              hypjoin (max x y) y by u end
    end.
    