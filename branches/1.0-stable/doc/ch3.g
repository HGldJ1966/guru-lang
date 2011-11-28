%- This runs through the examples in Chapter 2 -%

Include "../lib/plus.g".

Define plus224 := join (plus two two) four.

Classify plus224.

Define Zplus := foralli(m:nat). join (plus Z m) m.

Classify Zplus.

Classify [Zplus three].

Classify { (plus Z three) = three }.

Define plus413 := join four (plus one three).

Classify trans plus224 plus413.

Classify symm trans plus224 plus413.

Classify refl (fun loop(b:bool):bool. (loop b) tt).

Classify cong (S *) plus224.

Classify cong (plus * *) plus224.

Define not_not_a : Forall(b:bool). { (not (not b)) = b } :=
  foralli(b:bool).
    case b with
      ff => trans cong (not (not *)) b_eq
            trans join (not (not ff)) ff
                  symm b_eq
    | tt => trans cong (not (not *)) b_eq
            trans join (not (not tt)) tt
                  symm b_eq           
    end.
