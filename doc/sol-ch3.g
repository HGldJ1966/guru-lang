%- Problem 1 -%

Include "../guru-lang/lib/mult.g".

Classify join (mult Z three) zero.

Classify join (mult (S Z) three) three.

Classify join (mult one three) (mult three one).

%- Problem 2 -%

Classify foralli(x:nat). join (mult Z x) Z.

%- Problem 3 -%

Classify foralli(x y:nat). join (lt Z (plus (S x) y)) tt.

%- Problem 4 -%

Classify foralli(b:bool). join (and ff b) ff.

%- Problem 5 -%

Classify foralli(b:bool). 
           case b with
             ff => trans cong (and * *) b_eq
                   trans join (and ff ff) ff
                         symm b_eq
           | tt => trans cong (and * *) b_eq
                   trans join (and tt tt) tt
                         symm b_eq
           end.

%- Problem 6 -%

Classify foralli(x:nat). 
           case x with
             Z => trans cong (le Z *) x_eq
                        join (le Z Z) tt
           | S x' => trans cong (le Z *) x_eq
                           join (le Z (S x')) tt
           end.

%- Problem 7 -%

Inductive penta : type :=
  MacBride : penta
| MacLean : penta
| Schaeffer : penta
| Jessup : penta
| OldCapitol : penta.

Define clockwise :=
  fun (b:penta). 
    match b with
      MacBride => Schaeffer
    | MacLean => Jessup
    | Schaeffer => MacLean
    | Jessup => MacBride
    | OldCapitol => OldCapitol
  end.
  
Define counter :=
  fun (b:penta). 
    match b with
      MacBride => Jessup
    | MacLean => Schaeffer
    | Schaeffer => MacBride
    | Jessup => MacLean
    | OldCapitol => OldCapitol
  end.
  
Classify foralli(b:penta).
           case b with
             MacBride => trans cong (counter (clockwise *)) b_eq
                         trans join (counter (clockwise MacBride)) MacBride
                               symm b_eq
           | MacLean => trans cong (counter (clockwise *)) b_eq
                         trans join (counter (clockwise MacLean)) MacLean
                               symm b_eq
           | Schaeffer => trans cong (counter (clockwise *)) b_eq
                          trans join (counter (clockwise Schaeffer)) Schaeffer
                                symm b_eq
           | Jessup => trans cong (counter (clockwise *)) b_eq
                       trans join (counter (clockwise Jessup)) Jessup
                             symm b_eq
           | OldCapitol => trans cong (counter (clockwise *)) b_eq
                           trans join (counter (clockwise OldCapitol)) OldCapitol
                                 symm b_eq
           end.

%- Here is a much, much shorter way to write this, but we have to see
   default clauses of case-proofs and hypjoin in order to understand
   how it works. -%

Classify foralli(b:penta).
           case b with
             default penta => hypjoin (counter (clockwise b)) b by b_eq end
           end.