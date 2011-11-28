type boxed_word_t = Boxed_word of int;;

type mycomp = MGT | MEQ | MLT;;

let mylt a b = (a < b);;
let myeq a b = (a == b);;

let comparator lt eq a b = 
  match (lt a b) with
      false -> 
	(match (eq a b) with
	     false -> MGT
	   | true -> MEQ)
    | true -> MLT;;

let rec fill_array a i =
  if (i == 0) then
    a
  else
    (Array.set a i (Boxed_word i);
     fill_array a (i-1));;

let mysize = 1048576;;

let arr = fill_array (Array.make mysize (Boxed_word 0)) (mysize-1);;

let rec binsearch f l arr v =
  let mid = f + ((l-f)/2) in
  let (Boxed_word u) = Array.get arr mid in
    match (comparator mylt myeq u v) with
	MLT -> (if (mid+1 <= l) then
		  binsearch (mid+1) l arr v
		else
		  false)
      | MGT -> (if (f <= (mid - 1)) then
		  binsearch f (mid - 1) arr v
		else
		  false)
      | MEQ -> true;;

let rec search a i b =
  let r = binsearch 0 (mysize - 1) a i in
    if (i == 0) then (r && b)
    else (search a (i-1) (r && b));;

if (search arr (mysize - 1) true) then
  print_string "True\n"
else
  print_string "False\n";;
