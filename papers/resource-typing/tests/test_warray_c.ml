type boxed_word_t = Boxed_word of int;;

let rec fill_array a i =
  if (i == 0) then
    a
  else
    (Array.set a i (Boxed_word i);
     fill_array a (i-1));;

let mysize = 1048576;;

let arr = fill_array (Array.make mysize (Boxed_word 0)) (mysize-1);;

let rec binsearch a l u x =
  let mid = (l+u)/2 in
  let (Boxed_word v) = Array.get a mid in
    if (x == v) then true
    else 
      if (x < v) then
	(if (mid >= u) then
	   false
	 else
	   binsearch a l mid x)
      else
	(* x > v *)
	(if (mid <= l) then
	   false
	 else
	   binsearch a mid u x);;

let rec search a i b =
  let r = binsearch a 0 (mysize - 1) i in
    if (i == 0) then (r && b)
    else (search a (i-1) (r && b));;

if (search arr (mysize - 1) true) then
  print_string "False\n"
else
  print_string "True\n";;
