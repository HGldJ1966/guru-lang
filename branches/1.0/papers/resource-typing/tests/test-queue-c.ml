open Queue;;

let rec read_until_space() =
  try
    let c = (input_char stdin) in
      if (c = ' ') then
	(false,[])
      else
	let (eof,s) = (read_until_space()) in
	  (eof, c ::s)
  with End_of_file -> (true,[])
;;

let rec enqueue_all q =
  let (eof,s) = read_until_space() in
    add s q;
    if eof then
      q
    else
      enqueue_all q;;

let rec shift_all q1 q2 =
  if (is_empty q1) then q2
  else
  let s = (take q1) in
    add s q2; shift_all q1 q2;;

let rec print_charlist s =
  match s with
      [] -> ()
    | c::s -> output_char stdout c; print_charlist s;;

let rec dequeue_all q prev =
  if (is_empty q) then
    (print_charlist prev; print_newline())
  else
    dequeue_all q (pop q);;

(* (enqueue_all (create()));; *)

 (dequeue_all (enqueue_all (create())) []);; 


(* (dequeue_all (shift_all (enqueue_all (create())) (create())) []);;  *)

(*
let rec loop() = loop();;
loop();; 
*)
