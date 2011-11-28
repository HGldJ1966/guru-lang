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

let rec eat_all_words() =
  let (eof,s) = read_until_space() in
    if eof then
      ()
    else
      eat_all_words();;

eat_all_words();;

(* (dequeue_all (enqueue_all (create())) []);;  *)

(*
let rec loop() = loop();;
loop();; 
*)
