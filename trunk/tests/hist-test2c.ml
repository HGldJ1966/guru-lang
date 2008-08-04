open Array;;
open Char;;

type nat = Z | Succ of nat

exception Done of nat

let h = (make 128 Z);;

let rec do_hist = fun () -> 
                  let c = (code (try input_char stdin 
                                 with End_of_file -> raise (Done Z)))
                  in
                    (set h c (get h c));
                    do_hist ();;

try (do_hist ())
with (Done n) -> ();;

