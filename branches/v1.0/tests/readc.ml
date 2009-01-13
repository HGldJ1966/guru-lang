open Array;;
open Char;;

exception Done of char

let rec do_read = fun a -> 
                  let c = (try input_char stdin 
                                 with End_of_file -> raise (Done a))
                  in
                    do_read c;;

try (do_read '\n')
with (Done c) -> print_char c;;

