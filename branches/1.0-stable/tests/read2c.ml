open Array;;
open Char;;

exception Done of char

let rec do_read = fun b -> 
                  match b with
                    true -> true
                  | false ->
                    let b' = (try (input_char stdin); false
                             with End_of_file -> true)
                    in
                      do_read b';;

(do_read false);;

