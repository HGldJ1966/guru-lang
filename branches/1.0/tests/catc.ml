open Array;;
open Char;;

type nat = Z | Succ of nat

exception Done of nat

let rec cat = fun () -> 
                  let c = (try input_char stdin 
                                 with End_of_file -> raise (Done Z))
                  in
                    print_char c;
                    cat ();;

try (cat ())
with (Done n) -> ();;

