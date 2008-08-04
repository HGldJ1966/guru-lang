type nat = Z | Succ of nat

(* let c = input_char stdin;;

output_char stdout c;;
*)

exception Done of nat

let rec balanced = 
  fun n -> let c = try input_char stdin 
                   with End_of_file -> raise (Done n)
           in
             if c == '(' then balanced (Succ n) else
             if c == ')' then match n with Z -> raise (Done Z)
                                         | Succ n2 -> balanced n2
             else balanced n;;

(* match n with z -> true | _ -> false;;*)
try balanced Z 
with (Done n) ->
  match n with
    Z -> output_char stdout 'T'
  | _ -> output_char stdout 'F';;

output_char stdout '\n';;
