open Array;;
open Char;;

type nat = Z | Succ of nat

let rec print_nat n = 
  match n with 
    Z -> output_char stdout 'Z'
  | Succ n' -> output_char stdout 'S'; print_nat n'

type 'a trie = Tnone 
             | Texact of char list * 'a
             | Tnext of 'a option * 'a trie array

let mk_trievec a = (make 128 a);;

let rec trie_insert t s a = 
  match t with 
    Tnone -> Texact(s,a)
  | Texact(s',a') -> 
       (trie_insert (trie_insert (Tnext(None,(mk_trievec Tnone))) s' a') s a)
  | Tnext(o,v) ->
       match s with
         [] -> Tnext(Some(a),v)
       | c::s' -> 
           let cc = (code c) in
           set v cc (trie_insert (get v cc) s' a);
           Tnext(o,v)

let rec trie_lookup t s = 
   match t with
     Tnone -> None
   | Texact(s',a) -> if s = s' then Some(a) else None
   | Tnext(o,v) -> 
       match s with
         [] -> o
       | c::s' -> trie_lookup (get v (code c)) s'

let rec read_string_h reading =
  try 
    let c = (input_char stdin) in
    if (c = '\n' || c = ' ' || c = '\t' || c = '\r') then
       if reading then
         []
       else
         read_string_h reading
    else
       c :: (read_string_h true)
  with End_of_file -> []

let read_string () = read_string_h false

let rec do_hist = 
   fun h -> 
     let s = read_string () in
     match s with 
       [] -> h
     | c::s' -> 
         let n = match (trie_lookup h s) with
                   None -> Z
                 | Some(n) -> n in
         do_hist (trie_insert h s (Succ n));;

let h = do_hist Tnone;;

let n = match (trie_lookup h ('c'::'o'::'w'::[])) with
          None -> Z
        | Some(n) -> n in
  print_nat n;;
(* 

let rec spin () = spin ();;

spin ()

*)