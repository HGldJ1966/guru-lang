open Array;;
open Char;;

type nat = Z | Succ of nat

let rec print_nat n = 
  match n with 
    Z -> output_char stdout 'Z'
  | Succ n' -> output_char stdout 'S'; print_nat n'

let rec lt n m = 
  match n,m with
    Z, Succ _ -> true
  | _, Z -> false
  | Succ n', Succ m' -> lt n' m'

let rec alength l =
  match l with
    [] -> Z
  | a::l' -> Succ(alength l')

let rec eqlist l1 l2 =
   match l1,l2 with
     [],[] -> true
   | a::l1', b::l2' -> a=b && (eqlist l1' l2')
   | _,_ -> false

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
   | Texact(s',a) -> if eqlist s s' then Some(a) else None
   | Tnext(o,v) -> 
       match s with
         [] -> o
       | c::s' -> trie_lookup (get v (code c)) s'

let rec read_string_h reading =
    let c = (try Some(input_char stdin) with End_of_file -> None) in
    match c with
      None -> []
    | Some(c) ->
      if (c = '\n' || c = ' ' || c = '\t' || c = '\r') then
        if reading then
          []
        else
          read_string_h reading
      else
        c :: (read_string_h true)

let read_string () = read_string_h false

let rec do_hist = 
   fun h -> 
     let s = read_string () in
     match s with 
       [] -> h
     | _::_ -> do_hist h
;;

let h = ();;

do_hist h

(* 

let rec spin () = spin ();;

spin ()

*)