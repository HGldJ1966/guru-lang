Include "trie.g".
Include "stdio.g".

Define test_string1 := "ga".

Define test := 
  (trie_interp nat
  (trie_insert nat inc test_string1 (S (S Z)) 
  (trie_insert nat "ha" (S Z) 
  (trie_insert nat "hi" Z (trie_none nat))))).

Define main :=
  fun(unique stdin:stdin_t).
  dec stdin
  let ign = 
    (foldr <pair string nat> Unit Unit unit
      fun(cookie:Unit)(owned p:<pair string nat>)(u:Unit).
       match p with
         mkpair A B a b =>
         abbrev s = cast a by symm inj <pair * **> p_Eq in
         abbrev n = cast b by symm inj <pair ** *> p_Eq in
         let ign = (print_string s) in
         let ign = (print_char Csp) in
         let ign = (print_nat n) in
         let ign = (print_char Cco) in
           (print_char Csp)
       end
      unit test) in Z.

%Set "Debug_compiler".
%Set "compiler_print_initial_context".
%Set "debug_compiler_free_vars".
%Set "debug_eta_expand".
%Set "debug_classify_term_apps".
%Set "debug_classify_casts".
%Set "debug_classify_lets".
Set "print_ownership_annos".

Compile main to "trie_test.c".