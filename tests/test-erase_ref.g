Include trusted "../lib/erase_ref.g".
Include trusted "../lib/length_word.g".
Include trusted "../lib/stdio.g".

Define print_word_ln :=
	fun(#unique_point io:stdio_t)(w:word) : #unique_point stdio_t.
	let io = (print_string io (word_num_to_string w)) in
	(print_char io C10).

Define main :=
	let n = (S Z) in
	let n' = (S Z) in
	let l = (fill nat (inspect nat n) (inspect nat three)) in
	let stdio = (print_word_ln stdio (length_word nat (inspect <list nat> l))) in
	let l = (erase_ref nat n' l) in
	let stdio = (print_word_ln stdio (length_word nat (inspect <list nat> l))) in
	let l = (erase_ref nat n l) in
	let stdio = (print_word_ln stdio (length_word nat (inspect <list nat> l))) in
	do
		(consume_unowned nat n)
		(consume_unowned nat n')
		(consume_unique_point stdio_t stdio)
		l
	end.

%Interpret main.
Compile main to "test-erase_ref.c".
