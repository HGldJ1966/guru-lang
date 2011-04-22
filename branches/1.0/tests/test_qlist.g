Include "../lib/qlist.g".

Define main :=
	let z1 = Z in
	let z2 = Z in
	let u = (mk_ref nat (inc nat z1)) in
	let l = (qcons <ref nat> u (qnil <ref nat>)) in
	let l' = (qlist_erase_ref nat z1 l) in	% try erase z2, instead
	let n = (qlength_word <ref nat> l') in
	do
	(log_string (word_num_to_string n))
	(log_string "\n")
	(consume_unowned nat z1)
	(consume_unowned nat z2)
	(consume_unique <qlist <ref nat>> l')
	word0
	end
	.

Compile main to "test_qlist.c".
