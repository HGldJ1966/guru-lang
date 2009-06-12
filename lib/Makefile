stdio:
	time ../bin/guru stdio.g

plus:
	time ../bin/guru plus.g

string:
	time ../bin/guru string.g

char:
	time ../bin/guru char.g

pair:
	time ../bin/guru pair.g

list:
	time ../bin/guru list.g

bst-spec:
	time ../bin/guru bst-spec.g

bst:
	time ../bin/guru bst.g

pow:
	../bin/guru pow.g

minmax:
	../bin/guru minmax.g

minmax-le:
	../bin/guru minmax-le.g

trie:
	time java -cp .. guru.Main trie.g

word:
	java -cp .. guru.Main word.g

vec:
	java -cp .. guru.Main vec.g

bv:
	time java -cp .. guru.Main bv.g

list2:
	time java -cp .. guru.Main list2.g

msort:
	java -cp .. guru.Main msort.g

trie_test: trie_test.g trie.g
	java -cp .. guru.Main trie_test.g
	$(MAKE) TT
	./trie_test

TT:
	gcc -O0 -ggdb -o trie_test trie_test.c



