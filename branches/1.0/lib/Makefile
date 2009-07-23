queue:
	time ../bin/guru queue.g

rheaplet:
	time ../bin/guru rheaplet.g

heaplet:
	time ../bin/guru heaplet.g

charray:
	time ../bin/guru charray.g

warray:
	time ../bin/guru warray.g

wlist:
	time ../bin/guru wlist.g

trie:
	time ../bin/guru trie.g

qcharray:
	time ../bin/guru qcharray.g


ulist:
	time ../bin/guru ulist.g

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

qpair:
	time ../bin/guru qpair.g

nat:
	time ../bin/guru nat.g

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

word:
	time ../bin/guru word.g

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



