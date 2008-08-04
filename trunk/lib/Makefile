trie:
	java -cp .. guru.Main trie.g

word:
	java -cp .. guru.Main word.g

vec:
	java -cp .. guru.Main vec.g

msort:
	java -cp .. guru.Main msort.g

trie_test: trie_test.g trie.g
	java -cp .. guru.Main trie_test.g
	$(MAKE) TT
	./trie_test

TT:
	gcc -O0 -ggdb -o trie_test trie_test.c



