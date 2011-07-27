Include "unowned.g".
Include trusted "bool.g".

Define primitive eqref : Fun(spec A:type)(! #unowned x y:A).bool <<END
inline unsigned geqref(void* x, void* y) {
	return (x == y)? gtt(): gff();
}
END.
