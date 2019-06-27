declare nonterminal NT
declare inherited attribute d :: int
attach attribute d on NT
declare synthesized attribute u :: int
attach attribute u on NT

declare production A
top::NT ::= {
	top.u = 3;
}

declare nonterminal Main_nt
declare synthesized attribute exitcode :: int
attach attribute exitcode on Main_nt

declare production Main
top::Main_nt ::= {
	top.exitcode = decorate A() {d = 1/0}.u;
}