sig A {
p : set A,
q : set A,
r : set A
}
assert monotonicityRelComp {q in r => p.q in p.r }
check monotonicityRelComp for exactly 3 A

check monoCompSeq {q in r => p.q in p.r } for exactly 3 A
check distSeqUnion {p.(q + r) = p.q + p.r } for exactly 3 A
check distSeqInter {p.(q & r) = p.q & p.r } for exactly 2 A
run distSeqInter {p.(q & r) = p.q & p.r } for exactly 2 A
check distSeqInterDet {
	p in A -> one A => ( p.(q & r) = p.q & p.r )
} for exactly 3 A

