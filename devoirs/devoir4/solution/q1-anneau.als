// ne pas modifier la signature
sig S {
r : set S
}
// modifier seulement le fact
fact {
all s : S | S in s.^r
r in S one -> one S
}

run test1 {} for exactly 5 S, 5 Int
