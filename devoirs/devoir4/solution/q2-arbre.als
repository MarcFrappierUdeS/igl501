// arbre
sig S {
r : set S
}

fact {
all s : S | not s in s.^r // pas de cycle
one s : S | no r.s        // une seule racine
all s : S | lone r.s      // au plus un parent
all s : S | #(s.r) <= 2   // au plus deux enfants - arbre binaire
}

run test1 {} for exactly 5 S
