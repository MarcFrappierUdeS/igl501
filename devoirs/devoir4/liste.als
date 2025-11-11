// r est une liste commençant par first
// r est la relation successeur

sig S {
r : set S              // relation sucesseur
}

one sig first extends S {} // singleton qui représente le premier élément de la liste

fact {
r in S lone -> lone S  // injection partielle : au plus un prédécesseur et un successeur
first.^r = S-first     // tous les noeuds sont accessibles de first
}

run test1 {} for exactly 5 S
/*
Vérifier que first est bien le premier
qu'il est unique, et qu'il existe un dernier.
*/
check prop1 {
 no r.first                // first est le premier
 no x : S-first | no r.x   // first est unique
 some last : S | no last.r // il existe un dernier
} for exactly 5 S
