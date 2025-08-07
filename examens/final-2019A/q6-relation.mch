MACHINE q5_relation
SETS
 ELEM={a,b,c}
VARIABLES r
INVARIANT
  r ∈ ELEM ↔ ELEM
∧ id(ELEM) ∩ r = ∅

INITIALISATION r := ∅
OPERATIONS
   add(x,y) = PRE x ∈ ELEM ∧ y ∈ ELEM ∧ (x,y) ∉ r ∧ x ≠ y THEN r := r ∪ {(x,y)} END
;  del(x,y) = PRE x ∈ ELEM ∧ y ∈ ELEM ∧ (x,y) ∈ r THEN r := r - {(x,y)} END
;  res <-- transitive = res := bool((r;r) ⊆ r)
END


