MACHINE Q2
CONSTANTS S,k
PROPERTIES k = 4 ∧ S = 1..k & (1=1) <=> (1=1)
VARIABLES v,w
INVARIANT
  v ∈ S → S
∧ w ∈ S → S
INITIALISATION
   v := {(1,4),(2,3),(3,2),(4,1)}
|| w := {(1,1),(2,1),(3,1),(4,1)}
OPERATIONS
  P = ANY u WHERE u ∈ S → S ∧ ∀x.(x ∈ S ⇒ u(k+1-x) = v(x)) THEN w := u END
END



