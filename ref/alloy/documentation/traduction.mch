MACHINE traduction

SETS A = {a1,a2}; B

CONSTANTS b,B1,f

PROPERTIES

  b ∈ B
∧ B1 ⊆ B
∧ f ∈ B1 → B
∧ ∃ x . (x ∈ B1 ∧ f(x) = b)

VARIABLES a3, A1,g

INVARIANT
  a3 ∈ A1
∧ A1 ⊆ A
∧ g ∈ A1 ⇸ A1
∧ ∃ y . (y ∈ A1 ∧ a3 ↦ y ∈ g)

INITIALISATION
   a3 := a1
|| A1 := {a1,a2}
|| g := {a1 ↦ a1}

OPERATIONS

add_g(x) = PRE x ∈ A1 THEN g(x) := x END

END


