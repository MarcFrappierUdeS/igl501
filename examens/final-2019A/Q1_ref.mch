REFINEMENT Q1_ref
REFINES Q1
VARIABLES S1,S2
INVARIANT
  S1 ⊆ NAT
∧ S2 ⊆ NAT
∧ ∀x.(x ∈ S1 ⇒ x mod 2 = 0)
∧ ∀x.(x ∈ S2 ⇒ x mod 2 ≠ 0)
∧ S = S1∪S2
INITIALISATION
   S1 := ∅
|| S2 := ∅
OPERATIONS
  ajout(x) =
    PRE x ∈ NAT ∧ x ∉ S1 ∪ S2
    THEN IF x mod 2 = 0 THEN S1 := S1 ∪ {x}
         ELSE S2 := S2 ∪ {x} END
    END
;
  sup(x) =
    PRE x ∈ NAT ∧ x ∈ S1 ∪ S2
    THEN IF x mod 2 = 0 THEN S1 := S1 - {x}
         ELSE S2 := S2 - {x} END
    END
;
  r <-- maximum = IF S1∪S2 ≠ ∅ THEN r := max(S1∪S2) ELSE r := 0 END
END


