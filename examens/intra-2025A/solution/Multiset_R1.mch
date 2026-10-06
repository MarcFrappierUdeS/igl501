REFINEMENT Multiset_R1(n)
REFINES Multiset
VARIABLES g
INVARIANT
  g : E --> NAT
& dom(f) <| g = f
& dom(f) <<| g = (E-dom(f)) * {0}

INITIALISATION g := E*{0}

OPERATIONS

  Add(e) = PRE e : E & SIGMA x.(x : dom(g) | g(x)) < n THEN g(e) := g(e) + 1 END
; Del(e) = PRE e : E THEN  g(e) := max({g(e) - 1,0}) END
; DelAll(e) = PRE e : E THEN g(e) := 0 END
; r <-- In(e) = r := bool(g(e) > 0)
; r <-- ToSet = r := dom(g|>>{0})

END









