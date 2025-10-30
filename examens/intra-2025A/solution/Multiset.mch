MACHINE Multiset(n)

CONSTRAINTS
  n : NAT
& n = 5

SETS E = {e1,e2,e3}

VARIABLES f
INVARIANT
  f : E +-> NAT1
& SIGMA x.(x : dom(f) | f(x)) < n

INITIALISATION f := {}

OPERATIONS

  Add(e) = PRE e : E & SIGMA x.(x : dom(f) | f(x)) < n THEN
    IF e : dom(f) THEN f(e) := f(e) + 1 ELSE f(e) := 1 END END
; Del(e) = PRE e : E THEN IF e : dom(f) & f(e) > 1 THEN f(e) := f(e) - 1 ELSE f := {e} <<| f END END
; DelAll(e) = PRE e : E THEN f := {e} <<| f END
; r <-- In(e) = r := bool(e : dom(f))
; r <-- ToSet = r := dom(f)

END









