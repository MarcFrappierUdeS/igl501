REFINEMENT Q2_ref
REFINES Q2
VARIABLES v,w
INVARIANT
  v : S --> S
& w : S --> S
INITIALISATION
   v := {(1,4),(2,3),(3,2),(4,1)}
|| w := {(1,1),(2,1),(3,1),(4,1)}
OPERATIONS
  P =
VAR i IN
i := 0;
WHILE (i < k) DO
  i := i+1;
  w(i) := v(k+1-i)
INVARIANT
  !x.(x : 1..i => w(x) = v(k+1-x))
& i : 0..k
VARIANT
  (k-i)
END
END
END