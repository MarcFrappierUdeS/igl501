MACHINE file(k)
CONSTRAINTS k : NAT & k = 3
VARIABLES f
INVARIANT
  f : seq(0..k)
& size(f) <= k
INITIALISATION f := []
OPERATIONS

enfiler(x) =
  PRE x : 0..k & size(f) < k
  THEN f := f <- x
  END
;
defiler =
  PRE size(f) > 0
  THEN f := tail(f)
  END
;
res <-- tete =
  PRE size(f) > 0
  THEN res := first(f)
  END

END
