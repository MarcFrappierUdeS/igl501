MACHINE Q1
VARIABLES S
INVARIANT
  S <: NAT
INITIALISATION
  S := {}
OPERATIONS
  ajout(x) = PRE x : NAT & x /: S THEN S := S \/ {x} END
;
  sup(x) = PRE x : NAT & x : S THEN S := S - {x} END
;
  r <-- maximum = IF S /= {} THEN r := max(S) ELSE r := 0 END
END

