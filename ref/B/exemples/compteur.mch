MACHINE compteur
CONSTANTS c_max
PROPERTIES
  c_max ∈ NAT1
VARIABLES c
INVARIANT
 c ∈ 0..c_max
INITIALISATION c := 0
OPERATIONS
  inc = PRE c < c_max THEN c := c+1 END
;
  dec = PRE c > 0 THEN c := c-1 END
END


