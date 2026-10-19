MACHINE Ensemble
SETS
  E

CONSTANTS
  k

PROPERTIES
    k : NAT
  & k = 3

VARIABLES e

INVARIANT
  e <: E
& card(e) <= k

INITIALISATION
  e := {}

OPERATIONS

  Add(x) = 
    PRE
        x:E
      & x /: e
      & card(e) < k
    THEN
      e := e \/ {x}
    END
;
  Del(x) =
    PRE
        x:E
      & x : e
    THEN
      e := e - {x}
    END
;
  r <-- In(x) =
    PRE
      x : E
    THEN
      r := bool(x : e)
    END

END

