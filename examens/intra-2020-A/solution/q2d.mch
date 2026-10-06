MACHINE q2d
VARIABLES y

INVARIANT
  y : -2..2

INITIALISATION y := 0

OPERATIONS

D(x) =
  PRE x : -1..1
  THEN
    SELECT
      x <= 0 THEN y := -x
    WHEN
      x >= 0 THEN y := x
    END
  END

END




