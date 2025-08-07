MACHINE Q5_invariant
VARIABLES x
INVARIANT x : 0..2
INITIALISATION x := 0
OPERATIONS
  Op1(y) = PRE y : 3..4 THEN x := x-y END
; Op2(y) = PRE y : 0..x THEN x := x-y END
; Op3    = ANY y WHERE y : 0..x THEN x := x-y END
; Op4(y) = PRE y : -2..2 THEN
             SELECT y < 0 THEN x := x + y
             WHEN   y > 0 THEN x := x - y
             END
           END
; Op5    = CHOICE x := -1 OR x := 1 END
END

