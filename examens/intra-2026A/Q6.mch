MACHINE Q6
VARIABLES x,y
INVARIANT x ∈ 1..2 ∧ y : 0..3 & y+x <= 3 
INITIALISATION x := 1 || y := 2
OPERATIONS
  Op1 = CHOICE x := 2 OR y := 2 END
; Op2 = PRE x > 1
    THEN ANY z WHERE z ∈ x..y THEN x := x+z || y := y+z END
    END
END


