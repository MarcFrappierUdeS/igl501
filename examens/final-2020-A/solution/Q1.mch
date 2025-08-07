MACHINE Q1
CONSTANTS T,k
PROPERTIES k = 2 & T = 1..k
VARIABLES v
INVARIANT
  v : (T*T) --> BOOL
INITIALISATION
  v := (T*T)*{FALSE}
OPERATIONS
  set(x,y,b) =

    PRE
        x : T
      & y : T
      & b : BOOL
    THEN
      v(x,y) := b
    END
;
  flip(x,y) =

    PRE x : T & y : T
    THEN
      IF
        v(x,y) = TRUE
      THEN
        v(x,y) := FALSE
      ELSE
        v(x,y) := TRUE
      END
    END
;
  r <-- get(x,y) =

    PRE
        x : T
      & y : T
    THEN
      r := v(x,y)
    END
END

