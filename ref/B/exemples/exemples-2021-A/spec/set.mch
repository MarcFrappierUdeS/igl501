MACHINE set
SETS
 E={e1,e2,null}

VARIABLES S,nullPermis

INVARIANT
  S <: E
& nullPermis = FALSE => null /: S 
& nullPermis : BOOL

INITIALISATION S := {} || nullPermis := FALSE

OPERATIONS

setNullPermis(b) =
  PRE
      b : BOOL
    & (b = FALSE => null /: S)
  THEN
    nullPermis := b
  END
;
b <--  Add(e) =
  PRE
      e : E
    & (e = null => nullPermis = TRUE)
  THEN
        S := S \/ {e}
    ||  b := bool(e /: S)
  END
;
clear = S := {}
;
b <-- Contains(e) =
  PRE
      e : E
    & (e = null => nullPermis = TRUE)
  THEN
    b := bool(e : S)
  END		
;
b <-- isEmpty =
  b := bool(S={})  
;
b <-- remove(e)=
  PRE
      e : E
    & (e = null => nullPermis = TRUE)
  THEN
        S := S - {e}
    ||  b := bool(e:S)
  END
;
n <-- size_ = n := card(S)
END

